import V185TrunkScan23Chunk1045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6192543 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6192543 : Nat := 118140960795 + 6192543 * 2 ^ 59
def prefixEnd_6192543 : Nat := 4983230072969 + 3 ^ 40 * 6192543 * 2
def baseEnd_6192543 : Nat := 3179751032635270380733519

theorem tailTrace_6192543 : CollatzResearch.WordTrace tailWord_6192543 prefixEnd_6192543 3179751032635270380733519 := by
  unfold tailWord_6192543
  simp only [CollatzResearch.WordTrace]
  refine ⟨225860598404481787989502283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150573732269654525326334855 225860598404481787989502283)
  ·
    refine ⟨338790897606722681984253425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225860598404481787989502283 338790897606722681984253425)
    ·
      refine ⟨254093173205042011488190069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338790897606722681984253425 254093173205042011488190069)
      ·
        refine ⟨23821234987972688577017819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254093173205042011488190069 23821234987972688577017819)
        ·
          refine ⟨35731852481959032865526729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23821234987972688577017819 35731852481959032865526729)
          ·
            refine ⟨26798889361469274649145047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35731852481959032865526729 26798889361469274649145047)
            ·
              refine ⟨40198334042203911973717571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26798889361469274649145047 40198334042203911973717571)
              ·
                refine ⟨60297501063305867960576357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40198334042203911973717571 60297501063305867960576357)
                ·
                  refine ⟨11305781449369850242608067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60297501063305867960576357 11305781449369850242608067)
                  ·
                    refine ⟨16958672174054775363912101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11305781449369850242608067 16958672174054775363912101)
                    ·
                      refine ⟨3179751032635270380733519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16958672174054775363912101 3179751032635270380733519)
                      ·
                        rfl

theorem cell23_6192543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6192543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192543 prefixEnd_6192543 := by exact prefixLift 6192543
  have htrace : WordTrace (prefixWord ++ tailWord_6192543) baseStart_6192543 baseEnd_6192543 := by
    simpa [prefixWord, tailWord_6192543, baseEnd_6192543] using wordTrace_append hprefix tailTrace_6192543
  have hstable : (prefixWord ++ tailWord_6192543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192543).length < 2 ^ (prefixWord ++ tailWord_6192543).sum := by decide
  have hdescent : baseEnd_6192543 < baseStart_6192543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192556 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_6192556 : Nat := 118140960795 + 6192556 * 2 ^ 59
def prefixEnd_6192556 : Nat := 4983230072969 + 3 ^ 40 * 6192556 * 2
def baseEnd_6192556 : Nat := 3179757707883778829870959

theorem tailTrace_6192556 : CollatzResearch.WordTrace tailWord_6192556 prefixEnd_6192556 3179757707883778829870959 := by
  unfold tailWord_6192556
  simp only [CollatzResearch.WordTrace]
  refine ⟨112930536276717345604862761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150574048368956460806483681 112930536276717345604862761)
  ·
    refine ⟨84697902207538009203647071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112930536276717345604862761 84697902207538009203647071)
    ·
      refine ⟨127046853311307013805470607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84697902207538009203647071 127046853311307013805470607)
      ·
        refine ⟨190570279966960520708205911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127046853311307013805470607 190570279966960520708205911)
        ·
          refine ⟨285855419950440781062308867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190570279966960520708205911 285855419950440781062308867)
          ·
            refine ⟨428783129925661171593463301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285855419950440781062308867 428783129925661171593463301)
            ·
              refine ⟨80396836861061469673774369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 428783129925661171593463301 80396836861061469673774369)
              ·
                refine ⟨60297627645796102255330777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80396836861061469673774369 60297627645796102255330777)
                ·
                  refine ⟨45223220734347076691498083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60297627645796102255330777 45223220734347076691498083)
                  ·
                    refine ⟨67834831101520615037247125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45223220734347076691498083 67834831101520615037247125)
                    ·
                      refine ⟨3179757707883778829870959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67834831101520615037247125 3179757707883778829870959)
                      ·
                        rfl

theorem cell23_6192556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_6192556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192556 prefixEnd_6192556 := by exact prefixLift 6192556
  have htrace : WordTrace (prefixWord ++ tailWord_6192556) baseStart_6192556 baseEnd_6192556 := by
    simpa [prefixWord, tailWord_6192556, baseEnd_6192556] using wordTrace_append hprefix tailTrace_6192556
  have hstable : (prefixWord ++ tailWord_6192556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192556).length < 2 ^ (prefixWord ++ tailWord_6192556).sum := by decide
  have hdescent : baseEnd_6192556 < baseStart_6192556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192630 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6192630 : Nat := 118140960795 + 6192630 * 2 ^ 59
def prefixEnd_6192630 : Nat := 4983230072969 + 3 ^ 40 * 6192630 * 2
def baseEnd_6192630 : Nat := 1059931901817403846781873

theorem tailTrace_6192630 : CollatzResearch.WordTrace tailWord_6192630 prefixEnd_6192630 1059931901817403846781873 := by
  unfold tailWord_6192630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116485722197912615494959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150575847703444401231946229 14116485722197912615494959)
  ·
    refine ⟨21174728583296868923242439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116485722197912615494959 21174728583296868923242439)
    ·
      refine ⟨31762092874945303384863659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21174728583296868923242439 31762092874945303384863659)
      ·
        refine ⟨47643139312417955077295489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31762092874945303384863659 47643139312417955077295489)
        ·
          refine ⟨35732354484313466307971617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47643139312417955077295489 35732354484313466307971617)
          ·
            refine ⟨26799265863235099730978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35732354484313466307971617 26799265863235099730978713)
            ·
              refine ⟨20099449397426324798234035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26799265863235099730978713 20099449397426324798234035)
              ·
                refine ⟨30149174096139487197351053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20099449397426324798234035 30149174096139487197351053)
                ·
                  refine ⟨11305940286052307699006645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30149174096139487197351053 11305940286052307699006645)
                  ·
                    refine ⟨1059931901817403846781873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11305940286052307699006645 1059931901817403846781873)
                    ·
                      rfl

theorem cell23_6192630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6192630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192630 prefixEnd_6192630 := by exact prefixLift 6192630
  have htrace : WordTrace (prefixWord ++ tailWord_6192630) baseStart_6192630 baseEnd_6192630 := by
    simpa [prefixWord, tailWord_6192630, baseEnd_6192630] using wordTrace_append hprefix tailTrace_6192630
  have hstable : (prefixWord ++ tailWord_6192630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192630).length < 2 ^ (prefixWord ++ tailWord_6192630).sum := by decide
  have hdescent : baseEnd_6192630 < baseStart_6192630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192637 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_6192637 : Nat := 118140960795 + 6192637 * 2 ^ 59
def prefixEnd_6192637 : Nat := 4983230072969 + 3 ^ 40 * 6192637 * 2
def baseEnd_6192637 : Nat := 3179799299816793012958087

theorem tailTrace_6192637 : CollatzResearch.WordTrace tailWord_6192637 prefixEnd_6192637 3179799299816793012958087 := by
  unfold tailWord_6192637
  simp only [CollatzResearch.WordTrace]
  refine ⟨225864026866141242043424165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150576017910760828028949443 225864026866141242043424165)
  ·
    refine ⟨42349505037401482883142031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225864026866141242043424165 42349505037401482883142031)
    ·
      refine ⟨63524257556102224324713047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42349505037401482883142031 63524257556102224324713047)
      ·
        refine ⟨95286386334153336487069571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63524257556102224324713047 95286386334153336487069571)
        ·
          refine ⟨142929579501230004730604357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95286386334153336487069571 142929579501230004730604357)
          ·
            refine ⟨26799296156480625886988317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142929579501230004730604357 26799296156480625886988317)
            ·
              refine ⟨10049736058680234707620619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26799296156480625886988317 10049736058680234707620619)
              ·
                refine ⟨15074604088020352061430929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10049736058680234707620619 15074604088020352061430929)
                ·
                  refine ⟨11305953066015264046073197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15074604088020352061430929 11305953066015264046073197)
                  ·
                    refine ⟨4239732399755724017277449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11305953066015264046073197 4239732399755724017277449)
                    ·
                      refine ⟨3179799299816793012958087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239732399755724017277449 3179799299816793012958087)
                      ·
                        rfl

theorem cell23_6192637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_6192637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192637 prefixEnd_6192637 := by exact prefixLift 6192637
  have htrace : WordTrace (prefixWord ++ tailWord_6192637) baseStart_6192637 baseEnd_6192637 := by
    simpa [prefixWord, tailWord_6192637, baseEnd_6192637] using wordTrace_append hprefix tailTrace_6192637
  have hstable : (prefixWord ++ tailWord_6192637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192637).length < 2 ^ (prefixWord ++ tailWord_6192637).sum := by decide
  have hdescent : baseEnd_6192637 < baseStart_6192637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192647 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 1, 5]
def baseStart_6192647 : Nat := 118140960795 + 6192647 * 2 ^ 59
def prefixEnd_6192647 : Nat := 4983230072969 + 3 ^ 40 * 6192647 * 2
def baseEnd_6192647 : Nat := 1059934811541112657944347

theorem tailTrace_6192647 : CollatzResearch.WordTrace tailWord_6192647 prefixEnd_6192647 1059934811541112657944347 := by
  unfold tailWord_6192647
  simp only [CollatzResearch.WordTrace]
  refine ⟨225864391596105013751288195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150576261064070009167525463 225864391596105013751288195)
  ·
    refine ⟨338796587394157520626932293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225864391596105013751288195 338796587394157520626932293)
    ·
      refine ⟨63524360136404535117549805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338796587394157520626932293 63524360136404535117549805)
      ·
        refine ⟨23821635051151700669081177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63524360136404535117549805 23821635051151700669081177)
        ·
          refine ⟨17866226288363775501810883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23821635051151700669081177 17866226288363775501810883)
          ·
            refine ⟨26799339432545663252716325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17866226288363775501810883 26799339432545663252716325)
            ·
              refine ⟨5024876143602311859884311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26799339432545663252716325 5024876143602311859884311)
              ·
                refine ⟨7537314215403467789826467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024876143602311859884311 7537314215403467789826467)
                ·
                  refine ⟨11305971323105201684739701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537314215403467789826467 11305971323105201684739701)
                  ·
                    refine ⟨1059934811541112657944347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11305971323105201684739701 1059934811541112657944347)
                    ·
                      rfl

theorem cell23_6192647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_6192647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192647 prefixEnd_6192647 := by exact prefixLift 6192647
  have htrace : WordTrace (prefixWord ++ tailWord_6192647) baseStart_6192647 baseEnd_6192647 := by
    simpa [prefixWord, tailWord_6192647, baseEnd_6192647] using wordTrace_append hprefix tailTrace_6192647
  have hstable : (prefixWord ++ tailWord_6192647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192647).length < 2 ^ (prefixWord ++ tailWord_6192647).sum := by decide
  have hdescent : baseEnd_6192647 < baseStart_6192647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192744 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6192744 : Nat := 118140960795 + 6192744 * 2 ^ 59
def prefixEnd_6192744 : Nat := 4983230072969 + 3 ^ 40 * 6192744 * 2
def baseEnd_6192744 : Nat := 3179854242246824094320095

theorem tailTrace_6192744 : CollatzResearch.WordTrace tailWord_6192744 prefixEnd_6192744 3179854242246824094320095 := by
  unfold tailWord_6192744
  simp only [CollatzResearch.WordTrace]
  refine ⟨112933964738376799658784643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150578619651169066211712857 112933964738376799658784643)
  ·
    refine ⟨169400947107565199488176965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112933964738376799658784643 169400947107565199488176965)
    ·
      refine ⟨31762677582668474904033181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169400947107565199488176965 31762677582668474904033181)
      ·
        refine ⟨11911004093500678089012443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31762677582668474904033181 11911004093500678089012443)
        ·
          refine ⟨17866506140251017133518665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911004093500678089012443 17866506140251017133518665)
          ·
            refine ⟨13399879605188262850138999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17866506140251017133518665 13399879605188262850138999)
            ·
              refine ⟨20099819407782394275208499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13399879605188262850138999 20099819407782394275208499)
              ·
                refine ⟨30149729111673591412812749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20099819407782394275208499 30149729111673591412812749)
                ·
                  refine ⟨11306148416877596779804781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30149729111673591412812749 11306148416877596779804781)
                  ·
                    refine ⟨4239805656329098792426793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11306148416877596779804781 4239805656329098792426793)
                    ·
                      refine ⟨3179854242246824094320095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239805656329098792426793 3179854242246824094320095)
                      ·
                        rfl

theorem cell23_6192744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6192744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192744 prefixEnd_6192744 := by exact prefixLift 6192744
  have htrace : WordTrace (prefixWord ++ tailWord_6192744) baseStart_6192744 baseEnd_6192744 := by
    simpa [prefixWord, tailWord_6192744, baseEnd_6192744] using wordTrace_append hprefix tailTrace_6192744
  have hstable : (prefixWord ++ tailWord_6192744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192744).length < 2 ^ (prefixWord ++ tailWord_6192744).sum := by decide
  have hdescent : baseEnd_6192744 < baseStart_6192744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192857 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_6192857 : Nat := 118140960795 + 6192857 * 2 ^ 59
def prefixEnd_6192857 : Nat := 4983230072969 + 3 ^ 40 * 6192857 * 2
def baseEnd_6192857 : Nat := 1059970755186927384069025

theorem tailTrace_6192857 : CollatzResearch.WordTrace tailWord_6192857 prefixEnd_6192857 1059970755186927384069025 := by
  unfold tailWord_6192857
  simp only [CollatzResearch.WordTrace]
  refine ⟨225872050925344219616432825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150581367283562813077621883 225872050925344219616432825)
  ·
    refine ⟨169404038194008164712324619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225872050925344219616432825 169404038194008164712324619)
    ·
      refine ⟨254106057291012247068486929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169404038194008164712324619 254106057291012247068486929)
      ·
        refine ⟨190579542968259185301365197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254106057291012247068486929 190579542968259185301365197)
        ·
          refine ⟨71467328613097194488011949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190579542968259185301365197 71467328613097194488011949)
          ·
            refine ⟨26800248229911447933004481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71467328613097194488011949 26800248229911447933004481)
            ·
              refine ⟨20100186172433585949753361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26800248229911447933004481 20100186172433585949753361)
              ·
                refine ⟨15075139629325189462315021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20100186172433585949753361 15075139629325189462315021)
                ·
                  refine ⟨5653177360996946048368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15075139629325189462315021 5653177360996946048368133)
                  ·
                    refine ⟨1059970755186927384069025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653177360996946048368133 1059970755186927384069025)
                    ·
                      rfl

theorem cell23_6192857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_6192857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192857 prefixEnd_6192857 := by exact prefixLift 6192857
  have htrace : WordTrace (prefixWord ++ tailWord_6192857) baseStart_6192857 baseEnd_6192857 := by
    simpa [prefixWord, tailWord_6192857, baseEnd_6192857] using wordTrace_append hprefix tailTrace_6192857
  have hstable : (prefixWord ++ tailWord_6192857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192857).length < 2 ^ (prefixWord ++ tailWord_6192857).sum := by decide
  have hdescent : baseEnd_6192857 < baseStart_6192857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192907 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 5, 2]
def baseStart_6192907 : Nat := 118140960795 + 6192907 * 2 ^ 59
def prefixEnd_6192907 : Nat := 4983230072969 + 3 ^ 40 * 6192907 * 2
def baseEnd_6192907 : Nat := 3179937939593506956581845

theorem tailTrace_6192907 : CollatzResearch.WordTrace tailWord_6192907 prefixEnd_6192907 3179937939593506956581845 := by
  unfold tailWord_6192907
  simp only [CollatzResearch.WordTrace]
  refine ⟨225873874575163078155752975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150582583050108718770501983 225873874575163078155752975)
  ·
    refine ⟨338810811862744617233629463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225873874575163078155752975 338810811862744617233629463)
    ·
      refine ⟨508216217794116925850444195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338810811862744617233629463 508216217794116925850444195)
      ·
        refine ⟨762324326691175388775666293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508216217794116925850444195 762324326691175388775666293)
        ·
          refine ⟨71467905627297692697718715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 762324326691175388775666293 71467905627297692697718715)
          ·
            refine ⟨107201858440946539046578073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71467905627297692697718715 107201858440946539046578073)
            ·
              refine ⟨80401393830709904284933555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107201858440946539046578073 80401393830709904284933555)
              ·
                refine ⟨120602090746064856427400333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80401393830709904284933555 120602090746064856427400333)
                ·
                  refine ⟨45225784029774321160275125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120602090746064856427400333 45225784029774321160275125)
                  ·
                    refine ⟨4239917252791342608775793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45225784029774321160275125 4239917252791342608775793)
                    ·
                      refine ⟨3179937939593506956581845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4239917252791342608775793 3179937939593506956581845)
                      ·
                        rfl

theorem cell23_6192907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5, 2].length) (baseStart_6192907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192907 prefixEnd_6192907 := by exact prefixLift 6192907
  have htrace : WordTrace (prefixWord ++ tailWord_6192907) baseStart_6192907 baseEnd_6192907 := by
    simpa [prefixWord, tailWord_6192907, baseEnd_6192907] using wordTrace_append hprefix tailTrace_6192907
  have hstable : (prefixWord ++ tailWord_6192907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192907).length < 2 ^ (prefixWord ++ tailWord_6192907).sum := by decide
  have hdescent : baseEnd_6192907 < baseStart_6192907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192917 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_6192917 : Nat := 118140960795 + 6192917 * 2 ^ 59
def prefixEnd_6192917 : Nat := 4983230072969 + 3 ^ 40 * 6192917 * 2
def baseEnd_6192917 : Nat := 1059981024800017305818933

theorem tailTrace_6192917 : CollatzResearch.WordTrace tailWord_6192917 prefixEnd_6192917 1059981024800017305818933 := by
  unfold tailWord_6192917
  simp only [CollatzResearch.WordTrace]
  refine ⟨225874239305126849863617005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150582826203417899909078003 225874239305126849863617005)
  ·
    refine ⟨84702839739422568698856377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225874239305126849863617005 84702839739422568698856377)
    ·
      refine ⟨63527129804566926524142283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84702839739422568698856377 63527129804566926524142283)
      ·
        refine ⟨95290694706850389786213425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63527129804566926524142283 95290694706850389786213425)
        ·
          refine ⟨71468021030137792339660069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95290694706850389786213425 71468021030137792339660069)
          ·
            refine ⟨13400253943150836063686263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71468021030137792339660069 13400253943150836063686263)
            ·
              refine ⟨20100380914726254095529395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13400253943150836063686263 20100380914726254095529395)
              ·
                refine ⟨30150571372089381143294093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20100380914726254095529395 30150571372089381143294093)
                ·
                  refine ⟨11306464264533517928735285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30150571372089381143294093 11306464264533517928735285)
                  ·
                    refine ⟨1059981024800017305818933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11306464264533517928735285 1059981024800017305818933)
                    ·
                      rfl

theorem cell23_6192917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_6192917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192917 prefixEnd_6192917 := by exact prefixLift 6192917
  have htrace : WordTrace (prefixWord ++ tailWord_6192917) baseStart_6192917 baseEnd_6192917 := by
    simpa [prefixWord, tailWord_6192917, baseEnd_6192917] using wordTrace_append hprefix tailTrace_6192917
  have hstable : (prefixWord ++ tailWord_6192917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192917).length < 2 ^ (prefixWord ++ tailWord_6192917).sum := by decide
  have hdescent : baseEnd_6192917 < baseStart_6192917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192942 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6192942 : Nat := 118140960795 + 6192942 * 2 ^ 59
def prefixEnd_6192942 : Nat := 4983230072969 + 3 ^ 40 * 6192942 * 2
def baseEnd_6192942 : Nat := 1059985303805471439881395

theorem tailTrace_6192942 : CollatzResearch.WordTrace tailWord_6192942 prefixEnd_6192942 1059985303805471439881395 := by
  unfold tailWord_6192942
  simp only [CollatzResearch.WordTrace]
  refine ⟨28234393891254534891659635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150583434086690852755518053 28234393891254534891659635)
  ·
    refine ⟨42351590836881802337489453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28234393891254534891659635 42351590836881802337489453)
    ·
      refine ⟨15881846563830675876558545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42351590836881802337489453 15881846563830675876558545)
      ·
        refine ⟨11911384922873006907418909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15881846563830675876558545 11911384922873006907418909)
        ·
          refine ⟨4466769346077377590282091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11911384922873006907418909 4466769346077377590282091)
          ·
            refine ⟨6700154019116066385423137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466769346077377590282091 6700154019116066385423137)
            ·
              refine ⟨5025115514337049789067353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6700154019116066385423137 5025115514337049789067353)
              ·
                refine ⟨3768836635752787341800515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5025115514337049789067353 3768836635752787341800515)
                ·
                  refine ⟨5653254953629181012700773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768836635752787341800515 5653254953629181012700773)
                  ·
                    refine ⟨1059985303805471439881395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653254953629181012700773 1059985303805471439881395)
                    ·
                      rfl

theorem cell23_6192942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6192942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192942 prefixEnd_6192942 := by exact prefixLift 6192942
  have htrace : WordTrace (prefixWord ++ tailWord_6192942) baseStart_6192942 baseEnd_6192942 := by
    simpa [prefixWord, tailWord_6192942, baseEnd_6192942] using wordTrace_append hprefix tailTrace_6192942
  have hstable : (prefixWord ++ tailWord_6192942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192942).length < 2 ^ (prefixWord ++ tailWord_6192942).sum := by decide
  have hdescent : baseEnd_6192942 < baseStart_6192942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192967 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_6192967 : Nat := 118140960795 + 6192967 * 2 ^ 59
def prefixEnd_6192967 : Nat := 4983230072969 + 3 ^ 40 * 6192967 * 2
def baseEnd_6192967 : Nat := 3179968748432776721831569

theorem tailTrace_6192967 : CollatzResearch.WordTrace tailWord_6192967 prefixEnd_6192967 3179968748432776721831569 := by
  unfold tailWord_6192967
  simp only [CollatzResearch.WordTrace]
  refine ⟨225876062954945708402937155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150584041969963805601958103 225876062954945708402937155)
  ·
    refine ⟨338814094432418562604405733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225876062954945708402937155 338814094432418562604405733)
    ·
      refine ⟨63527642706078480488326075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338814094432418562604405733 63527642706078480488326075)
      ·
        refine ⟨95291464059117720732489113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63527642706078480488326075 95291464059117720732489113)
        ·
          refine ⟨71468598044338290549366835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95291464059117720732489113 71468598044338290549366835)
          ·
            refine ⟨107202897066507435824050253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71468598044338290549366835 107202897066507435824050253)
            ·
              refine ⟨40201086399940288434018845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107202897066507435824050253 40201086399940288434018845)
              ·
                refine ⟨15075407399977608162757067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40201086399940288434018845 15075407399977608162757067)
                ·
                  refine ⟨22613111099966412244135601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15075407399977608162757067 22613111099966412244135601)
                  ·
                    refine ⟨16959833324974809183101701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22613111099966412244135601 16959833324974809183101701)
                    ·
                      refine ⟨3179968748432776721831569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16959833324974809183101701 3179968748432776721831569)
                      ·
                        rfl

theorem cell23_6192967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_6192967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192967 prefixEnd_6192967 := by exact prefixLift 6192967
  have htrace : WordTrace (prefixWord ++ tailWord_6192967) baseStart_6192967 baseEnd_6192967 := by
    simpa [prefixWord, tailWord_6192967, baseEnd_6192967] using wordTrace_append hprefix tailTrace_6192967
  have hstable : (prefixWord ++ tailWord_6192967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192967).length < 2 ^ (prefixWord ++ tailWord_6192967).sum := by decide
  have hdescent : baseEnd_6192967 < baseStart_6192967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6192991 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 1, 2, 3]
def baseStart_6192991 : Nat := 118140960795 + 6192991 * 2 ^ 59
def prefixEnd_6192991 : Nat := 4983230072969 + 3 ^ 40 * 6192991 * 2
def baseEnd_6192991 : Nat := 3179981071968484627931459

theorem tailTrace_6192991 : CollatzResearch.WordTrace tailWord_6192991 prefixEnd_6192991 3179981071968484627931459 := by
  unfold tailWord_6192991
  simp only [CollatzResearch.WordTrace]
  refine ⟨225876938306858760501810827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150584625537905840334540551 225876938306858760501810827)
  ·
    refine ⟨338815407460288140752716241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225876938306858760501810827 338815407460288140752716241)
    ·
      refine ⟨254111555595216105564537181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338815407460288140752716241 254111555595216105564537181)
      ·
        refine ⟨95291833348206039586701443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254111555595216105564537181 95291833348206039586701443)
        ·
          refine ⟨142937750022309059380052165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95291833348206039586701443 142937750022309059380052165)
          ·
            refine ⟨26800828129182948633759781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142937750022309059380052165 26800828129182948633759781)
            ·
              refine ⟨5025155274221802868829959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26800828129182948633759781 5025155274221802868829959)
              ·
                refine ⟨7537732911332704303244939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025155274221802868829959 7537732911332704303244939)
                ·
                  refine ⟨11306599366999056454867409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537732911332704303244939 11306599366999056454867409)
                  ·
                    refine ⟨8479949525249292341150557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11306599366999056454867409 8479949525249292341150557)
                    ·
                      refine ⟨3179981071968484627931459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8479949525249292341150557 3179981071968484627931459)
                      ·
                        rfl

theorem cell23_6192991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_6192991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6192991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6192991 prefixEnd_6192991 := by exact prefixLift 6192991
  have htrace : WordTrace (prefixWord ++ tailWord_6192991) baseStart_6192991 baseEnd_6192991 := by
    simpa [prefixWord, tailWord_6192991, baseEnd_6192991] using wordTrace_append hprefix tailTrace_6192991
  have hstable : (prefixWord ++ tailWord_6192991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6192991).length < 2 ^ (prefixWord ++ tailWord_6192991).sum := by decide
  have hdescent : baseEnd_6192991 < baseStart_6192991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6192991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193047 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_6193047 : Nat := 118140960795 + 6193047 * 2 ^ 59
def prefixEnd_6193047 : Nat := 4983230072969 + 3 ^ 40 * 6193047 * 2
def baseEnd_6193047 : Nat := 3180009826885136408831201

theorem tailTrace_6193047 : CollatzResearch.WordTrace tailWord_6193047 prefixEnd_6193047 3180009826885136408831201 := by
  unfold tailWord_6193047
  simp only [CollatzResearch.WordTrace]
  refine ⟨225878980794655882065849395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150585987196437254710566263 225878980794655882065849395)
  ·
    refine ⟨338818471191983823098774093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225878980794655882065849395 338818471191983823098774093)
    ·
      refine ⟨127056926696993933662040285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338818471191983823098774093 127056926696993933662040285)
      ·
        refine ⟨47646347511372725123265107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127056926696993933662040285 47646347511372725123265107)
        ·
          refine ⟨71469521267059087684897661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47646347511372725123265107 71469521267059087684897661)
          ·
            refine ⟨26801070475147157881836623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71469521267059087684897661 26801070475147157881836623)
            ·
              refine ⟨40201605712720736822754935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26801070475147157881836623 40201605712720736822754935)
              ·
                refine ⟨60302408569081105234132403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40201605712720736822754935 60302408569081105234132403)
                ·
                  refine ⟨90453612853621657851198605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60302408569081105234132403 90453612853621657851198605)
                  ·
                    refine ⟨33920104820108121694199477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90453612853621657851198605 33920104820108121694199477)
                    ·
                      refine ⟨3180009826885136408831201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33920104820108121694199477 3180009826885136408831201)
                      ·
                        rfl

theorem cell23_6193047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_6193047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193047 prefixEnd_6193047 := by exact prefixLift 6193047
  have htrace : WordTrace (prefixWord ++ tailWord_6193047) baseStart_6193047 baseEnd_6193047 := by
    simpa [prefixWord, tailWord_6193047, baseEnd_6193047] using wordTrace_append hprefix tailTrace_6193047
  have hstable : (prefixWord ++ tailWord_6193047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193047).length < 2 ^ (prefixWord ++ tailWord_6193047).sum := by decide
  have hdescent : baseEnd_6193047 < baseStart_6193047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193097 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_6193097 : Nat := 118140960795 + 6193097 * 2 ^ 59
def prefixEnd_6193097 : Nat := 4983230072969 + 3 ^ 40 * 6193097 * 2
def baseEnd_6193097 : Nat := 1060011833639287071068657

theorem tailTrace_6193097 : CollatzResearch.WordTrace tailWord_6193097 prefixEnd_6193097 1060011833639287071068657 := by
  unfold tailWord_6193097
  simp only [CollatzResearch.WordTrace]
  refine ⟨225880804444474740605169545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150587202962983160403446363 225880804444474740605169545)
  ·
    refine ⟨169410603333356055453877159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225880804444474740605169545 169410603333356055453877159)
    ·
      refine ⟨254115905000034083180815739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169410603333356055453877159 254115905000034083180815739)
      ·
        refine ⟨381173857500051124771223609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254115905000034083180815739 381173857500051124771223609)
        ·
          refine ⟨285880393125038343578417707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381173857500051124771223609 285880393125038343578417707)
          ·
            refine ⟨428820589687557515367626561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285880393125038343578417707 428820589687557515367626561)
            ·
              refine ⟨321615442265668136525719921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428820589687557515367626561 321615442265668136525719921)
              ·
                refine ⟨241211581699251102394289941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321615442265668136525719921 241211581699251102394289941)
                ·
                  refine ⟨11306792892152395424732341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241211581699251102394289941 11306792892152395424732341)
                  ·
                    refine ⟨1060011833639287071068657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11306792892152395424732341 1060011833639287071068657)
                    ·
                      rfl

theorem cell23_6193097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_6193097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193097 prefixEnd_6193097 := by exact prefixLift 6193097
  have htrace : WordTrace (prefixWord ++ tailWord_6193097) baseStart_6193097 baseEnd_6193097 := by
    simpa [prefixWord, tailWord_6193097, baseEnd_6193097] using wordTrace_append hprefix tailTrace_6193097
  have hstable : (prefixWord ++ tailWord_6193097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193097).length < 2 ^ (prefixWord ++ tailWord_6193097).sum := by decide
  have hdescent : baseEnd_6193097 < baseStart_6193097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193144 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_6193144 : Nat := 118140960795 + 6193144 * 2 ^ 59
def prefixEnd_6193144 : Nat := 4983230072969 + 3 ^ 40 * 6193144 * 2
def baseEnd_6193144 : Nat := 1060019878169540843106085

theorem tailTrace_6193144 : CollatzResearch.WordTrace tailWord_6193144 prefixEnd_6193144 1060019878169540843106085 := by
  unfold tailWord_6193144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112941259337652233816065243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150588345783536311754753657 112941259337652233816065243)
  ·
    refine ⟨169411889006478350724097865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112941259337652233816065243 169411889006478350724097865)
    ·
      refine ⟨127058916754858763043073399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169411889006478350724097865 127058916754858763043073399)
      ·
        refine ⟨190588375132288144564610099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127058916754858763043073399 190588375132288144564610099)
        ·
          refine ⟨285882562698432216846915149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190588375132288144564610099 285882562698432216846915149)
          ·
            refine ⟨107205961011912081317593181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285882562698432216846915149 107205961011912081317593181)
            ·
              refine ⟨40202235379467030494097443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107205961011912081317593181 40202235379467030494097443)
              ·
                refine ⟨60303353069200545741146165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40202235379467030494097443 60303353069200545741146165)
                ·
                  refine ⟨5653439350237551163232453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60303353069200545741146165 5653439350237551163232453)
                  ·
                    refine ⟨1060019878169540843106085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653439350237551163232453 1060019878169540843106085)
                    ·
                      rfl

theorem cell23_6193144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_6193144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193144 prefixEnd_6193144 := by exact prefixLift 6193144
  have htrace : WordTrace (prefixWord ++ tailWord_6193144) baseStart_6193144 baseEnd_6193144 := by
    simpa [prefixWord, tailWord_6193144, baseEnd_6193144] using wordTrace_append hprefix tailTrace_6193144
  have hstable : (prefixWord ++ tailWord_6193144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193144).length < 2 ^ (prefixWord ++ tailWord_6193144).sum := by decide
  have hdescent : baseEnd_6193144 < baseStart_6193144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193178 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_6193178 : Nat := 118140960795 + 6193178 * 2 ^ 59
def prefixEnd_6193178 : Nat := 4983230072969 + 3 ^ 40 * 6193178 * 2
def baseEnd_6193178 : Nat := 1060025697616958465431033

theorem tailTrace_6193178 : CollatzResearch.WordTrace tailWord_6193178 prefixEnd_6193178 1060025697616958465431033 := by
  unfold tailWord_6193178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56470939689295322859717047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150589172504787527625912125 56470939689295322859717047)
  ·
    refine ⟨84706409533942984289575571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56470939689295322859717047 84706409533942984289575571)
    ·
      refine ⟨127059614300914476434363357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84706409533942984289575571 127059614300914476434363357)
      ·
        refine ⟨47647355362842928662886259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127059614300914476434363357 47647355362842928662886259)
        ·
          refine ⟨71471033044264392994329389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47647355362842928662886259 71471033044264392994329389)
          ·
            refine ⟨26801637391599147372873521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71471033044264392994329389 26801637391599147372873521)
            ·
              refine ⟨20101228043699360529655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26801637391599147372873521 20101228043699360529655141)
              ·
                refine ⟨3768980258193630099310339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20101228043699360529655141 3768980258193630099310339)
                ·
                  refine ⟨5653470387290445148965509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768980258193630099310339 5653470387290445148965509)
                  ·
                    refine ⟨1060025697616958465431033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653470387290445148965509 1060025697616958465431033)
                    ·
                      rfl

theorem cell23_6193178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_6193178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193178 prefixEnd_6193178 := by exact prefixLift 6193178
  have htrace : WordTrace (prefixWord ++ tailWord_6193178) baseStart_6193178 baseEnd_6193178 := by
    simpa [prefixWord, tailWord_6193178, baseEnd_6193178] using wordTrace_append hprefix tailTrace_6193178
  have hstable : (prefixWord ++ tailWord_6193178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193178).length < 2 ^ (prefixWord ++ tailWord_6193178).sum := by decide
  have hdescent : baseEnd_6193178 < baseStart_6193178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193258 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6193258 : Nat := 118140960795 + 6193258 * 2 ^ 59
def prefixEnd_6193258 : Nat := 4983230072969 + 3 ^ 40 * 6193258 * 2
def baseEnd_6193258 : Nat := 3180118171303235083292731

theorem tailTrace_6193258 : CollatzResearch.WordTrace tailWord_6193258 prefixEnd_6193258 3180118171303235083292731 := by
  unfold tailWord_6193258
  simp only [CollatzResearch.WordTrace]
  refine ⟨56471669149222866275445107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150591117731260976734520285 56471669149222866275445107)
  ·
    refine ⟨84707503723834299413167661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56471669149222866275445107 84707503723834299413167661)
    ·
      refine ⟨31765313896437862279937873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84707503723834299413167661 31765313896437862279937873)
      ·
        refine ⟨23823985422328396709953405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31765313896437862279937873 23823985422328396709953405)
        ·
          refine ⟨8933994533373148766232527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23823985422328396709953405 8933994533373148766232527)
          ·
            refine ⟨13400991800059723149348791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8933994533373148766232527 13400991800059723149348791)
            ·
              refine ⟨20101487700089584724023187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13400991800059723149348791 20101487700089584724023187)
              ·
                refine ⟨30152231550134377086034781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20101487700089584724023187 30152231550134377086034781)
                ·
                  refine ⟨11307086831300391407263043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30152231550134377086034781 11307086831300391407263043)
                  ·
                    refine ⟨16960630246950587110894565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11307086831300391407263043 16960630246950587110894565)
                    ·
                      refine ⟨3180118171303235083292731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16960630246950587110894565 3180118171303235083292731)
                      ·
                        rfl

theorem cell23_6193258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6193258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193258 prefixEnd_6193258 := by exact prefixLift 6193258
  have htrace : WordTrace (prefixWord ++ tailWord_6193258) baseStart_6193258 baseEnd_6193258 := by
    simpa [prefixWord, tailWord_6193258, baseEnd_6193258] using wordTrace_append hprefix tailTrace_6193258
  have hstable : (prefixWord ++ tailWord_6193258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193258).length < 2 ^ (prefixWord ++ tailWord_6193258).sum := by decide
  have hdescent : baseEnd_6193258 < baseStart_6193258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193264 : List Nat := [2, 1, 1, 1, 5, 2, 2, 9]
def baseStart_6193264 : Nat := 118140960795 + 6193264 * 2 ^ 59
def prefixEnd_6193264 : Nat := 4983230072969 + 3 ^ 40 * 6193264 * 2
def baseEnd_6193264 : Nat := 117782268599524520733989

theorem tailTrace_6193264 : CollatzResearch.WordTrace tailWord_6193264 prefixEnd_6193264 117782268599524520733989 := by
  unfold tailWord_6193264
  simp only [CollatzResearch.WordTrace]
  refine ⟨112943447717434864063249423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150591263623246485417665897 112943447717434864063249423)
  ·
    refine ⟨169415171576152296094874135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112943447717434864063249423 169415171576152296094874135)
    ·
      refine ⟨254122757364228444142311203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169415171576152296094874135 254122757364228444142311203)
      ·
        refine ⟨381184136046342666213466805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254122757364228444142311203 381184136046342666213466805)
        ·
          refine ⟨35736012754344624957512513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381184136046342666213466805 35736012754344624957512513)
          ·
            refine ⟨26802009565758468718134385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35736012754344624957512513 26802009565758468718134385)
            ·
              refine ⟨20101507174318851538600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26802009565758468718134385 20101507174318851538600789)
              ·
                refine ⟨117782268599524520733989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20101507174318851538600789 117782268599524520733989)
                ·
                  rfl

theorem cell23_6193264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_6193264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193264 prefixEnd_6193264 := by exact prefixLift 6193264
  have htrace : WordTrace (prefixWord ++ tailWord_6193264) baseStart_6193264 baseEnd_6193264 := by
    simpa [prefixWord, tailWord_6193264, baseEnd_6193264] using wordTrace_append hprefix tailTrace_6193264
  have hstable : (prefixWord ++ tailWord_6193264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193264).length < 2 ^ (prefixWord ++ tailWord_6193264).sum := by decide
  have hdescent : baseEnd_6193264 < baseStart_6193264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193271 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_6193271 : Nat := 118140960795 + 6193271 * 2 ^ 59
def prefixEnd_6193271 : Nat := 4983230072969 + 3 ^ 40 * 6193271 * 2
def baseEnd_6193271 : Nat := 3180124846551743532430171

theorem tailTrace_6193271 : CollatzResearch.WordTrace tailWord_6193271 prefixEnd_6193271 3180124846551743532430171 := by
  unfold tailWord_6193271
  simp only [CollatzResearch.WordTrace]
  refine ⟨225887150745844368322003667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150591433830562912214669111 225887150745844368322003667)
  ·
    refine ⟨338830726118766552483005501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225887150745844368322003667 338830726118766552483005501)
    ·
      refine ⟨127061522294537457181127063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338830726118766552483005501 127061522294537457181127063)
      ·
        refine ⟨190592283441806185771690595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127061522294537457181127063 190592283441806185771690595)
        ·
          refine ⟨285888425162709278657535893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190592283441806185771690595 285888425162709278657535893)
          ·
            refine ⟨13401019929501997437071995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285888425162709278657535893 13401019929501997437071995)
            ·
              refine ⟨20101529894252996155607993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401019929501997437071995 20101529894252996155607993)
              ·
                refine ⟨15076147420689747116705995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20101529894252996155607993 15076147420689747116705995)
                ·
                  refine ⟨22614221131034620675058993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076147420689747116705995 22614221131034620675058993)
                  ·
                    refine ⟨16960665848275965506294245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22614221131034620675058993 16960665848275965506294245)
                    ·
                      refine ⟨3180124846551743532430171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16960665848275965506294245 3180124846551743532430171)
                      ·
                        rfl

theorem cell23_6193271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_6193271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193271 prefixEnd_6193271 := by exact prefixLift 6193271
  have htrace : WordTrace (prefixWord ++ tailWord_6193271) baseStart_6193271 baseEnd_6193271 := by
    simpa [prefixWord, tailWord_6193271, baseEnd_6193271] using wordTrace_append hprefix tailTrace_6193271
  have hstable : (prefixWord ++ tailWord_6193271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193271).length < 2 ^ (prefixWord ++ tailWord_6193271).sum := by decide
  have hdescent : baseEnd_6193271 < baseStart_6193271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193281 : List Nat := [1, 2, 4, 2, 4, 10]
def baseStart_6193281 : Nat := 118140960795 + 6193281 * 2 ^ 59
def prefixEnd_6193281 : Nat := 4983230072969 + 3 ^ 40 * 6193281 * 2
def baseEnd_6193281 : Nat := 13086954655795425898375

theorem tailTrace_6193281 : CollatzResearch.WordTrace tailWord_6193281 prefixEnd_6193281 13086954655795425898375 := by
  unfold tailWord_6193281
  simp only [CollatzResearch.WordTrace]
  refine ⟨225887515475808140029867697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150591676983872093353245131 225887515475808140029867697)
  ·
    refine ⟨169415636606856105022400773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225887515475808140029867697 169415636606856105022400773)
    ·
      refine ⟨31765431863785519691700145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169415636606856105022400773 31765431863785519691700145)
      ·
        refine ⟨23824073897839139768775109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31765431863785519691700145 23824073897839139768775109)
        ·
          refine ⟨4467013855844838706645333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23824073897839139768775109 4467013855844838706645333)
          ·
            refine ⟨13086954655795425898375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4467013855844838706645333 13086954655795425898375)
            ·
              rfl

theorem cell23_6193281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 10].length) (baseStart_6193281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193281 prefixEnd_6193281 := by exact prefixLift 6193281
  have htrace : WordTrace (prefixWord ++ tailWord_6193281) baseStart_6193281 baseEnd_6193281 := by
    simpa [prefixWord, tailWord_6193281, baseEnd_6193281] using wordTrace_append hprefix tailTrace_6193281
  have hstable : (prefixWord ++ tailWord_6193281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193281).length < 2 ^ (prefixWord ++ tailWord_6193281).sum := by decide
  have hdescent : baseEnd_6193281 < baseStart_6193281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193308 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6193308 : Nat := 118140960795 + 6193308 * 2 ^ 59
def prefixEnd_6193308 : Nat := 4983230072969 + 3 ^ 40 * 6193308 * 2
def baseEnd_6193308 : Nat := 3180143845335959887667501

theorem tailTrace_6193308 : CollatzResearch.WordTrace tailWord_6193308 prefixEnd_6193308 3180143845335959887667501 := by
  unfold tailWord_6193308
  simp only [CollatzResearch.WordTrace]
  refine ⟨112944250123355161820550289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150592333497806882427400385 112944250123355161820550289)
  ·
    refine ⟨84708187592516371365412717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112944250123355161820550289 84708187592516371365412717)
    ·
      refine ⟨31765570347193639262029769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84708187592516371365412717 31765570347193639262029769)
      ·
        refine ⟨23824177760395229446522327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31765570347193639262029769 23824177760395229446522327)
        ·
          refine ⟨35736266640592844169783491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23824177760395229446522327 35736266640592844169783491)
          ·
            refine ⟨53604399960889266254675237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35736266640592844169783491 53604399960889266254675237)
            ·
              refine ⟨10050824992666737422751607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53604399960889266254675237 10050824992666737422751607)
              ·
                refine ⟨15076237489000106134127411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050824992666737422751607 15076237489000106134127411)
                ·
                  refine ⟨22614356233500159201191117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076237489000106134127411 22614356233500159201191117)
                  ·
                    refine ⟨8480383587562559700446669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22614356233500159201191117 8480383587562559700446669)
                    ·
                      refine ⟨3180143845335959887667501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480383587562559700446669 3180143845335959887667501)
                      ·
                        rfl

theorem cell23_6193308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6193308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193308 prefixEnd_6193308 := by exact prefixLift 6193308
  have htrace : WordTrace (prefixWord ++ tailWord_6193308) baseStart_6193308 baseEnd_6193308 := by
    simpa [prefixWord, tailWord_6193308, baseEnd_6193308] using wordTrace_append hprefix tailTrace_6193308
  have hstable : (prefixWord ++ tailWord_6193308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193308).length < 2 ^ (prefixWord ++ tailWord_6193308).sum := by decide
  have hdescent : baseEnd_6193308 < baseStart_6193308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193326 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6193326 : Nat := 118140960795 + 6193326 * 2 ^ 59
def prefixEnd_6193326 : Nat := 4983230072969 + 3 ^ 40 * 6193326 * 2
def baseEnd_6193326 : Nat := 3180153087987740817242419

theorem tailTrace_6193326 : CollatzResearch.WordTrace tailWord_6193326 prefixEnd_6193326 3180153087987740817242419 := by
  unfold tailWord_6193326
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236144595080639089406979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150592771173763408476837221 28236144595080639089406979)
  ·
    refine ⟨42354216892620958634110469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28236144595080639089406979 42354216892620958634110469)
    ·
      refine ⟨7941415667366429743895713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42354216892620958634110469 7941415667366429743895713)
      ·
        refine ⟨5956061750524822307921785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7941415667366429743895713 5956061750524822307921785)
        ·
          refine ⟨4467046312893616730941339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5956061750524822307921785 4467046312893616730941339)
          ·
            refine ⟨6700569469340425096412009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467046312893616730941339 6700569469340425096412009)
            ·
              refine ⟨5025427102005318822309007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6700569469340425096412009 5025427102005318822309007)
              ·
                refine ⟨7538140653007978233463511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025427102005318822309007 7538140653007978233463511)
                ·
                  refine ⟨11307210979511967350195267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538140653007978233463511 11307210979511967350195267)
                  ·
                    refine ⟨16960816469267951025292901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11307210979511967350195267 16960816469267951025292901)
                    ·
                      refine ⟨3180153087987740817242419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16960816469267951025292901 3180153087987740817242419)
                      ·
                        rfl

theorem cell23_6193326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6193326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193326 prefixEnd_6193326 := by exact prefixLift 6193326
  have htrace : WordTrace (prefixWord ++ tailWord_6193326) baseStart_6193326 baseEnd_6193326 := by
    simpa [prefixWord, tailWord_6193326, baseEnd_6193326] using wordTrace_append hprefix tailTrace_6193326
  have hstable : (prefixWord ++ tailWord_6193326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193326).length < 2 ^ (prefixWord ++ tailWord_6193326).sum := by decide
  have hdescent : baseEnd_6193326 < baseStart_6193326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193329 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6193329 : Nat := 118140960795 + 6193329 * 2 ^ 59
def prefixEnd_6193329 : Nat := 4983230072969 + 3 ^ 40 * 6193329 * 2
def baseEnd_6193329 : Nat := 3180154628429704305504905

theorem tailTrace_6193329 : CollatzResearch.WordTrace tailWord_6193329 prefixEnd_6193329 3180154628429704305504905 := by
  unfold tailWord_6193329
  simp only [CollatzResearch.WordTrace]
  refine ⟨225889266179634244227615041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150592844119756162818410027 225889266179634244227615041)
  ·
    refine ⟨169416949634725683170711281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225889266179634244227615041 169416949634725683170711281)
    ·
      refine ⟨127062712226044262378033461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169416949634725683170711281 127062712226044262378033461)
      ·
        refine ⟨11912129271191649597940637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127062712226044262378033461 11912129271191649597940637)
        ·
          refine ⟨4467048476696868599227739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11912129271191649597940637 4467048476696868599227739)
          ·
            refine ⟨6700572715045302898841609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467048476696868599227739 6700572715045302898841609)
            ·
              refine ⟨5025429536283977174131207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6700572715045302898841609 5025429536283977174131207)
              ·
                refine ⟨7538144304425965761196811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025429536283977174131207 7538144304425965761196811)
                ·
                  refine ⟨11307216456638948641795217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538144304425965761196811 11307216456638948641795217)
                  ·
                    refine ⟨8480412342479211481346413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11307216456638948641795217 8480412342479211481346413)
                    ·
                      refine ⟨3180154628429704305504905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480412342479211481346413 3180154628429704305504905)
                      ·
                        rfl

theorem cell23_6193329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6193329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193329 prefixEnd_6193329 := by exact prefixLift 6193329
  have htrace : WordTrace (prefixWord ++ tailWord_6193329) baseStart_6193329 baseEnd_6193329 := by
    simpa [prefixWord, tailWord_6193329, baseEnd_6193329] using wordTrace_append hprefix tailTrace_6193329
  have hstable : (prefixWord ++ tailWord_6193329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193329).length < 2 ^ (prefixWord ++ tailWord_6193329).sum := by decide
  have hdescent : baseEnd_6193329 < baseStart_6193329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193335 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_6193335 : Nat := 118140960795 + 6193335 * 2 ^ 59
def prefixEnd_6193335 : Nat := 4983230072969 + 3 ^ 40 * 6193335 * 2
def baseEnd_6193335 : Nat := 3180157709313631282029877

theorem tailTrace_6193335 : CollatzResearch.WordTrace tailWord_6193335 prefixEnd_6193335 3180157709313631282029877 := by
  unfold tailWord_6193335
  simp only [CollatzResearch.WordTrace]
  refine ⟨225889485017612507252333459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150592990011741671501555639 225889485017612507252333459)
  ·
    refine ⟨338834227526418760878500189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225889485017612507252333459 338834227526418760878500189)
    ·
      refine ⟨127062835322407035329437571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338834227526418760878500189 127062835322407035329437571)
      ·
        refine ⟨190594252983610552994156357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127062835322407035329437571 190594252983610552994156357)
        ·
          refine ⟨35736422434426978686404317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190594252983610552994156357 35736422434426978686404317)
          ·
            refine ⟨13401158412910117007401619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35736422434426978686404317 13401158412910117007401619)
            ·
              refine ⟨20101737619365175511102429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401158412910117007401619 20101737619365175511102429)
              ·
                refine ⟨7538151607261940816663411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20101737619365175511102429 7538151607261940816663411)
                ·
                  refine ⟨11307227410892911224995117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538151607261940816663411 11307227410892911224995117)
                  ·
                    refine ⟨4240210279084841709373169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11307227410892911224995117 4240210279084841709373169)
                    ·
                      refine ⟨3180157709313631282029877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240210279084841709373169 3180157709313631282029877)
                      ·
                        rfl

theorem cell23_6193335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_6193335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193335 prefixEnd_6193335 := by exact prefixLift 6193335
  have htrace : WordTrace (prefixWord ++ tailWord_6193335) baseStart_6193335 baseEnd_6193335 := by
    simpa [prefixWord, tailWord_6193335, baseEnd_6193335] using wordTrace_append hprefix tailTrace_6193335
  have hstable : (prefixWord ++ tailWord_6193335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193335).length < 2 ^ (prefixWord ++ tailWord_6193335).sum := by decide
  have hdescent : baseEnd_6193335 < baseStart_6193335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193361 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_6193361 : Nat := 118140960795 + 6193361 * 2 ^ 59
def prefixEnd_6193361 : Nat := 4983230072969 + 3 ^ 40 * 6193361 * 2
def baseEnd_6193361 : Nat := 3180171059810648180304757

theorem tailTrace_6193361 : CollatzResearch.WordTrace tailWord_6193361 prefixEnd_6193361 3180171059810648180304757 := by
  unfold tailWord_6193361
  simp only [CollatzResearch.WordTrace]
  refine ⟨225890433315518313692779937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150593622210345542461853291 225890433315518313692779937)
  ·
    refine ⟨169417824986638735269584953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225890433315518313692779937 169417824986638735269584953)
    ·
      refine ⟨127063368739979051452188715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169417824986638735269584953 127063368739979051452188715)
      ·
        refine ⟨190595053109968577178283073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127063368739979051452188715 190595053109968577178283073)
        ·
          refine ⟨142946289832476432883712305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190595053109968577178283073 142946289832476432883712305)
          ·
            refine ⟨107209717374357324662784229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142946289832476432883712305 107209717374357324662784229)
            ·
              refine ⟨20101822007691998374272043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107209717374357324662784229 20101822007691998374272043)
              ·
                refine ⟨30152733011537997561408065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20101822007691998374272043 30152733011537997561408065)
                ·
                  refine ⟨22614549758653498171056049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30152733011537997561408065 22614549758653498171056049)
                  ·
                    refine ⟨16960912318990123628292037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22614549758653498171056049 16960912318990123628292037)
                    ·
                      refine ⟨3180171059810648180304757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16960912318990123628292037 3180171059810648180304757)
                      ·
                        rfl

theorem cell23_6193361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_6193361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193361 prefixEnd_6193361 := by exact prefixLift 6193361
  have htrace : WordTrace (prefixWord ++ tailWord_6193361) baseStart_6193361 baseEnd_6193361 := by
    simpa [prefixWord, tailWord_6193361, baseEnd_6193361] using wordTrace_append hprefix tailTrace_6193361
  have hstable : (prefixWord ++ tailWord_6193361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193361).length < 2 ^ (prefixWord ++ tailWord_6193361).sum := by decide
  have hdescent : baseEnd_6193361 < baseStart_6193361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193398 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6193398 : Nat := 118140960795 + 6193398 * 2 ^ 59
def prefixEnd_6193398 : Nat := 4983230072969 + 3 ^ 40 * 6193398 * 2
def baseEnd_6193398 : Nat := 3180190058594864535542087

theorem tailTrace_6193398 : CollatzResearch.WordTrace tailWord_6193398 prefixEnd_6193398 3180190058594864535542087 := by
  unfold tailWord_6193398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14118236426024016813242303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150594521877589512674584565 14118236426024016813242303)
  ·
    refine ⟨21177354639036025219863455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14118236426024016813242303 21177354639036025219863455)
    ·
      refine ⟨31766031958554037829795183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21177354639036025219863455 31766031958554037829795183)
      ·
        refine ⟨47649047937831056744692775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31766031958554037829795183 47649047937831056744692775)
        ·
          refine ⟨71473571906746585117039163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47649047937831056744692775 71473571906746585117039163)
          ·
            refine ⟨107210357860119877675558745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71473571906746585117039163 107210357860119877675558745)
            ·
              refine ⟨80407768395089908256669059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107210357860119877675558745 80407768395089908256669059)
              ·
                refine ⟨120611652592634862385003589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80407768395089908256669059 120611652592634862385003589)
                ·
                  refine ⟨22614684861119036697188173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120611652592634862385003589 22614684861119036697188173)
                  ·
                    refine ⟨8480506822919638761445565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22614684861119036697188173 8480506822919638761445565)
                    ·
                      refine ⟨3180190058594864535542087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480506822919638761445565 3180190058594864535542087)
                      ·
                        rfl

theorem cell23_6193398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6193398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193398 prefixEnd_6193398 := by exact prefixLift 6193398
  have htrace : WordTrace (prefixWord ++ tailWord_6193398) baseStart_6193398 baseEnd_6193398 := by
    simpa [prefixWord, tailWord_6193398, baseEnd_6193398] using wordTrace_append hprefix tailTrace_6193398
  have hstable : (prefixWord ++ tailWord_6193398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193398).length < 2 ^ (prefixWord ++ tailWord_6193398).sum := by decide
  have hdescent : baseEnd_6193398 < baseStart_6193398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193411 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_6193411 : Nat := 118140960795 + 6193411 * 2 ^ 59
def prefixEnd_6193411 : Nat := 4983230072969 + 3 ^ 40 * 6193411 * 2
def baseEnd_6193411 : Nat := 3180196733843372984679527

theorem tailTrace_6193411 : CollatzResearch.WordTrace tailWord_6193411 prefixEnd_6193411 3180196733843372984679527 := by
  unfold tailWord_6193411
  simp only [CollatzResearch.WordTrace]
  refine ⟨225892256965337172232100087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150594837976891448154733391 225892256965337172232100087)
  ·
    refine ⟨338838385448005758348150131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225892256965337172232100087 338838385448005758348150131)
    ·
      refine ⟨508257578172008637522225197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338838385448005758348150131 508257578172008637522225197)
      ·
        refine ⟨190596591814503239070834449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508257578172008637522225197 190596591814503239070834449)
        ·
          refine ⟨142947443860877429303125837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190596591814503239070834449 142947443860877429303125837)
          ·
            refine ⟨53605291447829035988672189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142947443860877429303125837 53605291447829035988672189)
            ·
              refine ⟨20101984292935888495752071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53605291447829035988672189 20101984292935888495752071)
              ·
                refine ⟨30152976439403832743628107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20101984292935888495752071 30152976439403832743628107)
                ·
                  refine ⟨45229464659105749115442161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30152976439403832743628107 45229464659105749115442161)
                  ·
                    refine ⟨33922098494329311836581621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45229464659105749115442161 33922098494329311836581621)
                    ·
                      refine ⟨3180196733843372984679527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33922098494329311836581621 3180196733843372984679527)
                      ·
                        rfl

theorem cell23_6193411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_6193411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193411 prefixEnd_6193411 := by exact prefixLift 6193411
  have htrace : WordTrace (prefixWord ++ tailWord_6193411) baseStart_6193411 baseEnd_6193411 := by
    simpa [prefixWord, tailWord_6193411, baseEnd_6193411] using wordTrace_append hprefix tailTrace_6193411
  have hstable : (prefixWord ++ tailWord_6193411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193411).length < 2 ^ (prefixWord ++ tailWord_6193411).sum := by decide
  have hdescent : baseEnd_6193411 < baseStart_6193411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193492 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_6193492 : Nat := 118140960795 + 6193492 * 2 ^ 59
def prefixEnd_6193492 : Nat := 4983230072969 + 3 ^ 40 * 6193492 * 2
def baseEnd_6193492 : Nat := 3180238325776387167766655

theorem tailTrace_6193492 : CollatzResearch.WordTrace tailWord_6193492 prefixEnd_6193492 3180238325776387167766655 := by
  unfold tailWord_6193492
  simp only [CollatzResearch.WordTrace]
  refine ⟨112947605639021861532899365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150596807518695815377199153 112947605639021861532899365)
  ·
    refine ⟨21177676057316599037418631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112947605639021861532899365 21177676057316599037418631)
    ·
      refine ⟨31766514085974898556127947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21177676057316599037418631 31766514085974898556127947)
      ·
        refine ⟨47649771128962347834191921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31766514085974898556127947 47649771128962347834191921)
        ·
          refine ⟨35737328346721760875643941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47649771128962347834191921 35737328346721760875643941)
          ·
            refine ⟨6700749065010330164183239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35737328346721760875643941 6700749065010330164183239)
            ·
              refine ⟨10051123597515495246274859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700749065010330164183239 10051123597515495246274859)
              ·
                refine ⟨15076685396273242869412289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051123597515495246274859 15076685396273242869412289)
                ·
                  refine ⟨11307514047204932152059217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15076685396273242869412289 11307514047204932152059217)
                  ·
                    refine ⟨8480635535403699114044413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11307514047204932152059217 8480635535403699114044413)
                    ·
                      refine ⟨3180238325776387167766655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480635535403699114044413 3180238325776387167766655)
                      ·
                        rfl

theorem cell23_6193492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_6193492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193492 prefixEnd_6193492 := by exact prefixLift 6193492
  have htrace : WordTrace (prefixWord ++ tailWord_6193492) baseStart_6193492 baseEnd_6193492 := by
    simpa [prefixWord, tailWord_6193492, baseEnd_6193492] using wordTrace_append hprefix tailTrace_6193492
  have hstable : (prefixWord ++ tailWord_6193492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193492).length < 2 ^ (prefixWord ++ tailWord_6193492).sum := by decide
  have hdescent : baseEnd_6193492 < baseStart_6193492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193522 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6193522 : Nat := 118140960795 + 6193522 * 2 ^ 59
def prefixEnd_6193522 : Nat := 4983230072969 + 3 ^ 40 * 6193522 * 2
def baseEnd_6193522 : Nat := 3180253730196022050391517

theorem tailTrace_6193522 : CollatzResearch.WordTrace tailWord_6193522 prefixEnd_6193522 3180253730196022050391517 := by
  unfold tailWord_6193522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56474076366983759547347705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150597536978623358792927213 56474076366983759547347705)
  ·
    refine ⟨42355557275237819660510779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56474076366983759547347705 42355557275237819660510779)
    ·
      refine ⟨63533335912856729490766169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42355557275237819660510779 63533335912856729490766169)
      ·
        refine ⟨47650001934642547118074627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63533335912856729490766169 47650001934642547118074627)
        ·
          refine ⟨71475002901963820677111941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47650001934642547118074627 71475002901963820677111941)
          ·
            refine ⟨13401563044118216376958489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71475002901963820677111941 13401563044118216376958489)
            ·
              refine ⟨10051172283088662282718867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401563044118216376958489 10051172283088662282718867)
              ·
                refine ⟨15076758424632993424078301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051172283088662282718867 15076758424632993424078301)
                ·
                  refine ⟨5653784409237372534029363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15076758424632993424078301 5653784409237372534029363)
                  ·
                    refine ⟨8480676613856058801044045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5653784409237372534029363 8480676613856058801044045)
                    ·
                      refine ⟨3180253730196022050391517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480676613856058801044045 3180253730196022050391517)
                      ·
                        rfl

theorem cell23_6193522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6193522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193522 prefixEnd_6193522 := by exact prefixLift 6193522
  have htrace : WordTrace (prefixWord ++ tailWord_6193522) baseStart_6193522 baseEnd_6193522 := by
    simpa [prefixWord, tailWord_6193522, baseEnd_6193522] using wordTrace_append hprefix tailTrace_6193522
  have hstable : (prefixWord ++ tailWord_6193522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193522).length < 2 ^ (prefixWord ++ tailWord_6193522).sum := by decide
  have hdescent : baseEnd_6193522 < baseStart_6193522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193545 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_6193545 : Nat := 118140960795 + 6193545 * 2 ^ 59
def prefixEnd_6193545 : Nat := 4983230072969 + 3 ^ 40 * 6193545 * 2
def baseEnd_6193545 : Nat := 3180265540251075460403911

theorem tailTrace_6193545 : CollatzResearch.WordTrace tailWord_6193545 prefixEnd_6193545 3180265540251075460403911 := by
  unfold tailWord_6193545
  simp only [CollatzResearch.WordTrace]
  refine ⟨225897144346851713117478089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150598096231234475411652059 225897144346851713117478089)
  ·
    refine ⟨169422858260138784838108567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225897144346851713117478089 169422858260138784838108567)
    ·
      refine ⟨254134287390208177257162851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169422858260138784838108567 254134287390208177257162851)
      ·
        refine ⟨381201431085312265885744277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254134287390208177257162851 381201431085312265885744277)
        ·
          refine ⟨17868817082124012463394263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 381201431085312265885744277 17868817082124012463394263)
          ·
            refine ⟨26803225623186018695091395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17868817082124012463394263 26803225623186018695091395)
            ·
              refine ⟨40204838434779028042637093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26803225623186018695091395 40204838434779028042637093)
              ·
                refine ⟨7538407206521067757994455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40204838434779028042637093 7538407206521067757994455)
                ·
                  refine ⟨11307610809781601636991683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7538407206521067757994455 11307610809781601636991683)
                  ·
                    refine ⟨16961416214672402455487525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11307610809781601636991683 16961416214672402455487525)
                    ·
                      refine ⟨3180265540251075460403911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16961416214672402455487525 3180265540251075460403911)
                      ·
                        rfl

theorem cell23_6193545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_6193545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193545 prefixEnd_6193545 := by exact prefixLift 6193545
  have htrace : WordTrace (prefixWord ++ tailWord_6193545) baseStart_6193545 baseEnd_6193545 := by
    simpa [prefixWord, tailWord_6193545, baseEnd_6193545] using wordTrace_append hprefix tailTrace_6193545
  have hstable : (prefixWord ++ tailWord_6193545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193545).length < 2 ^ (prefixWord ++ tailWord_6193545).sum := by decide
  have hdescent : baseEnd_6193545 < baseStart_6193545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193568 : List Nat := [2, 1, 1, 4, 1, 5, 9]
def baseStart_6193568 : Nat := 118140960795 + 6193568 * 2 ^ 59
def prefixEnd_6193568 : Nat := 4983230072969 + 3 ^ 40 * 6193568 * 2
def baseEnd_6193568 : Nat := 39262683337112702103905

theorem tailTrace_6193568 : CollatzResearch.WordTrace tailWord_6193568 prefixEnd_6193568 39262683337112702103905 := by
  unfold tailWord_6193568
  simp only [CollatzResearch.WordTrace]
  refine ⟨112948991612884194022782679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150598655483845592030376905 112948991612884194022782679)
  ·
    refine ⟨169423487419326291034174019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112948991612884194022782679 169423487419326291034174019)
    ·
      refine ⟨254135231128989436551261029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169423487419326291034174019 254135231128989436551261029)
      ·
        refine ⟨47650355836685519353361443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254135231128989436551261029 47650355836685519353361443)
        ·
          refine ⟨71475533755028279030042165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47650355836685519353361443 71475533755028279030042165)
          ·
            refine ⟨6700831289533901159066453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71475533755028279030042165 6700831289533901159066453)
            ·
              refine ⟨39262683337112702103905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6700831289533901159066453 39262683337112702103905)
              ·
                rfl

theorem cell23_6193568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 9].length) (baseStart_6193568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193568 prefixEnd_6193568 := by exact prefixLift 6193568
  have htrace : WordTrace (prefixWord ++ tailWord_6193568) baseStart_6193568 baseEnd_6193568 := by
    simpa [prefixWord, tailWord_6193568, baseEnd_6193568] using wordTrace_append hprefix tailTrace_6193568
  have hstable : (prefixWord ++ tailWord_6193568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193568).length < 2 ^ (prefixWord ++ tailWord_6193568).sum := by decide
  have hdescent : baseEnd_6193568 < baseStart_6193568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193612 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6193612 : Nat := 118140960795 + 6193612 * 2 ^ 59
def prefixEnd_6193612 : Nat := 4983230072969 + 3 ^ 40 * 6193612 * 2
def baseEnd_6193612 : Nat := 3180299943454926698266103

theorem tailTrace_6193612 : CollatzResearch.WordTrace tailWord_6193612 prefixEnd_6193612 3180299943454926698266103 := by
  unfold tailWord_6193612
  simp only [CollatzResearch.WordTrace]
  refine ⟨112949794018804491780083545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150599725358405989040111393 112949794018804491780083545)
  ·
    refine ⟨84712345514103368835062659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112949794018804491780083545 84712345514103368835062659)
    ·
      refine ⟨127068518271155053252593989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84712345514103368835062659 127068518271155053252593989)
      ·
        refine ⟨23825347175841572484861373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127068518271155053252593989 23825347175841572484861373)
        ·
          refine ⟨8934505190940589681823015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23825347175841572484861373 8934505190940589681823015)
          ·
            refine ⟨13401757786410884522734523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934505190940589681823015 13401757786410884522734523)
            ·
              refine ⟨20102636679616326784101785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401757786410884522734523 20102636679616326784101785)
              ·
                refine ⟨15076977509712245088076339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20102636679616326784101785 15076977509712245088076339)
                ·
                  refine ⟨22615466264568367632114509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15076977509712245088076339 22615466264568367632114509)
                  ·
                    refine ⟨8480799849213137862042941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22615466264568367632114509 8480799849213137862042941)
                    ·
                      refine ⟨3180299943454926698266103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480799849213137862042941 3180299943454926698266103)
                      ·
                        rfl

theorem cell23_6193612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6193612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193612 prefixEnd_6193612 := by exact prefixLift 6193612
  have htrace : WordTrace (prefixWord ++ tailWord_6193612) baseStart_6193612 baseEnd_6193612 := by
    simpa [prefixWord, tailWord_6193612, baseEnd_6193612] using wordTrace_append hprefix tailTrace_6193612
  have hstable : (prefixWord ++ tailWord_6193612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193612).length < 2 ^ (prefixWord ++ tailWord_6193612).sum := by decide
  have hdescent : baseEnd_6193612 < baseStart_6193612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193629 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_6193629 : Nat := 118140960795 + 6193629 * 2 ^ 59
def prefixEnd_6193629 : Nat := 4983230072969 + 3 ^ 40 * 6193629 * 2
def baseEnd_6193629 : Nat := 3180308672626053131753525

theorem tailTrace_6193629 : CollatzResearch.WordTrace tailWord_6193629 prefixEnd_6193629 3180308672626053131753525 := by
  unfold tailWord_6193629
  simp only [CollatzResearch.WordTrace]
  refine ⟨225900208078547395463535941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150600138719031596975690627 225900208078547395463535941)
  ·
    refine ⟨42356289014727636649412989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225900208078547395463535941 42356289014727636649412989)
    ·
      refine ⟨15883608380522863743529871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42356289014727636649412989 15883608380522863743529871)
      ·
        refine ⟨23825412570784295615294807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15883608380522863743529871 23825412570784295615294807)
        ·
          refine ⟨35738118856176443422942211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23825412570784295615294807 35738118856176443422942211)
          ·
            refine ⟨53607178284264665134413317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35738118856176443422942211 53607178284264665134413317)
            ·
              refine ⟨10051345928299624712702497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53607178284264665134413317 10051345928299624712702497)
              ·
                refine ⟨7538509446224718534526873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10051345928299624712702497 7538509446224718534526873)
                ·
                  refine ⟨5653882084668538900895155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7538509446224718534526873 5653882084668538900895155)
                  ·
                    refine ⟨8480823127002808351342733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5653882084668538900895155 8480823127002808351342733)
                    ·
                      refine ⟨3180308672626053131753525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480823127002808351342733 3180308672626053131753525)
                      ·
                        rfl

theorem cell23_6193629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_6193629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193629 prefixEnd_6193629 := by exact prefixLift 6193629
  have htrace : WordTrace (prefixWord ++ tailWord_6193629) baseStart_6193629 baseEnd_6193629 := by
    simpa [prefixWord, tailWord_6193629, baseEnd_6193629] using wordTrace_append hprefix tailTrace_6193629
  have hstable : (prefixWord ++ tailWord_6193629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193629).length < 2 ^ (prefixWord ++ tailWord_6193629).sum := by decide
  have hdescent : baseEnd_6193629 < baseStart_6193629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193645 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6193645 : Nat := 118140960795 + 6193645 * 2 ^ 59
def prefixEnd_6193645 : Nat := 4983230072969 + 3 ^ 40 * 6193645 * 2
def baseEnd_6193645 : Nat := 1060105629438841689717817

theorem tailTrace_6193645 : CollatzResearch.WordTrace tailWord_6193645 prefixEnd_6193645 1060105629438841689717817 := by
  unfold tailWord_6193645
  simp only [CollatzResearch.WordTrace]
  refine ⟨225900791646489430196118389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150600527764326286797412259 225900791646489430196118389)
  ·
    refine ⟨21178199216858384080886099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225900791646489430196118389 21178199216858384080886099)
    ·
      refine ⟨31767298825287576121329149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21178199216858384080886099 31767298825287576121329149)
      ·
        refine ⟨11912737059482841045498431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31767298825287576121329149 11912737059482841045498431)
        ·
          refine ⟨17869105589224261568247647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912737059482841045498431 17869105589224261568247647)
          ·
            refine ⟨26803658383836392352371471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17869105589224261568247647 26803658383836392352371471)
            ·
              refine ⟨40205487575754588528557207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26803658383836392352371471 40205487575754588528557207)
              ·
                refine ⟨60308231363631882792835811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40205487575754588528557207 60308231363631882792835811)
                ·
                  refine ⟨90462347045447824189253717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60308231363631882792835811 90462347045447824189253717)
                  ·
                    refine ⟨1060105629438841689717817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90462347045447824189253717 1060105629438841689717817)
                    ·
                      rfl

theorem cell23_6193645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6193645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193645 prefixEnd_6193645 := by exact prefixLift 6193645
  have htrace : WordTrace (prefixWord ++ tailWord_6193645) baseStart_6193645 baseEnd_6193645 := by
    simpa [prefixWord, tailWord_6193645, baseEnd_6193645] using wordTrace_append hprefix tailTrace_6193645
  have hstable : (prefixWord ++ tailWord_6193645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193645).length < 2 ^ (prefixWord ++ tailWord_6193645).sum := by decide
  have hdescent : baseEnd_6193645 < baseStart_6193645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193685 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_6193685 : Nat := 118140960795 + 6193685 * 2 ^ 59
def prefixEnd_6193685 : Nat := 4983230072969 + 3 ^ 40 * 6193685 * 2
def baseEnd_6193685 : Nat := 3180337427542704912653267

theorem tailTrace_6193685 : CollatzResearch.WordTrace tailWord_6193685 prefixEnd_6193685 3180337427542704912653267 := by
  unfold tailWord_6193685
  simp only [CollatzResearch.WordTrace]
  refine ⟨225902250566344517027574509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150601500377563011351716339 225902250566344517027574509)
  ·
    refine ⟨84713343962379193885340441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225902250566344517027574509 84713343962379193885340441)
    ·
      refine ⟨63535007971784395414005331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84713343962379193885340441 63535007971784395414005331)
      ·
        refine ⟨95302511957676593121007997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63535007971784395414005331 95302511957676593121007997)
        ·
          refine ⟨35738441984128722420377999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95302511957676593121007997 35738441984128722420377999)
          ·
            refine ⟨53607662976193083630566999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35738441984128722420377999 53607662976193083630566999)
            ·
              refine ⟨80411494464289625445850499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53607662976193083630566999 80411494464289625445850499)
              ·
                refine ⟨120617241696434438168775749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80411494464289625445850499 120617241696434438168775749)
                ·
                  refine ⟨22615732818081457156645453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120617241696434438168775749 22615732818081457156645453)
                  ·
                    refine ⟨8480899806780546433742045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22615732818081457156645453 8480899806780546433742045)
                    ·
                      refine ⟨3180337427542704912653267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8480899806780546433742045 3180337427542704912653267)
                      ·
                        rfl

theorem cell23_6193685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_6193685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193685 prefixEnd_6193685 := by exact prefixLift 6193685
  have htrace : WordTrace (prefixWord ++ tailWord_6193685) baseStart_6193685 baseEnd_6193685 := by
    simpa [prefixWord, tailWord_6193685, baseEnd_6193685] using wordTrace_append hprefix tailTrace_6193685
  have hstable : (prefixWord ++ tailWord_6193685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193685).length < 2 ^ (prefixWord ++ tailWord_6193685).sum := by decide
  have hdescent : baseEnd_6193685 < baseStart_6193685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193692 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 5]
def baseStart_6193692 : Nat := 118140960795 + 6193692 * 2 ^ 59
def prefixEnd_6193692 : Nat := 4983230072969 + 3 ^ 40 * 6193692 * 2
def baseEnd_6193692 : Nat := 353371224656365153918415

theorem tailTrace_6193692 : CollatzResearch.WordTrace tailWord_6193692 prefixEnd_6193692 353371224656365153918415 := by
  unfold tailWord_6193692
  simp only [CollatzResearch.WordTrace]
  refine ⟨112951252938659578611539665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150601670584879438148719553 112951252938659578611539665)
  ·
    refine ⟨84713439703994683958654749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112951252938659578611539665 84713439703994683958654749)
    ·
      refine ⟨31767539888998006484495531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84713439703994683958654749 31767539888998006484495531)
      ·
        refine ⟨47651309833497009726743297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31767539888998006484495531 47651309833497009726743297)
        ·
          refine ⟨35738482375122757295057473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47651309833497009726743297 35738482375122757295057473)
          ·
            refine ⟨26803861781342067971293105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35738482375122757295057473 26803861781342067971293105)
            ·
              refine ⟨20102896336006550978469829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26803861781342067971293105 20102896336006550978469829)
              ·
                refine ⟨3769293063001228308463093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20102896336006550978469829 3769293063001228308463093)
                ·
                  refine ⟨353371224656365153918415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3769293063001228308463093 353371224656365153918415)
                  ·
                    rfl

theorem cell23_6193692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_6193692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193692 prefixEnd_6193692 := by exact prefixLift 6193692
  have htrace : WordTrace (prefixWord ++ tailWord_6193692) baseStart_6193692 baseEnd_6193692 := by
    simpa [prefixWord, tailWord_6193692, baseEnd_6193692] using wordTrace_append hprefix tailTrace_6193692
  have hstable : (prefixWord ++ tailWord_6193692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193692).length < 2 ^ (prefixWord ++ tailWord_6193692).sum := by decide
  have hdescent : baseEnd_6193692 < baseStart_6193692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193703 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6193703 : Nat := 118140960795 + 6193703 * 2 ^ 59
def prefixEnd_6193703 : Nat := 4983230072969 + 3 ^ 40 * 6193703 * 2
def baseEnd_6193703 : Nat := 3180346670194485842228185

theorem tailTrace_6193703 : CollatzResearch.WordTrace tailWord_6193703 prefixEnd_6193703 3180346670194485842228185 := by
  unfold tailWord_6193703
  simp only [CollatzResearch.WordTrace]
  refine ⟨225902907080279306101729763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150601938053519537401153175 225902907080279306101729763)
  ·
    refine ⟨338854360620418959152594645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225902907080279306101729763 338854360620418959152594645)
    ·
      refine ⟨7941899077041069355138937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 338854360620418959152594645 7941899077041069355138937)
      ·
        refine ⟨5956424307780802016354203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7941899077041069355138937 5956424307780802016354203)
        ·
          refine ⟨8934636461671203024531305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956424307780802016354203 8934636461671203024531305)
          ·
            refine ⟨6700977346253402268398479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8934636461671203024531305 6700977346253402268398479)
            ·
              refine ⟨10051466019380103402597719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700977346253402268398479 10051466019380103402597719)
              ·
                refine ⟨15077199029070155103896579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051466019380103402597719 15077199029070155103896579)
                ·
                  refine ⟨22615798543605232655844869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15077199029070155103896579 22615798543605232655844869)
                  ·
                    refine ⟨4240462226925981122970913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22615798543605232655844869 4240462226925981122970913)
                    ·
                      refine ⟨3180346670194485842228185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240462226925981122970913 3180346670194485842228185)
                      ·
                        rfl

theorem cell23_6193703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6193703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193703 prefixEnd_6193703 := by exact prefixLift 6193703
  have htrace : WordTrace (prefixWord ++ tailWord_6193703) baseStart_6193703 baseEnd_6193703 := by
    simpa [prefixWord, tailWord_6193703, baseEnd_6193703] using wordTrace_append hprefix tailTrace_6193703
  have hstable : (prefixWord ++ tailWord_6193703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193703).length < 2 ^ (prefixWord ++ tailWord_6193703).sum := by decide
  have hdescent : baseEnd_6193703 < baseStart_6193703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193742 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_6193742 : Nat := 118140960795 + 6193742 * 2 ^ 59
def prefixEnd_6193742 : Nat := 4983230072969 + 3 ^ 40 * 6193742 * 2
def baseEnd_6193742 : Nat := 3180366695940011189640505

theorem tailTrace_6193742 : CollatzResearch.WordTrace tailWord_6193742 prefixEnd_6193742 3180366695940011189640505 := by
  unfold tailWord_6193742
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238041190892251970299935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150602886351425343841599653 28238041190892251970299935)
  ·
    refine ⟨42357061786338377955449903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28238041190892251970299935 42357061786338377955449903)
    ·
      refine ⟨63535592679507566933174855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42357061786338377955449903 63535592679507566933174855)
      ·
        refine ⟨95303389019261350399762283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63535592679507566933174855 95303389019261350399762283)
        ·
          refine ⟨142955083528892025599643425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95303389019261350399762283 142955083528892025599643425)
          ·
            refine ⟨107216312646669019199732569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142955083528892025599643425 107216312646669019199732569)
            ·
              refine ⟨80412234485001764399799427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107216312646669019199732569 80412234485001764399799427)
              ·
                refine ⟨120618351727502646599699141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80412234485001764399799427 120618351727502646599699141)
                ·
                  refine ⟨22615940948906746237443589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120618351727502646599699141 22615940948906746237443589)
                  ·
                    refine ⟨4240488927920014919520673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22615940948906746237443589 4240488927920014919520673)
                    ·
                      refine ⟨3180366695940011189640505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240488927920014919520673 3180366695940011189640505)
                      ·
                        rfl

theorem cell23_6193742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_6193742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193742 prefixEnd_6193742 := by exact prefixLift 6193742
  have htrace : WordTrace (prefixWord ++ tailWord_6193742) baseStart_6193742 baseEnd_6193742 := by
    simpa [prefixWord, tailWord_6193742, baseEnd_6193742] using wordTrace_append hprefix tailTrace_6193742
  have hstable : (prefixWord ++ tailWord_6193742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193742).length < 2 ^ (prefixWord ++ tailWord_6193742).sum := by decide
  have hdescent : baseEnd_6193742 < baseStart_6193742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193752 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_6193752 : Nat := 118140960795 + 6193752 * 2 ^ 59
def prefixEnd_6193752 : Nat := 4983230072969 + 3 ^ 40 * 6193752 * 2
def baseEnd_6193752 : Nat := 1060123943582185383505153

theorem tailTrace_6193752 : CollatzResearch.WordTrace tailWord_6193752 prefixEnd_6193752 1060123943582185383505153 := by
  unfold tailWord_6193752
  simp only [CollatzResearch.WordTrace]
  refine ⟨112952347128550893735131755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150603129504734524980175673 112952347128550893735131755)
  ·
    refine ⟨169428520692826340602697633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112952347128550893735131755 169428520692826340602697633)
    ·
      refine ⟨127071390519619755452023225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169428520692826340602697633 127071390519619755452023225)
      ·
        refine ⟨95303542889714816589017419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127071390519619755452023225 95303542889714816589017419)
        ·
          refine ⟨142955314334572224883526129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95303542889714816589017419 142955314334572224883526129)
          ·
            refine ⟨107216485750929168662644597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142955314334572224883526129 107216485750929168662644597)
            ·
              refine ⟨10051545539149609562122931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107216485750929168662644597 10051545539149609562122931)
              ·
                refine ⟨15077318308724414343184397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051545539149609562122931 15077318308724414343184397)
                ·
                  refine ⟨5653994365771655378694149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15077318308724414343184397 5653994365771655378694149)
                  ·
                    refine ⟨1060123943582185383505153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653994365771655378694149 1060123943582185383505153)
                    ·
                      rfl

theorem cell23_6193752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_6193752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193752 prefixEnd_6193752 := by exact prefixLift 6193752
  have htrace : WordTrace (prefixWord ++ tailWord_6193752) baseStart_6193752 baseEnd_6193752 := by
    simpa [prefixWord, tailWord_6193752, baseEnd_6193752] using wordTrace_append hprefix tailTrace_6193752
  have hstable : (prefixWord ++ tailWord_6193752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193752).length < 2 ^ (prefixWord ++ tailWord_6193752).sum := by decide
  have hdescent : baseEnd_6193752 < baseStart_6193752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193775 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_6193775 : Nat := 118140960795 + 6193775 * 2 ^ 59
def prefixEnd_6193775 : Nat := 4983230072969 + 3 ^ 40 * 6193775 * 2
def baseEnd_6193775 : Nat := 3180383640801609560527853

theorem tailTrace_6193775 : CollatzResearch.WordTrace tailWord_6193775 prefixEnd_6193775 3180383640801609560527853 := by
  unfold tailWord_6193775
  simp only [CollatzResearch.WordTrace]
  refine ⟨225905533136018462398350779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150603688757345641598900519 225905533136018462398350779)
  ·
    refine ⟨338858299704027693597526169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225905533136018462398350779 338858299704027693597526169)
    ·
      refine ⟨254143724778020770198144627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338858299704027693597526169 254143724778020770198144627)
      ·
        refine ⟨381215587167031155297216941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254143724778020770198144627 381215587167031155297216941)
        ·
          refine ⟨142955845187636683236456353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381215587167031155297216941 142955845187636683236456353)
          ·
            refine ⟨107216883890727512427342265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142955845187636683236456353 107216883890727512427342265)
            ·
              refine ⟨80412662918045634320506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107216883890727512427342265 80412662918045634320506699)
              ·
                refine ⟨120618994377068451480760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80412662918045634320506699 120618994377068451480760049)
                ·
                  refine ⟨90464245782801338610570037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120618994377068451480760049 90464245782801338610570037)
                  ·
                    refine ⟨8481023042137625494740941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90464245782801338610570037 8481023042137625494740941)
                    ·
                      refine ⟨3180383640801609560527853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8481023042137625494740941 3180383640801609560527853)
                      ·
                        rfl

theorem cell23_6193775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_6193775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193775 prefixEnd_6193775 := by exact prefixLift 6193775
  have htrace : WordTrace (prefixWord ++ tailWord_6193775) baseStart_6193775 baseEnd_6193775 := by
    simpa [prefixWord, tailWord_6193775, baseEnd_6193775] using wordTrace_append hprefix tailTrace_6193775
  have hstable : (prefixWord ++ tailWord_6193775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193775).length < 2 ^ (prefixWord ++ tailWord_6193775).sum := by decide
  have hdescent : baseEnd_6193775 < baseStart_6193775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193822 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6193822 : Nat := 118140960795 + 6193822 * 2 ^ 59
def prefixEnd_6193822 : Nat := 4983230072969 + 3 ^ 40 * 6193822 * 2
def baseEnd_6193822 : Nat := 3180407774392370876640137

theorem tailTrace_6193822 : CollatzResearch.WordTrace tailWord_6193822 prefixEnd_6193822 3180407774392370876640137 := by
  unfold tailWord_6193822
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238405920856023678163965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150604831577898792950207813 28238405920856023678163965)
  ·
    refine ⟨10589402220321008879311487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28238405920856023678163965 10589402220321008879311487)
    ·
      refine ⟨15884103330481513318967231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10589402220321008879311487 15884103330481513318967231)
      ·
        refine ⟨23826154995722269978450847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15884103330481513318967231 23826154995722269978450847)
        ·
          refine ⟨35739232493583404967676271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23826154995722269978450847 35739232493583404967676271)
          ·
            refine ⟨53608848740375107451514407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35739232493583404967676271 53608848740375107451514407)
            ·
              refine ⟨80413273110562661177271611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53608848740375107451514407 80413273110562661177271611)
              ·
                refine ⟨120619909665843991765907417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80413273110562661177271611 120619909665843991765907417)
                ·
                  refine ⟨90464932249382993824430563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120619909665843991765907417 90464932249382993824430563)
                  ·
                    refine ⟨135697398374074490736645845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90464932249382993824430563 135697398374074490736645845)
                    ·
                      refine ⟨3180407774392370876640137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135697398374074490736645845 3180407774392370876640137)
                      ·
                        rfl

theorem cell23_6193822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6193822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193822 prefixEnd_6193822 := by exact prefixLift 6193822
  have htrace : WordTrace (prefixWord ++ tailWord_6193822) baseStart_6193822 baseEnd_6193822 := by
    simpa [prefixWord, tailWord_6193822, baseEnd_6193822] using wordTrace_append hprefix tailTrace_6193822
  have hstable : (prefixWord ++ tailWord_6193822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193822).length < 2 ^ (prefixWord ++ tailWord_6193822).sum := by decide
  have hdescent : baseEnd_6193822 < baseStart_6193822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193842 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_6193842 : Nat := 118140960795 + 6193842 * 2 ^ 59
def prefixEnd_6193842 : Nat := 4983230072969 + 3 ^ 40 * 6193842 * 2
def baseEnd_6193842 : Nat := 1060139348001820266130015

theorem tailTrace_6193842 : CollatzResearch.WordTrace tailWord_6193842 prefixEnd_6193842 1060139348001820266130015 := by
  unfold tailWord_6193842
  simp only [CollatzResearch.WordTrace]
  refine ⟨56476994206693933210259945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150605317884517155227359853 56476994206693933210259945)
  ·
    refine ⟨42357745655020449907694959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56476994206693933210259945 42357745655020449907694959)
    ·
      refine ⟨63536618482530674861542439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42357745655020449907694959 63536618482530674861542439)
      ·
        refine ⟨95304927723796012292313659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63536618482530674861542439 95304927723796012292313659)
        ·
          refine ⟨142957391585694018438470489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95304927723796012292313659 142957391585694018438470489)
          ·
            refine ⟨107218043689270513828852867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142957391585694018438470489 107218043689270513828852867)
            ·
              refine ⟨160827065533905770743279301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107218043689270513828852867 160827065533905770743279301)
              ·
                refine ⟨30155074787607332014364869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160827065533905770743279301 30155074787607332014364869)
                ·
                  refine ⟨5654076522676374752693413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30155074787607332014364869 5654076522676374752693413)
                  ·
                    refine ⟨1060139348001820266130015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5654076522676374752693413 1060139348001820266130015)
                    ·
                      rfl

theorem cell23_6193842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_6193842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193842 prefixEnd_6193842 := by exact prefixLift 6193842
  have htrace : WordTrace (prefixWord ++ tailWord_6193842) baseStart_6193842 baseEnd_6193842 := by
    simpa [prefixWord, tailWord_6193842, baseEnd_6193842] using wordTrace_append hprefix tailTrace_6193842
  have hstable : (prefixWord ++ tailWord_6193842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193842).length < 2 ^ (prefixWord ++ tailWord_6193842).sum := by decide
  have hdescent : baseEnd_6193842 < baseStart_6193842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193849 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6193849 : Nat := 118140960795 + 6193849 * 2 ^ 59
def prefixEnd_6193849 : Nat := 4983230072969 + 3 ^ 40 * 6193849 * 2
def baseEnd_6193849 : Nat := 3180421638370042271002513

theorem tailTrace_6193849 : CollatzResearch.WordTrace tailWord_6193849 prefixEnd_6193849 3180421638370042271002513 := by
  unfold tailWord_6193849
  simp only [CollatzResearch.WordTrace]
  refine ⟨225908232137750373036544601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150605488091833582024363067 225908232137750373036544601)
  ·
    refine ⟨169431174103312779777408451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225908232137750373036544601 169431174103312779777408451)
    ·
      refine ⟨254146761154969169666112677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169431174103312779777408451 254146761154969169666112677)
      ·
        refine ⟨47652517716556719312396127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254146761154969169666112677 47652517716556719312396127)
        ·
          refine ⟨71478776574835078968594191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47652517716556719312396127 71478776574835078968594191)
          ·
            refine ⟨107218164862252618452891287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71478776574835078968594191 107218164862252618452891287)
            ·
              refine ⟨160827247293378927679336931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107218164862252618452891287 160827247293378927679336931)
              ·
                refine ⟨241240870940068391519005397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160827247293378927679336931 241240870940068391519005397)
                ·
                  refine ⟨5654082912657852926226689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241240870940068391519005397 5654082912657852926226689)
                  ·
                    refine ⟨4240562184493389694670017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654082912657852926226689 4240562184493389694670017)
                    ·
                      refine ⟨3180421638370042271002513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240562184493389694670017 3180421638370042271002513)
                      ·
                        rfl

theorem cell23_6193849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6193849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193849 prefixEnd_6193849 := by exact prefixLift 6193849
  have htrace : WordTrace (prefixWord ++ tailWord_6193849) baseStart_6193849 baseEnd_6193849 := by
    simpa [prefixWord, tailWord_6193849, baseEnd_6193849] using wordTrace_append hprefix tailTrace_6193849
  have hstable : (prefixWord ++ tailWord_6193849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193849).length < 2 ^ (prefixWord ++ tailWord_6193849).sum := by decide
  have hdescent : baseEnd_6193849 < baseStart_6193849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193852 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6193852 : Nat := 118140960795 + 6193852 * 2 ^ 59
def prefixEnd_6193852 : Nat := 4983230072969 + 3 ^ 40 * 6193852 * 2
def baseEnd_6193852 : Nat := 3180423178812005759264999

theorem tailTrace_6193852 : CollatzResearch.WordTrace tailWord_6193852 prefixEnd_6193852 3180423178812005759264999 := by
  unfold tailWord_6193852
  simp only [CollatzResearch.WordTrace]
  refine ⟨112954170778369752274451905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150605561037826336365935873 112954170778369752274451905)
  ·
    refine ⟨84715628083777314205838929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112954170778369752274451905 84715628083777314205838929)
    ·
      refine ⟨63536721062832985654379197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84715628083777314205838929 63536721062832985654379197)
      ·
        refine ⟨23826270398562369620392199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63536721062832985654379197 23826270398562369620392199)
        ·
          refine ⟨35739405597843554430588299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23826270398562369620392199 35739405597843554430588299)
          ·
            refine ⟨53609108396765331645882449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35739405597843554430588299 53609108396765331645882449)
            ·
              refine ⟨40206831297573998734411837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53609108396765331645882449 40206831297573998734411837)
              ·
                refine ⟨15077561736590249525404439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40206831297573998734411837 15077561736590249525404439)
                ·
                  refine ⟨22616342604885374288106659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15077561736590249525404439 22616342604885374288106659)
                  ·
                    refine ⟨33924513907328061432159989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22616342604885374288106659 33924513907328061432159989)
                    ·
                      refine ⟨3180423178812005759264999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33924513907328061432159989 3180423178812005759264999)
                      ·
                        rfl

theorem cell23_6193852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6193852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193852 prefixEnd_6193852 := by exact prefixLift 6193852
  have htrace : WordTrace (prefixWord ++ tailWord_6193852) baseStart_6193852 baseEnd_6193852 := by
    simpa [prefixWord, tailWord_6193852, baseEnd_6193852] using wordTrace_append hprefix tailTrace_6193852
  have hstable : (prefixWord ++ tailWord_6193852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193852).length < 2 ^ (prefixWord ++ tailWord_6193852).sum := by decide
  have hdescent : baseEnd_6193852 < baseStart_6193852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193855 : List Nat := [1, 1, 2, 2, 2, 5, 10]
def baseStart_6193855 : Nat := 118140960795 + 6193855 * 2 ^ 59
def prefixEnd_6193855 : Nat := 4983230072969 + 3 ^ 40 * 6193855 * 2
def baseEnd_6193855 : Nat := 39264502706839126512685

theorem tailTrace_6193855 : CollatzResearch.WordTrace tailWord_6193855 prefixEnd_6193855 39264502706839126512685 := by
  unfold tailWord_6193855
  simp only [CollatzResearch.WordTrace]
  refine ⟨225908450975728636061263019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150605633983819090707508679 225908450975728636061263019)
  ·
    refine ⟨338862676463592954091894529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225908450975728636061263019 338862676463592954091894529)
    ·
      refine ⟨254147007347694715568920897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338862676463592954091894529 254147007347694715568920897)
      ·
        refine ⟨190610255510771036676690673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254147007347694715568920897 190610255510771036676690673)
        ·
          refine ⟨142957691633078277507518005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190610255510771036676690673 142957691633078277507518005)
          ·
            refine ⟨13402283590601088516329813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142957691633078277507518005 13402283590601088516329813)
            ·
              refine ⟨39264502706839126512685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13402283590601088516329813 39264502706839126512685)
              ·
                rfl

theorem cell23_6193855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 10].length) (baseStart_6193855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193855 prefixEnd_6193855 := by exact prefixLift 6193855
  have htrace : WordTrace (prefixWord ++ tailWord_6193855) baseStart_6193855 baseEnd_6193855 := by
    simpa [prefixWord, tailWord_6193855, baseEnd_6193855] using wordTrace_append hprefix tailTrace_6193855
  have hstable : (prefixWord ++ tailWord_6193855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193855).length < 2 ^ (prefixWord ++ tailWord_6193855).sum := by decide
  have hdescent : baseEnd_6193855 < baseStart_6193855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193866 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_6193866 : Nat := 118140960795 + 6193866 * 2 ^ 59
def prefixEnd_6193866 : Nat := 4983230072969 + 3 ^ 40 * 6193866 * 2
def baseEnd_6193866 : Nat := 3180430367541168704489935

theorem tailTrace_6193866 : CollatzResearch.WordTrace tailWord_6193866 prefixEnd_6193866 3180430367541168704489935 := by
  unfold tailWord_6193866
  simp only [CollatzResearch.WordTrace]
  refine ⟨56477213044672196234978363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150605901452459189959942301 56477213044672196234978363)
  ·
    refine ⟨84715819567008294352467545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56477213044672196234978363 84715819567008294352467545)
    ·
      refine ⟨63536864675256220764350659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84715819567008294352467545 63536864675256220764350659)
      ·
        refine ⟨95305297012884331146525989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63536864675256220764350659 95305297012884331146525989)
        ·
          refine ⟨17869743189915812089973623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95305297012884331146525989 17869743189915812089973623)
          ·
            refine ⟨26804614784873718134960435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17869743189915812089973623 26804614784873718134960435)
            ·
              refine ⟨40206922177310577202440653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26804614784873718134960435 40206922177310577202440653)
              ·
                refine ⟨15077595816491466450915245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40206922177310577202440653 15077595816491466450915245)
                ·
                  refine ⟨5654098431184299919093217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15077595816491466450915245 5654098431184299919093217)
                  ·
                    refine ⟨4240573823388224939319913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654098431184299919093217 4240573823388224939319913)
                    ·
                      refine ⟨3180430367541168704489935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240573823388224939319913 3180430367541168704489935)
                      ·
                        rfl

theorem cell23_6193866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_6193866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193866 prefixEnd_6193866 := by exact prefixLift 6193866
  have htrace : WordTrace (prefixWord ++ tailWord_6193866) baseStart_6193866 baseEnd_6193866 := by
    simpa [prefixWord, tailWord_6193866, baseEnd_6193866] using wordTrace_append hprefix tailTrace_6193866
  have hstable : (prefixWord ++ tailWord_6193866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193866).length < 2 ^ (prefixWord ++ tailWord_6193866).sum := by decide
  have hdescent : baseEnd_6193866 < baseStart_6193866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193876 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_6193876 : Nat := 118140960795 + 6193876 * 2 ^ 59
def prefixEnd_6193876 : Nat := 4983230072969 + 3 ^ 40 * 6193876 * 2
def baseEnd_6193876 : Nat := 1060145167449237888454963

theorem tailTrace_6193876 : CollatzResearch.WordTrace tailWord_6193876 prefixEnd_6193876 1060145167449237888454963 := by
  unfold tailWord_6193876
  simp only [CollatzResearch.WordTrace]
  refine ⟨112954608454326278323888741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150606144605768371098518321 112954608454326278323888741)
  ·
    refine ⟨21178989085186177185729139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112954608454326278323888741 21178989085186177185729139)
    ·
      refine ⟨31768483627779265778593709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21178989085186177185729139 31768483627779265778593709)
      ·
        refine ⟨11913181360417224666972641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31768483627779265778593709 11913181360417224666972641)
        ·
          refine ⟨8934886020312918500229481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11913181360417224666972641 8934886020312918500229481)
          ·
            refine ⟨6701164515234688875172111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8934886020312918500229481 6701164515234688875172111)
            ·
              refine ⟨10051746772852033312758167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701164515234688875172111 10051746772852033312758167)
              ·
                refine ⟨15077620159278049969137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051746772852033312758167 15077620159278049969137251)
                ·
                  refine ⟨22616430238917074953705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15077620159278049969137251 22616430238917074953705877)
                  ·
                    refine ⟨1060145167449237888454963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22616430238917074953705877 1060145167449237888454963)
                    ·
                      rfl

theorem cell23_6193876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_6193876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193876 prefixEnd_6193876 := by exact prefixLift 6193876
  have htrace : WordTrace (prefixWord ++ tailWord_6193876) baseStart_6193876 baseEnd_6193876 := by
    simpa [prefixWord, tailWord_6193876, baseEnd_6193876] using wordTrace_append hprefix tailTrace_6193876
  have hstable : (prefixWord ++ tailWord_6193876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193876).length < 2 ^ (prefixWord ++ tailWord_6193876).sum := by decide
  have hdescent : baseEnd_6193876 < baseStart_6193876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193879 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_6193879 : Nat := 118140960795 + 6193879 * 2 ^ 59
def prefixEnd_6193879 : Nat := 4983230072969 + 3 ^ 40 * 6193879 * 2
def baseEnd_6193879 : Nat := 3180437042789677153627375

theorem tailTrace_6193879 : CollatzResearch.WordTrace tailWord_6193879 prefixEnd_6193879 3180437042789677153627375 := by
  unfold tailWord_6193879
  simp only [CollatzResearch.WordTrace]
  refine ⟨225909326327641688160136691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150606217551761125440091127 225909326327641688160136691)
  ·
    refine ⟨338863989491462532240205037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225909326327641688160136691 338863989491462532240205037)
    ·
      refine ⟨127073996059298449590076889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338863989491462532240205037 127073996059298449590076889)
      ·
        refine ⟨95305497044473837192557667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127073996059298449590076889 95305497044473837192557667)
        ·
          refine ⟨142958245566710755788836501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95305497044473837192557667 142958245566710755788836501)
          ·
            refine ⟨6701167760939566677601711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142958245566710755788836501 6701167760939566677601711)
            ·
              refine ⟨10051751641409350016402567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701167760939566677601711 10051751641409350016402567)
              ·
                refine ⟨15077627462114025024603851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051751641409350016402567 15077627462114025024603851)
                ·
                  refine ⟨22616441193171037536905777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15077627462114025024603851 22616441193171037536905777)
                  ·
                    refine ⟨16962330894878278152679333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22616441193171037536905777 16962330894878278152679333)
                    ·
                      refine ⟨3180437042789677153627375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16962330894878278152679333 3180437042789677153627375)
                      ·
                        rfl

theorem cell23_6193879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_6193879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193879 prefixEnd_6193879 := by exact prefixLift 6193879
  have htrace : WordTrace (prefixWord ++ tailWord_6193879) baseStart_6193879 baseEnd_6193879 := by
    simpa [prefixWord, tailWord_6193879, baseEnd_6193879] using wordTrace_append hprefix tailTrace_6193879
  have hstable : (prefixWord ++ tailWord_6193879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193879).length < 2 ^ (prefixWord ++ tailWord_6193879).sum := by decide
  have hdescent : baseEnd_6193879 < baseStart_6193879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193889 : List Nat := [1, 2, 3, 1, 4, 3, 2, 7]
def baseStart_6193889 : Nat := 118140960795 + 6193889 * 2 ^ 59
def prefixEnd_6193889 : Nat := 4983230072969 + 3 ^ 40 * 6193889 * 2
def baseEnd_6193889 : Nat := 117794154725786004240827

theorem tailTrace_6193889 : CollatzResearch.WordTrace tailWord_6193889 prefixEnd_6193889 117794154725786004240827 := by
  unfold tailWord_6193889
  simp only [CollatzResearch.WordTrace]
  refine ⟨225909691057605459868000721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150606460705070306578667147 225909691057605459868000721)
  ·
    refine ⟨169432268293204094901000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225909691057605459868000721 169432268293204094901000541)
    ·
      refine ⟨63537100609951535587875203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169432268293204094901000541 63537100609951535587875203)
      ·
        refine ⟨95305650914927303381812805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63537100609951535587875203 95305650914927303381812805)
        ·
          refine ⟨17869809546548869384089901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95305650914927303381812805 17869809546548869384089901)
          ·
            refine ⟨6701178579955826019033713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17869809546548869384089901 6701178579955826019033713)
            ·
              refine ⟨5025883934966869514275285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6701178579955826019033713 5025883934966869514275285)
              ·
                refine ⟨117794154725786004240827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5025883934966869514275285 117794154725786004240827)
                ·
                  rfl

theorem cell23_6193889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 7].length) (baseStart_6193889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193889 prefixEnd_6193889 := by exact prefixLift 6193889
  have htrace : WordTrace (prefixWord ++ tailWord_6193889) baseStart_6193889 baseEnd_6193889 := by
    simpa [prefixWord, tailWord_6193889, baseEnd_6193889] using wordTrace_append hprefix tailTrace_6193889
  have hstable : (prefixWord ++ tailWord_6193889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193889).length < 2 ^ (prefixWord ++ tailWord_6193889).sum := by decide
  have hdescent : baseEnd_6193889 < baseStart_6193889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193939 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 4, 2]
def baseStart_6193939 : Nat := 118140960795 + 6193939 * 2 ^ 59
def prefixEnd_6193939 : Nat := 4983230072969 + 3 ^ 40 * 6193939 * 2
def baseEnd_6193939 : Nat := 3180467851628946918877099

theorem tailTrace_6193939 : CollatzResearch.WordTrace tailWord_6193939 prefixEnd_6193939 3180467851628946918877099 := by
  unfold tailWord_6193939
  simp only [CollatzResearch.WordTrace]
  refine ⟨225911514707424318407320871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150607676471616212271547247 225911514707424318407320871)
  ·
    refine ⟨338867272061136477610981307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225911514707424318407320871 338867272061136477610981307)
    ·
      refine ⟨508300908091704716416471961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338867272061136477610981307 508300908091704716416471961)
      ·
        refine ⟨381225681068778537312353971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508300908091704716416471961 381225681068778537312353971)
        ·
          refine ⟨571838521603167805968530957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381225681068778537312353971 571838521603167805968530957)
          ·
            refine ⟨214439445601187927238199109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571838521603167805968530957 214439445601187927238199109)
            ·
              refine ⟨40207396050222736357162333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214439445601187927238199109 40207396050222736357162333)
              ·
                refine ⟨15077773518833526133935875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40207396050222736357162333 15077773518833526133935875)
                ·
                  refine ⟨22616660278250289200903813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15077773518833526133935875 22616660278250289200903813)
                  ·
                    refine ⟨4240623802171929225169465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22616660278250289200903813 4240623802171929225169465)
                    ·
                      refine ⟨3180467851628946918877099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240623802171929225169465 3180467851628946918877099)
                      ·
                        rfl

theorem cell23_6193939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4, 2].length) (baseStart_6193939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193939 prefixEnd_6193939 := by exact prefixLift 6193939
  have htrace : WordTrace (prefixWord ++ tailWord_6193939) baseStart_6193939 baseEnd_6193939 := by
    simpa [prefixWord, tailWord_6193939, baseEnd_6193939] using wordTrace_append hprefix tailTrace_6193939
  have hstable : (prefixWord ++ tailWord_6193939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193939).length < 2 ^ (prefixWord ++ tailWord_6193939).sum := by decide
  have hdescent : baseEnd_6193939 < baseStart_6193939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193973 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_6193973 : Nat := 118140960795 + 6193973 * 2 ^ 59
def prefixEnd_6193973 : Nat := 4983230072969 + 3 ^ 40 * 6193973 * 2
def baseEnd_6193973 : Nat := 3180485309971199785851943

theorem tailTrace_6193973 : CollatzResearch.WordTrace tailWord_6193973 prefixEnd_6193973 3180485309971199785851943 := by
  unfold tailWord_6193973
  simp only [CollatzResearch.WordTrace]
  refine ⟨225912754789301142214058573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150608503192867428142705715 225912754789301142214058573)
  ·
    refine ⟨84717283045987928330271965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225912754789301142214058573 84717283045987928330271965)
    ·
      refine ⟨31768981142245473123851987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84717283045987928330271965 31768981142245473123851987)
      ·
        refine ⟨47653471713368209685777981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31768981142245473123851987 47653471713368209685777981)
        ·
          refine ⟨17870051892513078632166743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47653471713368209685777981 17870051892513078632166743)
          ·
            refine ⟨26805077838769617948250115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17870051892513078632166743 26805077838769617948250115)
            ·
              refine ⟨40207616758154426922375173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26805077838769617948250115 40207616758154426922375173)
              ·
                refine ⟨7538928142153955047945345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40207616758154426922375173 7538928142153955047945345)
                ·
                  refine ⟨5654196106615466285959009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7538928142153955047945345 5654196106615466285959009)
                  ·
                    refine ⟨4240647079961599714469257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654196106615466285959009 4240647079961599714469257)
                    ·
                      refine ⟨3180485309971199785851943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240647079961599714469257 3180485309971199785851943)
                      ·
                        rfl

theorem cell23_6193973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_6193973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193973 prefixEnd_6193973 := by exact prefixLift 6193973
  have htrace : WordTrace (prefixWord ++ tailWord_6193973) baseStart_6193973 baseEnd_6193973 := by
    simpa [prefixWord, tailWord_6193973, baseEnd_6193973] using wordTrace_append hprefix tailTrace_6193973
  have hstable : (prefixWord ++ tailWord_6193973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193973).length < 2 ^ (prefixWord ++ tailWord_6193973).sum := by decide
  have hdescent : baseEnd_6193973 < baseStart_6193973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6193992 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6193992 : Nat := 118140960795 + 6193992 * 2 ^ 59
def prefixEnd_6193992 : Nat := 4983230072969 + 3 ^ 40 * 6193992 * 2
def baseEnd_6193992 : Nat := 1060165022034545070504785

theorem tailTrace_6193992 : CollatzResearch.WordTrace tailWord_6193992 prefixEnd_6193992 1060165022034545070504785 := by
  unfold tailWord_6193992
  simp only [CollatzResearch.WordTrace]
  refine ⟨112956723888116154229500115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150608965184154872306000153 112956723888116154229500115)
  ·
    refine ⟨169435085832174231344250173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112956723888116154229500115 169435085832174231344250173)
    ·
      refine ⟨63538157187065336754093815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169435085832174231344250173 63538157187065336754093815)
      ·
        refine ⟨95307235780598005131140723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63538157187065336754093815 95307235780598005131140723)
        ·
          refine ⟨142960853670897007696711085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95307235780598005131140723 142960853670897007696711085)
          ·
            refine ⟨53610320126586377886266657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142960853670897007696711085 53610320126586377886266657)
            ·
              refine ⟨40207740094939783414699993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53610320126586377886266657 40207740094939783414699993)
              ·
                refine ⟨30155805071204837561024995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40207740094939783414699993 30155805071204837561024995)
                ·
                  refine ⟨45233707606807256341537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30155805071204837561024995 45233707606807256341537493)
                  ·
                    refine ⟨1060165022034545070504785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45233707606807256341537493 1060165022034545070504785)
                    ·
                      rfl

theorem cell23_6193992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6193992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6193992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6193992 prefixEnd_6193992 := by exact prefixLift 6193992
  have htrace : WordTrace (prefixWord ++ tailWord_6193992) baseStart_6193992 baseEnd_6193992 := by
    simpa [prefixWord, tailWord_6193992, baseEnd_6193992] using wordTrace_append hprefix tailTrace_6193992
  have hstable : (prefixWord ++ tailWord_6193992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6193992).length < 2 ^ (prefixWord ++ tailWord_6193992).sum := by decide
  have hdescent : baseEnd_6193992 < baseStart_6193992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6193992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194009 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_6194009 : Nat := 118140960795 + 6194009 * 2 ^ 59
def prefixEnd_6194009 : Nat := 4983230072969 + 3 ^ 40 * 6194009 * 2
def baseEnd_6194009 : Nat := 1060167931758253881667259

theorem tailTrace_6194009 : CollatzResearch.WordTrace tailWord_6194009 prefixEnd_6194009 1060167931758253881667259 := by
  unfold tailWord_6194009
  simp only [CollatzResearch.WordTrace]
  refine ⟨225914067817170720362369081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150609378544780480241579387 225914067817170720362369081)
  ·
    refine ⟨169435550862878040271776811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225914067817170720362369081 169435550862878040271776811)
    ·
      refine ⟨254153326294317060407665217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169435550862878040271776811 254153326294317060407665217)
      ·
        refine ⟨190614994720737795305748913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254153326294317060407665217 190614994720737795305748913)
        ·
          refine ⟨142961246040553346479311685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190614994720737795305748913 142961246040553346479311685)
          ·
            refine ⟨26805233632603752464870941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142961246040553346479311685 26805233632603752464870941)
            ·
              refine ⟨10051962612226407174326603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26805233632603752464870941 10051962612226407174326603)
              ·
                refine ⟨15077943918339610761489905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051962612226407174326603 15077943918339610761489905)
                ·
                  refine ⟨11308457938754708071117429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15077943918339610761489905 11308457938754708071117429)
                  ·
                    refine ⟨1060167931758253881667259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11308457938754708071117429 1060167931758253881667259)
                    ·
                      rfl

theorem cell23_6194009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_6194009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194009 prefixEnd_6194009 := by exact prefixLift 6194009
  have htrace : WordTrace (prefixWord ++ tailWord_6194009) baseStart_6194009 baseEnd_6194009 := by
    simpa [prefixWord, tailWord_6194009, baseEnd_6194009] using wordTrace_append hprefix tailTrace_6194009
  have hstable : (prefixWord ++ tailWord_6194009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194009).length < 2 ^ (prefixWord ++ tailWord_6194009).sum := by decide
  have hdescent : baseEnd_6194009 < baseStart_6194009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194029 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6194029 : Nat := 118140960795 + 6194029 * 2 ^ 59
def prefixEnd_6194029 : Nat := 4983230072969 + 3 ^ 40 * 6194029 * 2
def baseEnd_6194029 : Nat := 3180514064887851566751685

theorem tailTrace_6194029 : CollatzResearch.WordTrace tailWord_6194029 prefixEnd_6194029 3180514064887851566751685 := by
  unfold tailWord_6194029
  simp only [CollatzResearch.WordTrace]
  refine ⟨225914797277098263778097141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150609864851398842518731427 225914797277098263778097141)
  ·
    refine ⟨21179512244727962229196607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225914797277098263778097141 21179512244727962229196607)
    ·
      refine ⟨31769268367091943343794911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21179512244727962229196607 31769268367091943343794911)
      ·
        refine ⟨47653902550637915015692367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31769268367091943343794911 47653902550637915015692367)
        ·
          refine ⟨71480853825956872523538551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47653902550637915015692367 71480853825956872523538551)
          ·
            refine ⟨107221280738935308785307827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71480853825956872523538551 107221280738935308785307827)
            ·
              refine ⟨160831921108402963177961741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107221280738935308785307827 160831921108402963177961741)
              ·
                refine ⟨60311970415651111191735653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160831921108402963177961741 60311970415651111191735653)
                ·
                  refine ⟨11308494452934583348450435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60311970415651111191735653 11308494452934583348450435)
                  ·
                    refine ⟨16962741679401875022675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11308494452934583348450435 16962741679401875022675653)
                    ·
                      refine ⟨3180514064887851566751685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16962741679401875022675653 3180514064887851566751685)
                      ·
                        rfl

theorem cell23_6194029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6194029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194029 prefixEnd_6194029 := by exact prefixLift 6194029
  have htrace : WordTrace (prefixWord ++ tailWord_6194029) baseStart_6194029 baseEnd_6194029 := by
    simpa [prefixWord, tailWord_6194029, baseEnd_6194029] using wordTrace_append hprefix tailTrace_6194029
  have hstable : (prefixWord ++ tailWord_6194029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194029).length < 2 ^ (prefixWord ++ tailWord_6194029).sum := by decide
  have hdescent : baseEnd_6194029 < baseStart_6194029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194032 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_6194032 : Nat := 118140960795 + 6194032 * 2 ^ 59
def prefixEnd_6194032 : Nat := 4983230072969 + 3 ^ 40 * 6194032 * 2
def baseEnd_6194032 : Nat := 3180515605329815055014171

theorem tailTrace_6194032 : CollatzResearch.WordTrace tailWord_6194032 prefixEnd_6194032 3180515605329815055014171 := by
  unfold tailWord_6194032
  simp only [CollatzResearch.WordTrace]
  refine ⟨112957453348043697645228175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150609937797391596860304233 112957453348043697645228175)
  ·
    refine ⟨169436180022065546467842263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112957453348043697645228175 169436180022065546467842263)
    ·
      refine ⟨254154270033098319701763395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169436180022065546467842263 254154270033098319701763395)
      ·
        refine ⟨381231405049647479552645093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254154270033098319701763395 381231405049647479552645093)
        ·
          refine ⟨71480888446808902416120955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381231405049647479552645093 71480888446808902416120955)
          ·
            refine ⟨107221332670213353624181433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71480888446808902416120955 107221332670213353624181433)
            ·
              refine ⟨80415999502660015218136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107221332670213353624181433 80415999502660015218136075)
              ·
                refine ⟨120623999253990022827204113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80415999502660015218136075 120623999253990022827204113)
                ·
                  refine ⟨90467999440492517120403085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120623999253990022827204113 90467999440492517120403085)
                  ·
                    refine ⟨33925499790184693920151157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90467999440492517120403085 33925499790184693920151157)
                    ·
                      refine ⟨3180515605329815055014171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33925499790184693920151157 3180515605329815055014171)
                      ·
                        rfl

theorem cell23_6194032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_6194032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194032 prefixEnd_6194032 := by exact prefixLift 6194032
  have htrace : WordTrace (prefixWord ++ tailWord_6194032) baseStart_6194032 baseEnd_6194032 := by
    simpa [prefixWord, tailWord_6194032, baseEnd_6194032] using wordTrace_append hprefix tailTrace_6194032
  have hstable : (prefixWord ++ tailWord_6194032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194032).length < 2 ^ (prefixWord ++ tailWord_6194032).sum := by decide
  have hdescent : baseEnd_6194032 < baseStart_6194032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194042 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_6194042 : Nat := 118140960795 + 6194042 * 2 ^ 59
def prefixEnd_6194042 : Nat := 4983230072969 + 3 ^ 40 * 6194042 * 2
def baseEnd_6194042 : Nat := 3180520740136360015889125

theorem tailTrace_6194042 : CollatzResearch.WordTrace tailWord_6194042 prefixEnd_6194042 3180520740136360015889125 := by
  unfold tailWord_6194042
  simp only [CollatzResearch.WordTrace]
  refine ⟨56478817856512791749580095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150610180950700777998880253 56478817856512791749580095)
  ·
    refine ⟨84718226784769187624370143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56478817856512791749580095 84718226784769187624370143)
    ·
      refine ⟨127077340177153781436555215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84718226784769187624370143 127077340177153781436555215)
      ·
        refine ⟨190616010265730672154832823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127077340177153781436555215 190616010265730672154832823)
        ·
          refine ⟨285924015398596008232249235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190616010265730672154832823 285924015398596008232249235)
          ·
            refine ⟨428886023097894012348373853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285924015398596008232249235 428886023097894012348373853)
            ·
              refine ⟨160832258661710254630640195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428886023097894012348373853 160832258661710254630640195)
              ·
                refine ⟨241248387992565381945960293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160832258661710254630640195 241248387992565381945960293)
                ·
                  refine ⟨45234072748606009114867555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241248387992565381945960293 45234072748606009114867555)
                  ·
                    refine ⟨67851109122909013672301333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45234072748606009114867555 67851109122909013672301333)
                    ·
                      refine ⟨3180520740136360015889125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67851109122909013672301333 3180520740136360015889125)
                      ·
                        rfl

theorem cell23_6194042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_6194042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194042 prefixEnd_6194042 := by exact prefixLift 6194042
  have htrace : WordTrace (prefixWord ++ tailWord_6194042) baseStart_6194042 baseEnd_6194042 := by
    simpa [prefixWord, tailWord_6194042, baseEnd_6194042] using wordTrace_append hprefix tailTrace_6194042
  have hstable : (prefixWord ++ tailWord_6194042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194042).length < 2 ^ (prefixWord ++ tailWord_6194042).sum := by decide
  have hdescent : baseEnd_6194042 < baseStart_6194042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194056 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_6194056 : Nat := 118140960795 + 6194056 * 2 ^ 59
def prefixEnd_6194056 : Nat := 4983230072969 + 3 ^ 40 * 6194056 * 2
def baseEnd_6194056 : Nat := 1060175976288507653704687

theorem tailTrace_6194056 : CollatzResearch.WordTrace tailWord_6194056 prefixEnd_6194056 1060175976288507653704687 := by
  unfold tailWord_6194056
  simp only [CollatzResearch.WordTrace]
  refine ⟨112957891024000223694665011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150610521365333631592886681 112957891024000223694665011)
  ·
    refine ⟨169436836536000335541997517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112957891024000223694665011 169436836536000335541997517)
    ·
      refine ⟨63538813701000125828249069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169436836536000335541997517 63538813701000125828249069)
      ·
        refine ⟨23827055137875047185593401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63538813701000125828249069 23827055137875047185593401)
        ·
          refine ⟨17870291353406285389195051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23827055137875047185593401 17870291353406285389195051)
          ·
            refine ⟨26805437030109428083792577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17870291353406285389195051 26805437030109428083792577)
            ·
              refine ⟨20104077772582071062844433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26805437030109428083792577 20104077772582071062844433)
              ·
                refine ⟨15078058329436553297133325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20104077772582071062844433 15078058329436553297133325)
                ·
                  refine ⟨5654271873538707486424997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15078058329436553297133325 5654271873538707486424997)
                  ·
                    refine ⟨1060175976288507653704687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5654271873538707486424997 1060175976288507653704687)
                    ·
                      rfl

theorem cell23_6194056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_6194056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194056 prefixEnd_6194056 := by exact prefixLift 6194056
  have htrace : WordTrace (prefixWord ++ tailWord_6194056) baseStart_6194056 baseEnd_6194056 := by
    simpa [prefixWord, tailWord_6194056, baseEnd_6194056] using wordTrace_append hprefix tailTrace_6194056
  have hstable : (prefixWord ++ tailWord_6194056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194056).length < 2 ^ (prefixWord ++ tailWord_6194056).sum := by decide
  have hdescent : baseEnd_6194056 < baseStart_6194056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194106 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_6194106 : Nat := 118140960795 + 6194106 * 2 ^ 59
def prefixEnd_6194106 : Nat := 4983230072969 + 3 ^ 40 * 6194106 * 2
def baseEnd_6194106 : Nat := 3180553602898247765488831

theorem tailTrace_6194106 : CollatzResearch.WordTrace tailWord_6194106 prefixEnd_6194106 3180553602898247765488831 := by
  unfold tailWord_6194106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56479401424454826482162543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150611737131879537285766781 56479401424454826482162543)
  ·
    refine ⟨84719102136682239723243815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56479401424454826482162543 84719102136682239723243815)
    ·
      refine ⟨127078653205023359584865723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84719102136682239723243815 127078653205023359584865723)
      ·
        refine ⟨190617979807535039377298585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127078653205023359584865723 190617979807535039377298585)
        ·
          refine ⟨142963484855651279532973939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190617979807535039377298585 142963484855651279532973939)
          ·
            refine ⟨214445227283476919299460909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142963484855651279532973939 214445227283476919299460909)
            ·
              refine ⟨80416960231303844737297841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214445227283476919299460909 80416960231303844737297841)
              ·
                refine ⟨60312720173477883552973381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80416960231303844737297841 60312720173477883552973381)
                ·
                  refine ⟨11308635032527103166182509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60312720173477883552973381 11308635032527103166182509)
                  ·
                    refine ⟨4240738137197663687318441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11308635032527103166182509 4240738137197663687318441)
                    ·
                      refine ⟨3180553602898247765488831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240738137197663687318441 3180553602898247765488831)
                      ·
                        rfl

theorem cell23_6194106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_6194106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194106 prefixEnd_6194106 := by exact prefixLift 6194106
  have htrace : WordTrace (prefixWord ++ tailWord_6194106) baseStart_6194106 baseEnd_6194106 := by
    simpa [prefixWord, tailWord_6194106, baseEnd_6194106] using wordTrace_append hprefix tailTrace_6194106
  have hstable : (prefixWord ++ tailWord_6194106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194106).length < 2 ^ (prefixWord ++ tailWord_6194106).sum := by decide
  have hdescent : baseEnd_6194106 < baseStart_6194106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194123 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 2, 3, 2]
def baseStart_6194123 : Nat := 118140960795 + 6194123 * 2 ^ 59
def prefixEnd_6194123 : Nat := 4983230072969 + 3 ^ 40 * 6194123 * 2
def baseEnd_6194123 : Nat := 3180562332069374198976253

theorem tailTrace_6194123 : CollatzResearch.WordTrace tailWord_6194123 prefixEnd_6194123 3180562332069374198976253 := by
  unfold tailWord_6194123
  simp only [CollatzResearch.WordTrace]
  refine ⟨225918225738757717832019023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150612150492505145221346015 225918225738757717832019023)
  ·
    refine ⟨338877338608136576748028535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225918225738757717832019023 338877338608136576748028535)
    ·
      refine ⟨508316007912204865122042803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338877338608136576748028535 508316007912204865122042803)
      ·
        refine ⟨762474011868307297683064205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508316007912204865122042803 762474011868307297683064205)
        ·
          refine ⟨285927754450615236631149077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 762474011868307297683064205 285927754450615236631149077)
          ·
            refine ⟨13402863489872589217085113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285927754450615236631149077 13402863489872589217085113)
            ·
              refine ⟨10052147617404441912813835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13402863489872589217085113 10052147617404441912813835)
              ·
                refine ⟨15078221426106662869220753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052147617404441912813835 15078221426106662869220753)
                ·
                  refine ⟨11308666069579997151915565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15078221426106662869220753 11308666069579997151915565)
                  ·
                    refine ⟨4240749776092498931968337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11308666069579997151915565 4240749776092498931968337)
                    ·
                      refine ⟨3180562332069374198976253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240749776092498931968337 3180562332069374198976253)
                      ·
                        rfl

theorem cell23_6194123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3, 2].length) (baseStart_6194123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194123 prefixEnd_6194123 := by exact prefixLift 6194123
  have htrace : WordTrace (prefixWord ++ tailWord_6194123) baseStart_6194123 baseEnd_6194123 := by
    simpa [prefixWord, tailWord_6194123, baseEnd_6194123] using wordTrace_append hprefix tailTrace_6194123
  have hstable : (prefixWord ++ tailWord_6194123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194123).length < 2 ^ (prefixWord ++ tailWord_6194123).sum := by decide
  have hdescent : baseEnd_6194123 < baseStart_6194123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194129 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_6194129 : Nat := 118140960795 + 6194129 * 2 ^ 59
def prefixEnd_6194129 : Nat := 4983230072969 + 3 ^ 40 * 6194129 * 2
def baseEnd_6194129 : Nat := 1060188470984433725167075

theorem tailTrace_6194129 : CollatzResearch.WordTrace tailWord_6194129 prefixEnd_6194129 1060188470984433725167075 := by
  unfold tailWord_6194129
  simp only [CollatzResearch.WordTrace]
  refine ⟨225918444576735980856737441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150612296384490653904491627 225918444576735980856737441)
  ·
    refine ⟨169438833432551985642553081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225918444576735980856737441 169438833432551985642553081)
    ·
      refine ⟨127079125074413989231914811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169438833432551985642553081 127079125074413989231914811)
      ·
        refine ⟨190618687611620983847872217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127079125074413989231914811 190618687611620983847872217)
        ·
          refine ⟨142964015708715737885904163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190618687611620983847872217 142964015708715737885904163)
          ·
            refine ⟨214446023563073606828856245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142964015708715737885904163 214446023563073606828856245)
            ·
              refine ⟨20104314709038150640205273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214446023563073606828856245 20104314709038150640205273)
              ·
                refine ⟨15078236031778612980153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20104314709038150640205273 15078236031778612980153955)
                ·
                  refine ⟨22617354047667919470230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15078236031778612980153955 22617354047667919470230933)
                  ·
                    refine ⟨1060188470984433725167075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22617354047667919470230933 1060188470984433725167075)
                    ·
                      rfl

theorem cell23_6194129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_6194129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194129 prefixEnd_6194129 := by exact prefixLift 6194129
  have htrace : WordTrace (prefixWord ++ tailWord_6194129) baseStart_6194129 baseEnd_6194129 := by
    simpa [prefixWord, tailWord_6194129, baseEnd_6194129] using wordTrace_append hprefix tailTrace_6194129
  have hstable : (prefixWord ++ tailWord_6194129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194129).length < 2 ^ (prefixWord ++ tailWord_6194129).sum := by decide
  have hdescent : baseEnd_6194129 < baseStart_6194129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194159 : List Nat := [1, 1, 2, 1, 4, 3, 3, 8]
def baseStart_6194159 : Nat := 118140960795 + 6194159 * 2 ^ 59
def prefixEnd_6194159 : Nat := 4983230072969 + 3 ^ 40 * 6194159 * 2
def baseEnd_6194159 : Nat := 117799289532330965115781

theorem tailTrace_6194159 : CollatzResearch.WordTrace tailWord_6194159 prefixEnd_6194159 117799289532330965115781 := by
  unfold tailWord_6194159
  simp only [CollatzResearch.WordTrace]
  refine ⟨225919538766627295980329531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150613025844418197320219687 225919538766627295980329531)
  ·
    refine ⟨338879308149940943970494297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225919538766627295980329531 338879308149940943970494297)
    ·
      refine ⟨254159481112455707977870723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338879308149940943970494297 254159481112455707977870723)
      ·
        refine ⟨381239221668683561966806085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254159481112455707977870723 381239221668683561966806085)
        ·
          refine ⟨71482354062878167868776141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381239221668683561966806085 71482354062878167868776141)
          ·
            refine ⟨26805882773579312950791053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71482354062878167868776141 26805882773579312950791053)
            ·
              refine ⟨10052206040092242356546645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26805882773579312950791053 10052206040092242356546645)
              ·
                refine ⟨117799289532330965115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10052206040092242356546645 117799289532330965115781)
                ·
                  rfl

theorem cell23_6194159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 8].length) (baseStart_6194159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194159 prefixEnd_6194159 := by exact prefixLift 6194159
  have htrace : WordTrace (prefixWord ++ tailWord_6194159) baseStart_6194159 baseEnd_6194159 := by
    simpa [prefixWord, tailWord_6194159, baseEnd_6194159] using wordTrace_append hprefix tailTrace_6194159
  have hstable : (prefixWord ++ tailWord_6194159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194159).length < 2 ^ (prefixWord ++ tailWord_6194159).sum := by decide
  have hdescent : baseEnd_6194159 < baseStart_6194159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194174 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6194174 : Nat := 118140960795 + 6194174 * 2 ^ 59
def prefixEnd_6194174 : Nat := 4983230072969 + 3 ^ 40 * 6194174 * 2
def baseEnd_6194174 : Nat := 3180588519582753499438519

theorem tailTrace_6194174 : CollatzResearch.WordTrace tailWord_6194174 prefixEnd_6194174 3180588519582753499438519 := by
  unfold tailWord_6194174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28240010732696619192765697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150613390574381969028083717 28240010732696619192765697)
  ·
    refine ⟨21180008049522464394574273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28240010732696619192765697 21180008049522464394574273)
    ·
      refine ⟨15885006037141848295930705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21180008049522464394574273 15885006037141848295930705)
      ·
        refine ⟨11913754527856386221948029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15885006037141848295930705 11913754527856386221948029)
        ·
          refine ⟨4467657947946144833230511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11913754527856386221948029 4467657947946144833230511)
          ·
            refine ⟨6701486921919217249845767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467657947946144833230511 6701486921919217249845767)
            ·
              refine ⟨10052230382878825874768651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701486921919217249845767 10052230382878825874768651)
              ·
                refine ⟨15078345574318238812152977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052230382878825874768651 15078345574318238812152977)
                ·
                  refine ⟨11308759180738679109114733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15078345574318238812152977 11308759180738679109114733)
                  ·
                    refine ⟨4240784692777004665918025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11308759180738679109114733 4240784692777004665918025)
                    ·
                      refine ⟨3180588519582753499438519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240784692777004665918025 3180588519582753499438519)
                      ·
                        rfl

theorem cell23_6194174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6194174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194174 prefixEnd_6194174 := by exact prefixLift 6194174
  have htrace : WordTrace (prefixWord ++ tailWord_6194174) baseStart_6194174 baseEnd_6194174 := by
    simpa [prefixWord, tailWord_6194174, baseEnd_6194174] using wordTrace_append hprefix tailTrace_6194174
  have hstable : (prefixWord ++ tailWord_6194174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194174).length < 2 ^ (prefixWord ++ tailWord_6194174).sum := by decide
  have hdescent : baseEnd_6194174 < baseStart_6194174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194187 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 1, 2, 2]
def baseStart_6194187 : Nat := 118140960795 + 6194187 * 2 ^ 59
def prefixEnd_6194187 : Nat := 4983230072969 + 3 ^ 40 * 6194187 * 2
def baseEnd_6194187 : Nat := 3180595194831261948575959

theorem tailTrace_6194187 : CollatzResearch.WordTrace tailWord_6194187 prefixEnd_6194187 3180595194831261948575959 := by
  unfold tailWord_6194187
  simp only [CollatzResearch.WordTrace]
  refine ⟨225920560010525856762348815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150613706673683904508232543 225920560010525856762348815)
  ·
    refine ⟨338880840015788785143523223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225920560010525856762348815 338880840015788785143523223)
    ·
      refine ⟨508321260023683177715284835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338880840015788785143523223 508321260023683177715284835)
      ·
        refine ⟨762481890035524766572927253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508321260023683177715284835 762481890035524766572927253)
        ·
          refine ⟨35741338595415223433105965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 762481890035524766572927253 35741338595415223433105965)
          ·
            refine ⟨13403001973280708787414737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35741338595415223433105965 13403001973280708787414737)
            ·
              refine ⟨10052251479960531590561053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13403001973280708787414737 10052251479960531590561053)
              ·
                refine ⟨3769594304985199346460395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10052251479960531590561053 3769594304985199346460395)
                ·
                  refine ⟨5654391457477799019690593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769594304985199346460395 5654391457477799019690593)
                  ·
                    refine ⟨4240793593108349264767945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654391457477799019690593 4240793593108349264767945)
                    ·
                      refine ⟨3180595194831261948575959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240793593108349264767945 3180595194831261948575959)
                      ·
                        rfl

theorem cell23_6194187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 2, 2].length) (baseStart_6194187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194187 prefixEnd_6194187 := by exact prefixLift 6194187
  have htrace : WordTrace (prefixWord ++ tailWord_6194187) baseStart_6194187 baseEnd_6194187 := by
    simpa [prefixWord, tailWord_6194187, baseEnd_6194187] using wordTrace_append hprefix tailTrace_6194187
  have hstable : (prefixWord ++ tailWord_6194187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194187).length < 2 ^ (prefixWord ++ tailWord_6194187).sum := by decide
  have hdescent : baseEnd_6194187 < baseStart_6194187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194190 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6194190 : Nat := 118140960795 + 6194190 * 2 ^ 59
def prefixEnd_6194190 : Nat := 4983230072969 + 3 ^ 40 * 6194190 * 2
def baseEnd_6194190 : Nat := 3180596735273225436838445

theorem tailTrace_6194190 : CollatzResearch.WordTrace tailWord_6194190 prefixEnd_6194190 3180596735273225436838445 := by
  unfold tailWord_6194190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28240083678689373534338503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150613779619676658849805349 28240083678689373534338503)
  ·
    refine ⟨42360125518034060301507755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28240083678689373534338503 42360125518034060301507755)
    ·
      refine ⟨63540188277051090452261633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42360125518034060301507755 63540188277051090452261633)
      ·
        refine ⟨47655141207788317839196225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63540188277051090452261633 47655141207788317839196225)
        ·
          refine ⟨35741355905841238379397169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47655141207788317839196225 35741355905841238379397169)
          ·
            refine ⟨26806016929380928784547877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35741355905841238379397169 26806016929380928784547877)
            ·
              refine ⟨5026128174258924147102727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26806016929380928784547877 5026128174258924147102727)
              ·
                refine ⟨7539192261388386220654091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026128174258924147102727 7539192261388386220654091)
                ·
                  refine ⟨11308788392082579330981137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539192261388386220654091 11308788392082579330981137)
                  ·
                    refine ⟨8481591294061934498235853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11308788392082579330981137 8481591294061934498235853)
                    ·
                      refine ⟨3180596735273225436838445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8481591294061934498235853 3180596735273225436838445)
                      ·
                        rfl

theorem cell23_6194190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6194190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194190 prefixEnd_6194190 := by exact prefixLift 6194190
  have htrace : WordTrace (prefixWord ++ tailWord_6194190) baseStart_6194190 baseEnd_6194190 := by
    simpa [prefixWord, tailWord_6194190, baseEnd_6194190] using wordTrace_append hprefix tailTrace_6194190
  have hstable : (prefixWord ++ tailWord_6194190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194190).length < 2 ^ (prefixWord ++ tailWord_6194190).sum := by decide
  have hdescent : baseEnd_6194190 < baseStart_6194190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194219 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 6]
def baseStart_6194219 : Nat := 118140960795 + 6194219 * 2 ^ 59
def prefixEnd_6194219 : Nat := 4983230072969 + 3 ^ 40 * 6194219 * 2
def baseEnd_6194219 : Nat := 1060203875404068607791937

theorem tailTrace_6194219 : CollatzResearch.WordTrace tailWord_6194219 prefixEnd_6194219 1060203875404068607791937 := by
  unfold tailWord_6194219
  simp only [CollatzResearch.WordTrace]
  refine ⟨225921727146409926227513711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150614484764273284151675807 225921727146409926227513711)
  ·
    refine ⟨338882590719614889341270567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225921727146409926227513711 338882590719614889341270567)
    ·
      refine ⟨508323886079422334011905851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338882590719614889341270567 508323886079422334011905851)
      ·
        refine ⟨762485829119133501017858777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508323886079422334011905851 762485829119133501017858777)
        ·
          refine ⟨571864371839350125763394083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762485829119133501017858777 571864371839350125763394083)
          ·
            refine ⟨857796557759025188645091125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571864371839350125763394083 857796557759025188645091125)
            ·
              refine ⟨80418427289908611435477293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 857796557759025188645091125 80418427289908611435477293)
              ·
                refine ⟨30156910233715729288303985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80418427289908611435477293 30156910233715729288303985)
                ·
                  refine ⟨22617682675286796966227989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30156910233715729288303985 22617682675286796966227989)
                  ·
                    refine ⟨1060203875404068607791937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22617682675286796966227989 1060203875404068607791937)
                    ·
                      rfl

theorem cell23_6194219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_6194219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194219 prefixEnd_6194219 := by exact prefixLift 6194219
  have htrace : WordTrace (prefixWord ++ tailWord_6194219) baseStart_6194219 baseEnd_6194219 := by
    simpa [prefixWord, tailWord_6194219, baseEnd_6194219] using wordTrace_append hprefix tailTrace_6194219
  have hstable : (prefixWord ++ tailWord_6194219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194219).length < 2 ^ (prefixWord ++ tailWord_6194219).sum := by decide
  have hdescent : baseEnd_6194219 < baseStart_6194219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194220 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_6194220 : Nat := 118140960795 + 6194220 * 2 ^ 59
def prefixEnd_6194220 : Nat := 4983230072969 + 3 ^ 40 * 6194220 * 2
def baseEnd_6194220 : Nat := 3180612139692860319463307

theorem tailTrace_6194220 : CollatzResearch.WordTrace tailWord_6194220 prefixEnd_6194220 3180612139692860319463307 := by
  unfold tailWord_6194220
  simp only [CollatzResearch.WordTrace]
  refine ⟨112960881809703151699150057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150614509079604202265533409 112960881809703151699150057)
  ·
    refine ⟨84720661357277363774362543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112960881809703151699150057 84720661357277363774362543)
    ·
      refine ⟨127080992035916045661543815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84720661357277363774362543 127080992035916045661543815)
      ·
        refine ⟨190621488053874068492315723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127080992035916045661543815 190621488053874068492315723)
        ·
          refine ⟨285932232080811102738473585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190621488053874068492315723 285932232080811102738473585)
          ·
            refine ⟨214449174060608327053855189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285932232080811102738473585 214449174060608327053855189)
            ·
              refine ⟨5026152517045507665324731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 214449174060608327053855189 5026152517045507665324731)
              ·
                refine ⟨7539228775568261497987097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026152517045507665324731 7539228775568261497987097)
                ·
                  refine ⟨5654421581676196123490323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539228775568261497987097 5654421581676196123490323)
                  ·
                    refine ⟨8481632372514294185235485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654421581676196123490323 8481632372514294185235485)
                    ·
                      refine ⟨3180612139692860319463307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8481632372514294185235485 3180612139692860319463307)
                      ·
                        rfl

theorem cell23_6194220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_6194220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194220 prefixEnd_6194220 := by exact prefixLift 6194220
  have htrace : WordTrace (prefixWord ++ tailWord_6194220) baseStart_6194220 baseEnd_6194220 := by
    simpa [prefixWord, tailWord_6194220, baseEnd_6194220] using wordTrace_append hprefix tailTrace_6194220
  have hstable : (prefixWord ++ tailWord_6194220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194220).length < 2 ^ (prefixWord ++ tailWord_6194220).sum := by decide
  have hdescent : baseEnd_6194220 < baseStart_6194220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194243 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 6, 2, 2]
def baseStart_6194243 : Nat := 118140960795 + 6194243 * 2 ^ 59
def prefixEnd_6194243 : Nat := 4983230072969 + 3 ^ 40 * 6194243 * 2
def baseEnd_6194243 : Nat := 3180623949747913729475701

theorem tailTrace_6194243 : CollatzResearch.WordTrace tailWord_6194243 prefixEnd_6194243 3180623949747913729475701 := by
  unfold tailWord_6194243
  simp only [CollatzResearch.WordTrace]
  refine ⟨225922602498322978326387383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150615068332215318884258255 225922602498322978326387383)
  ·
    refine ⟨338883903747484467489581075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225922602498322978326387383 338883903747484467489581075)
    ·
      refine ⟨508325855621226701234371613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338883903747484467489581075 508325855621226701234371613)
      ·
        refine ⟨190622195857960012962889355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508325855621226701234371613 190622195857960012962889355)
        ·
          refine ⟨285933293786940019444334033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190622195857960012962889355 285933293786940019444334033)
          ·
            refine ⟨214449970340205014583250525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285933293786940019444334033 214449970340205014583250525)
            ·
              refine ⟨80418738877576880468718947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214449970340205014583250525 80418738877576880468718947)
              ·
                refine ⟨120628108316365320703078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80418738877576880468718947 120628108316365320703078421)
                ·
                  refine ⟨5654442577329624407956801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120628108316365320703078421 5654442577329624407956801)
                  ·
                    refine ⟨4240831932997218305967601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654442577329624407956801 4240831932997218305967601)
                    ·
                      refine ⟨3180623949747913729475701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240831932997218305967601 3180623949747913729475701)
                      ·
                        rfl

theorem cell23_6194243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_6194243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194243 prefixEnd_6194243 := by exact prefixLift 6194243
  have htrace : WordTrace (prefixWord ++ tailWord_6194243) baseStart_6194243 baseEnd_6194243 := by
    simpa [prefixWord, tailWord_6194243, baseEnd_6194243] using wordTrace_append hprefix tailTrace_6194243
  have hstable : (prefixWord ++ tailWord_6194243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194243).length < 2 ^ (prefixWord ++ tailWord_6194243).sum := by decide
  have hdescent : baseEnd_6194243 < baseStart_6194243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194260 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_6194260 : Nat := 118140960795 + 6194260 * 2 ^ 59
def prefixEnd_6194260 : Nat := 4983230072969 + 3 ^ 40 * 6194260 * 2
def baseEnd_6194260 : Nat := 3180632678919040162963123

theorem tailTrace_6194260 : CollatzResearch.WordTrace tailWord_6194260 prefixEnd_6194260 3180632678919040162963123 := by
  unfold tailWord_6194260
  simp only [CollatzResearch.WordTrace]
  refine ⟨112961611269630695114878117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150615481692840926819837489 112961611269630695114878117)
  ·
    refine ⟨21180302113055755334039647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112961611269630695114878117 21180302113055755334039647)
    ·
      refine ⟨31770453169583633001059471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21180302113055755334039647 31770453169583633001059471)
      ·
        refine ⟨47655679754375449501589207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31770453169583633001059471 47655679754375449501589207)
        ·
          refine ⟨71483519631563174252383811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47655679754375449501589207 71483519631563174252383811)
          ·
            refine ⟨107225279447344761378575717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71483519631563174252383811 107225279447344761378575717)
            ·
              refine ⟨20104739896377142758482947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107225279447344761378575717 20104739896377142758482947)
              ·
                refine ⟨30157109844565714137724421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20104739896377142758482947 30157109844565714137724421)
                ·
                  refine ⟨5654458095856071400823329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30157109844565714137724421 5654458095856071400823329)
                  ·
                    refine ⟨4240843571892053550617497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654458095856071400823329 4240843571892053550617497)
                    ·
                      refine ⟨3180632678919040162963123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240843571892053550617497 3180632678919040162963123)
                      ·
                        rfl

theorem cell23_6194260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_6194260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194260 prefixEnd_6194260 := by exact prefixLift 6194260
  have htrace : WordTrace (prefixWord ++ tailWord_6194260) baseStart_6194260 baseEnd_6194260 := by
    simpa [prefixWord, tailWord_6194260, baseEnd_6194260] using wordTrace_append hprefix tailTrace_6194260
  have hstable : (prefixWord ++ tailWord_6194260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194260).length < 2 ^ (prefixWord ++ tailWord_6194260).sum := by decide
  have hdescent : baseEnd_6194260 < baseStart_6194260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194276 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_6194276 : Nat := 118140960795 + 6194276 * 2 ^ 59
def prefixEnd_6194276 : Nat := 4983230072969 + 3 ^ 40 * 6194276 * 2
def baseEnd_6194276 : Nat := 3180640894609512100363049

theorem tailTrace_6194276 : CollatzResearch.WordTrace tailWord_6194276 prefixEnd_6194276 3180640894609512100363049 := by
  unfold tailWord_6194276
  simp only [CollatzResearch.WordTrace]
  refine ⟨112961903053601712481169341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150615870738135616641559121 112961903053601712481169341)
  ·
    refine ⟨42360713645100642180438503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112961903053601712481169341 42360713645100642180438503)
    ·
      refine ⟨63541070467650963270657755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42360713645100642180438503 63541070467650963270657755)
      ·
        refine ⟨95311605701476444905986633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63541070467650963270657755 95311605701476444905986633)
        ·
          refine ⟨71483704276107333679489975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95311605701476444905986633 71483704276107333679489975)
          ·
            refine ⟨107225556414161000519234963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71483704276107333679489975 107225556414161000519234963)
            ·
              refine ⟨160838334621241500778852445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107225556414161000519234963 160838334621241500778852445)
              ·
                refine ⟨60314375482965562792069667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160838334621241500778852445 60314375482965562792069667)
                ·
                  refine ⟨90471563224448344188104501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60314375482965562792069667 90471563224448344188104501)
                  ·
                    refine ⟨8481709052292032267634797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90471563224448344188104501 8481709052292032267634797)
                    ·
                      refine ⟨3180640894609512100363049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8481709052292032267634797 3180640894609512100363049)
                      ·
                        rfl

theorem cell23_6194276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_6194276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194276 prefixEnd_6194276 := by exact prefixLift 6194276
  have htrace : WordTrace (prefixWord ++ tailWord_6194276) baseStart_6194276 baseEnd_6194276 := by
    simpa [prefixWord, tailWord_6194276, baseEnd_6194276] using wordTrace_append hprefix tailTrace_6194276
  have hstable : (prefixWord ++ tailWord_6194276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194276).length < 2 ^ (prefixWord ++ tailWord_6194276).sum := by decide
  have hdescent : baseEnd_6194276 < baseStart_6194276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194296 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_6194296 : Nat := 118140960795 + 6194296 * 2 ^ 59
def prefixEnd_6194296 : Nat := 4983230072969 + 3 ^ 40 * 6194296 * 2
def baseEnd_6194296 : Nat := 1060217054740867340704319

theorem tailTrace_6194296 : CollatzResearch.WordTrace tailWord_6194296 prefixEnd_6194296 1060217054740867340704319 := by
  unfold tailWord_6194296
  simp only [CollatzResearch.WordTrace]
  refine ⟨112962267783565484189033371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150616357044753978918711161 112962267783565484189033371)
  ·
    refine ⟨169443401675348226283550057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112962267783565484189033371 169443401675348226283550057)
    ·
      refine ⟨127082551256511169712662543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169443401675348226283550057 127082551256511169712662543)
      ·
        refine ⟨190623826884766754568993815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127082551256511169712662543 190623826884766754568993815)
        ·
          refine ⟨285935740327150131853490723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190623826884766754568993815 285935740327150131853490723)
          ·
            refine ⟨428903610490725197780236085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285935740327150131853490723 428903610490725197780236085)
            ·
              refine ⟨40209713483505487291897133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 428903610490725197780236085 40209713483505487291897133)
              ·
                refine ⟨15078642556314557734461425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40209713483505487291897133 15078642556314557734461425)
                ·
                  refine ⟨11308981917235918300846069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15078642556314557734461425 11308981917235918300846069)
                  ·
                    refine ⟨1060217054740867340704319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11308981917235918300846069 1060217054740867340704319)
                    ·
                      rfl

theorem cell23_6194296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_6194296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194296 prefixEnd_6194296 := by exact prefixLift 6194296
  have htrace : WordTrace (prefixWord ++ tailWord_6194296) baseStart_6194296 baseEnd_6194296 := by
    simpa [prefixWord, tailWord_6194296, baseEnd_6194296] using wordTrace_append hprefix tailTrace_6194296
  have hstable : (prefixWord ++ tailWord_6194296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194296).length < 2 ^ (prefixWord ++ tailWord_6194296).sum := by decide
  have hdescent : baseEnd_6194296 < baseStart_6194296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194376 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6194376 : Nat := 118140960795 + 6194376 * 2 ^ 59
def prefixEnd_6194376 : Nat := 4983230072969 + 3 ^ 40 * 6194376 * 2
def baseEnd_6194376 : Nat := 3180692242674961709112589

theorem tailTrace_6194376 : CollatzResearch.WordTrace tailWord_6194376 prefixEnd_6194376 3180692242674961709112589 := by
  unfold tailWord_6194376
  simp only [CollatzResearch.WordTrace]
  refine ⟨112963726703420571020489491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150618302271227428027319321 112963726703420571020489491)
  ·
    refine ⟨169445590055130856530734237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112963726703420571020489491 169445590055130856530734237)
    ·
      refine ⟨63542096270674071199025339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169445590055130856530734237 63542096270674071199025339)
      ·
        refine ⟨95313144406011106798538009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63542096270674071199025339 95313144406011106798538009)
        ·
          refine ⟨71484858304508330098903507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95313144406011106798538009 71484858304508330098903507)
          ·
            refine ⟨107227287456762495148355261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71484858304508330098903507 107227287456762495148355261)
            ·
              refine ⟨40210232796285935680633223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107227287456762495148355261 40210232796285935680633223)
              ·
                refine ⟨60315349194428903520949835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40210232796285935680633223 60315349194428903520949835)
                ·
                  refine ⟨90473023791643355281424753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60315349194428903520949835 90473023791643355281424753)
                  ·
                    refine ⟨67854767843732516461068565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90473023791643355281424753 67854767843732516461068565)
                    ·
                      refine ⟨3180692242674961709112589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67854767843732516461068565 3180692242674961709112589)
                      ·
                        rfl

theorem cell23_6194376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6194376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194376 prefixEnd_6194376 := by exact prefixLift 6194376
  have htrace : WordTrace (prefixWord ++ tailWord_6194376) baseStart_6194376 baseEnd_6194376 := by
    simpa [prefixWord, tailWord_6194376, baseEnd_6194376] using wordTrace_append hprefix tailTrace_6194376
  have hstable : (prefixWord ++ tailWord_6194376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194376).length < 2 ^ (prefixWord ++ tailWord_6194376).sum := by decide
  have hdescent : baseEnd_6194376 < baseStart_6194376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194400 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_6194400 : Nat := 118140960795 + 6194400 * 2 ^ 59
def prefixEnd_6194400 : Nat := 4983230072969 + 3 ^ 40 * 6194400 * 2
def baseEnd_6194400 : Nat := 3180704566210669615212479

theorem tailTrace_6194400 : CollatzResearch.WordTrace tailWord_6194400 prefixEnd_6194400 3180704566210669615212479 := by
  unfold tailWord_6194400
  simp only [CollatzResearch.WordTrace]
  refine ⟨112964164379377097069926327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150618885839169462759901769 112964164379377097069926327)
  ·
    refine ⟨169446246569065645604889491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112964164379377097069926327 169446246569065645604889491)
    ·
      refine ⟨254169369853598468407334237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169446246569065645604889491 254169369853598468407334237)
      ·
        refine ⟨95313513695099425652750339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254169369853598468407334237 95313513695099425652750339)
        ·
          refine ⟨142970270542649138479125509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95313513695099425652750339 142970270542649138479125509)
          ·
            refine ⟨26806925726746713464836033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142970270542649138479125509 26806925726746713464836033)
            ·
              refine ⟨20105194295060035098627025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26806925726746713464836033 20105194295060035098627025)
              ·
                refine ⟨15078895721295026323970269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20105194295060035098627025 15078895721295026323970269)
                ·
                  refine ⟨5654585895485634871488851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15078895721295026323970269 5654585895485634871488851)
                  ·
                    refine ⟨8481878843228452307233277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654585895485634871488851 8481878843228452307233277)
                    ·
                      refine ⟨3180704566210669615212479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8481878843228452307233277 3180704566210669615212479)
                      ·
                        rfl

theorem cell23_6194400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_6194400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194400 prefixEnd_6194400 := by exact prefixLift 6194400
  have htrace : WordTrace (prefixWord ++ tailWord_6194400) baseStart_6194400 baseEnd_6194400 := by
    simpa [prefixWord, tailWord_6194400, baseEnd_6194400] using wordTrace_append hprefix tailTrace_6194400
  have hstable : (prefixWord ++ tailWord_6194400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194400).length < 2 ^ (prefixWord ++ tailWord_6194400).sum := by decide
  have hdescent : baseEnd_6194400 < baseStart_6194400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194410 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_6194410 : Nat := 118140960795 + 6194410 * 2 ^ 59
def prefixEnd_6194410 : Nat := 4983230072969 + 3 ^ 40 * 6194410 * 2
def baseEnd_6194410 : Nat := 3180709701017214576087433

theorem tailTrace_6194410 : CollatzResearch.WordTrace tailWord_6194410 prefixEnd_6194410 3180709701017214576087433 := by
  unfold tailWord_6194410
  simp only [CollatzResearch.WordTrace]
  refine ⟨56482173372179491461929171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150619128992478643898477789 56482173372179491461929171)
  ·
    refine ⟨84723260058269237192893757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56482173372179491461929171 84723260058269237192893757)
    ·
      refine ⟨31771222521850963947335159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84723260058269237192893757 31771222521850963947335159)
      ·
        refine ⟨47656833782776445921002739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31771222521850963947335159 47656833782776445921002739)
        ·
          refine ⟨71485250674164668881504109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47656833782776445921002739 71485250674164668881504109)
          ·
            refine ⟨26806969002811750830564041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71485250674164668881504109 26806969002811750830564041)
            ·
              refine ⟨20105226752108813122923031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26806969002811750830564041 20105226752108813122923031)
              ·
                refine ⟨30157840128163219684384547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20105226752108813122923031 30157840128163219684384547)
                ·
                  refine ⟨45236760192244829526576821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30157840128163219684384547 45236760192244829526576821)
                  ·
                    refine ⟨4240946268022952768116577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45236760192244829526576821 4240946268022952768116577)
                    ·
                      refine ⟨3180709701017214576087433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240946268022952768116577 3180709701017214576087433)
                      ·
                        rfl

theorem cell23_6194410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_6194410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194410 prefixEnd_6194410 := by exact prefixLift 6194410
  have htrace : WordTrace (prefixWord ++ tailWord_6194410) baseStart_6194410 baseEnd_6194410 := by
    simpa [prefixWord, tailWord_6194410, baseEnd_6194410] using wordTrace_append hprefix tailTrace_6194410
  have hstable : (prefixWord ++ tailWord_6194410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194410).length < 2 ^ (prefixWord ++ tailWord_6194410).sum := by decide
  have hdescent : baseEnd_6194410 < baseStart_6194410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194423 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_6194423 : Nat := 118140960795 + 6194423 * 2 ^ 59
def prefixEnd_6194423 : Nat := 4983230072969 + 3 ^ 40 * 6194423 * 2
def baseEnd_6194423 : Nat := 3180716376265723025224873

theorem tailTrace_6194423 : CollatzResearch.WordTrace tailWord_6194423 prefixEnd_6194423 3180716376265723025224873 := by
  unfold tailWord_6194423
  simp only [CollatzResearch.WordTrace]
  refine ⟨225929167637670869067939923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150619445091780579378626615 225929167637670869067939923)
  ·
    refine ⟨338893751456506303601909885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225929167637670869067939923 338893751456506303601909885)
    ·
      refine ⟨127085156796189863850716207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338893751456506303601909885 127085156796189863850716207)
      ·
        refine ⟨190627735194284795776074311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127085156796189863850716207 190627735194284795776074311)
        ·
          refine ⟨285941602791427193664111467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190627735194284795776074311 285941602791427193664111467)
          ·
            refine ⟨428912404187140790496167201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285941602791427193664111467 428912404187140790496167201)
            ·
              refine ⟨321684303140355592872125401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428912404187140790496167201 321684303140355592872125401)
              ·
                refine ⟨241263227355266694654094051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321684303140355592872125401 241263227355266694654094051)
                ·
                  refine ⟨361894841032900041981141077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241263227355266694654094051 361894841032900041981141077)
                  ·
                    refine ⟨4240955168354297366966497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 361894841032900041981141077 4240955168354297366966497)
                    ·
                      refine ⟨3180716376265723025224873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4240955168354297366966497 3180716376265723025224873)
                      ·
                        rfl

theorem cell23_6194423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_6194423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194423 prefixEnd_6194423 := by exact prefixLift 6194423
  have htrace : WordTrace (prefixWord ++ tailWord_6194423) baseStart_6194423 baseEnd_6194423 := by
    simpa [prefixWord, tailWord_6194423, baseEnd_6194423] using wordTrace_append hprefix tailTrace_6194423
  have hstable : (prefixWord ++ tailWord_6194423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194423).length < 2 ^ (prefixWord ++ tailWord_6194423).sum := by decide
  have hdescent : baseEnd_6194423 < baseStart_6194423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194443 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_6194443 : Nat := 118140960795 + 6194443 * 2 ^ 59
def prefixEnd_6194443 : Nat := 4983230072969 + 3 ^ 40 * 6194443 * 2
def baseEnd_6194443 : Nat := 3180726645878812946974781

theorem tailTrace_6194443 : CollatzResearch.WordTrace tailWord_6194443 prefixEnd_6194443 3180726645878812946974781 := by
  unfold tailWord_6194443
  simp only [CollatzResearch.WordTrace]
  refine ⟨225929897097598412483667983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150619931398398941655778655 225929897097598412483667983)
  ·
    refine ⟨338894845646397618725501975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225929897097598412483667983 338894845646397618725501975)
    ·
      refine ⟨508342268469596428088252963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338894845646397618725501975 508342268469596428088252963)
      ·
        refine ⟨762513402704394642132379445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508342268469596428088252963 762513402704394642132379445)
        ·
          refine ⟨71485631503536997699910573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 762513402704394642132379445 71485631503536997699910573)
          ·
            refine ⟨26807111813826374137466465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71485631503536997699910573 26807111813826374137466465)
            ·
              refine ⟨20105333860369780603099849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26807111813826374137466465 20105333860369780603099849)
              ·
                refine ⟨15079000395277335452324887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20105333860369780603099849 15079000395277335452324887)
                ·
                  refine ⟨22618500592916003178487331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079000395277335452324887 22618500592916003178487331)
                  ·
                    refine ⟨33927750889374004767730997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22618500592916003178487331 33927750889374004767730997)
                    ·
                      refine ⟨3180726645878812946974781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33927750889374004767730997 3180726645878812946974781)
                      ·
                        rfl

theorem cell23_6194443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_6194443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194443 prefixEnd_6194443 := by exact prefixLift 6194443
  have htrace : WordTrace (prefixWord ++ tailWord_6194443) baseStart_6194443 baseEnd_6194443 := by
    simpa [prefixWord, tailWord_6194443, baseEnd_6194443] using wordTrace_append hprefix tailTrace_6194443
  have hstable : (prefixWord ++ tailWord_6194443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194443).length < 2 ^ (prefixWord ++ tailWord_6194443).sum := by decide
  have hdescent : baseEnd_6194443 < baseStart_6194443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194453 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_6194453 : Nat := 118140960795 + 6194453 * 2 ^ 59
def prefixEnd_6194453 : Nat := 4983230072969 + 3 ^ 40 * 6194453 * 2
def baseEnd_6194453 : Nat := 3180731780685357907849735

theorem tailTrace_6194453 : CollatzResearch.WordTrace tailWord_6194453 prefixEnd_6194453 3180731780685357907849735 := by
  unfold tailWord_6194453
  simp only [CollatzResearch.WordTrace]
  refine ⟨225930261827562184191532013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150620174551708122794354675 225930261827562184191532013)
  ·
    refine ⟨84723848185335819071824505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225930261827562184191532013 84723848185335819071824505)
    ·
      refine ⟨63542886139001864303868379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84723848185335819071824505 63542886139001864303868379)
      ·
        refine ⟨95314329208502796455802569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63542886139001864303868379 95314329208502796455802569)
        ·
          refine ⟨71485746906377097341851927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95314329208502796455802569 71485746906377097341851927)
          ·
            refine ⟨107228620359565646012777891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71485746906377097341851927 107228620359565646012777891)
            ·
              refine ⟨160842930539348469019166837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107228620359565646012777891 160842930539348469019166837)
              ·
                refine ⟨15079024738063918970546891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160842930539348469019166837 15079024738063918970546891)
                ·
                  refine ⟨22618537107095878455820337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079024738063918970546891 22618537107095878455820337)
                  ·
                    refine ⟨16963902830321908841865253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22618537107095878455820337 16963902830321908841865253)
                    ·
                      refine ⟨3180731780685357907849735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16963902830321908841865253 3180731780685357907849735)
                      ·
                        rfl

theorem cell23_6194453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_6194453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194453 prefixEnd_6194453 := by exact prefixLift 6194453
  have htrace : WordTrace (prefixWord ++ tailWord_6194453) baseStart_6194453 baseEnd_6194453 := by
    simpa [prefixWord, tailWord_6194453, baseEnd_6194453] using wordTrace_append hprefix tailTrace_6194453
  have hstable : (prefixWord ++ tailWord_6194453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194453).length < 2 ^ (prefixWord ++ tailWord_6194453).sum := by decide
  have hdescent : baseEnd_6194453 < baseStart_6194453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194474 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6194474 : Nat := 118140960795 + 6194474 * 2 ^ 59
def prefixEnd_6194474 : Nat := 4983230072969 + 3 ^ 40 * 6194474 * 2
def baseEnd_6194474 : Nat := 3180742563779102325687139

theorem tailTrace_6194474 : CollatzResearch.WordTrace tailWord_6194474 prefixEnd_6194474 3180742563779102325687139 := by
  unfold tailWord_6194474
  simp only [CollatzResearch.WordTrace]
  refine ⟨56482756940121526194511619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150620685173657403185364317 56482756940121526194511619)
  ·
    refine ⟨84724135410182289291767429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56482756940121526194511619 84724135410182289291767429)
    ·
      refine ⟨15885775389409179242206393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84724135410182289291767429 15885775389409179242206393)
      ·
        refine ⟨11914331542056884431654795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15885775389409179242206393 11914331542056884431654795)
        ·
          refine ⟨17871497313085326647482193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914331542056884431654795 17871497313085326647482193)
          ·
            refine ⟨13403622984813994985611645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17871497313085326647482193 13403622984813994985611645)
            ·
              refine ⟨5026358619305248119604367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13403622984813994985611645 5026358619305248119604367)
              ·
                refine ⟨7539537928957872179406551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026358619305248119604367 7539537928957872179406551)
                ·
                  refine ⟨11309306893436808269109827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539537928957872179406551 11309306893436808269109827)
                  ·
                    refine ⟨16963960340155212403664741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11309306893436808269109827 16963960340155212403664741)
                    ·
                      refine ⟨3180742563779102325687139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16963960340155212403664741 3180742563779102325687139)
                      ·
                        rfl

theorem cell23_6194474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6194474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194474 prefixEnd_6194474 := by exact prefixLift 6194474
  have htrace : WordTrace (prefixWord ++ tailWord_6194474) baseStart_6194474 baseEnd_6194474 := by
    simpa [prefixWord, tailWord_6194474, baseEnd_6194474] using wordTrace_append hprefix tailTrace_6194474
  have hstable : (prefixWord ++ tailWord_6194474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194474).length < 2 ^ (prefixWord ++ tailWord_6194474).sum := by decide
  have hdescent : baseEnd_6194474 < baseStart_6194474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194477 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6194477 : Nat := 118140960795 + 6194477 * 2 ^ 59
def prefixEnd_6194477 : Nat := 4983230072969 + 3 ^ 40 * 6194477 * 2
def baseEnd_6194477 : Nat := 3180744104221065813949625

theorem tailTrace_6194477 : CollatzResearch.WordTrace tailWord_6194477 prefixEnd_6194477 3180744104221065813949625 := by
  unfold tailWord_6194477
  simp only [CollatzResearch.WordTrace]
  refine ⟨225931137179475236290405685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150620758119650157526937123 225931137179475236290405685)
  ·
    refine ⟨21181044110575803402225533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225931137179475236290405685 21181044110575803402225533)
    ·
      refine ⟨7942891541465926275834575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21181044110575803402225533 7942891541465926275834575)
      ·
        refine ⟨11914337312198889413751863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7942891541465926275834575 11914337312198889413751863)
        ·
          refine ⟨17871505968298334120627795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914337312198889413751863 17871505968298334120627795)
          ·
            refine ⟨26807258952447501180941693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17871505968298334120627795 26807258952447501180941693)
            ·
              refine ⟨10052722107167812942853135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26807258952447501180941693 10052722107167812942853135)
              ·
                refine ⟨15079083160751719414279703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052722107167812942853135 15079083160751719414279703)
                ·
                  refine ⟨22618624741127579121419555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079083160751719414279703 22618624741127579121419555)
                  ·
                    refine ⟨33927937111691368682129333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22618624741127579121419555 33927937111691368682129333)
                    ·
                      refine ⟨3180744104221065813949625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33927937111691368682129333 3180744104221065813949625)
                      ·
                        rfl

theorem cell23_6194477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6194477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194477 prefixEnd_6194477 := by exact prefixLift 6194477
  have htrace : WordTrace (prefixWord ++ tailWord_6194477) baseStart_6194477 baseEnd_6194477 := by
    simpa [prefixWord, tailWord_6194477, baseEnd_6194477] using wordTrace_append hprefix tailTrace_6194477
  have hstable : (prefixWord ++ tailWord_6194477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194477).length < 2 ^ (prefixWord ++ tailWord_6194477).sum := by decide
  have hdescent : baseEnd_6194477 < baseStart_6194477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194513 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_6194513 : Nat := 118140960795 + 6194513 * 2 ^ 59
def prefixEnd_6194513 : Nat := 4983230072969 + 3 ^ 40 * 6194513 * 2
def baseEnd_6194513 : Nat := 3180762589524627673099459

theorem tailTrace_6194513 : CollatzResearch.WordTrace tailWord_6194513 prefixEnd_6194513 3180762589524627673099459 := by
  unfold tailWord_6194513
  simp only [CollatzResearch.WordTrace]
  refine ⟨225932450207344814438716193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150621633471563209625810795 225932450207344814438716193)
  ·
    refine ⟨169449337655508610829037145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225932450207344814438716193 169449337655508610829037145)
    ·
      refine ⟨127087003241631458121777859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169449337655508610829037145 127087003241631458121777859)
      ·
        refine ⟨190630504862447187182666789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127087003241631458121777859 190630504862447187182666789)
        ·
          refine ⟨35743219661708847596750023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190630504862447187182666789 35743219661708847596750023)
          ·
            refine ⟨53614829492563271395125035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35743219661708847596750023 53614829492563271395125035)
            ·
              refine ⟨80422244238844907092687553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53614829492563271395125035 80422244238844907092687553)
              ·
                refine ⟨60316683179133680319515665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80422244238844907092687553 60316683179133680319515665)
                ·
                  refine ⟨45237512384350260239636749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60316683179133680319515665 45237512384350260239636749)
                  ·
                    refine ⟨16964067144131347589863781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45237512384350260239636749 16964067144131347589863781)
                    ·
                      refine ⟨3180762589524627673099459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16964067144131347589863781 3180762589524627673099459)
                      ·
                        rfl

theorem cell23_6194513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_6194513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194513 prefixEnd_6194513 := by exact prefixLift 6194513
  have htrace : WordTrace (prefixWord ++ tailWord_6194513) baseStart_6194513 baseEnd_6194513 := by
    simpa [prefixWord, tailWord_6194513, baseEnd_6194513] using wordTrace_append hprefix tailTrace_6194513
  have hstable : (prefixWord ++ tailWord_6194513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194513).length < 2 ^ (prefixWord ++ tailWord_6194513).sum := by decide
  have hdescent : baseEnd_6194513 < baseStart_6194513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194517 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6194517 : Nat := 118140960795 + 6194517 * 2 ^ 59
def prefixEnd_6194517 : Nat := 4983230072969 + 3 ^ 40 * 6194517 * 2
def baseEnd_6194517 : Nat := 3180764643447245657449441

theorem tailTrace_6194517 : CollatzResearch.WordTrace tailWord_6194517 prefixEnd_6194517 3180764643447245657449441 := by
  unfold tailWord_6194517
  simp only [CollatzResearch.WordTrace]
  refine ⟨225932596099330323121861805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150621730732886882081241203 225932596099330323121861805)
  ·
    refine ⟨84724723537248871170698177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225932596099330323121861805 84724723537248871170698177)
    ·
      refine ⟨63543542652936653378023633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84724723537248871170698177 63543542652936653378023633)
      ·
        refine ⟨47657656989702490033517725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63543542652936653378023633 47657656989702490033517725)
        ·
          refine ⟨17871621371138433762569147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47657656989702490033517725 17871621371138433762569147)
          ·
            refine ⟨26807432056707650643853721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17871621371138433762569147 26807432056707650643853721)
            ·
              refine ⟨20105574042530737982890291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26807432056707650643853721 20105574042530737982890291)
              ·
                refine ⟨30158361063796106974335437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20105574042530737982890291 30158361063796106974335437)
                ·
                  refine ⟨11309385398923540115375789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30158361063796106974335437 11309385398923540115375789)
                  ·
                    refine ⟨4241019524596327543265921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11309385398923540115375789 4241019524596327543265921)
                    ·
                      refine ⟨3180764643447245657449441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241019524596327543265921 3180764643447245657449441)
                      ·
                        rfl

theorem cell23_6194517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6194517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194517 prefixEnd_6194517 := by exact prefixLift 6194517
  have htrace : WordTrace (prefixWord ++ tailWord_6194517) baseStart_6194517 baseEnd_6194517 := by
    simpa [prefixWord, tailWord_6194517, baseEnd_6194517] using wordTrace_append hprefix tailTrace_6194517
  have hstable : (prefixWord ++ tailWord_6194517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194517).length < 2 ^ (prefixWord ++ tailWord_6194517).sum := by decide
  have hdescent : baseEnd_6194517 < baseStart_6194517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194525 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6194525 : Nat := 118140960795 + 6194525 * 2 ^ 59
def prefixEnd_6194525 : Nat := 4983230072969 + 3 ^ 40 * 6194525 * 2
def baseEnd_6194525 : Nat := 3180768751292481626149405

theorem tailTrace_6194525 : CollatzResearch.WordTrace tailWord_6194525 prefixEnd_6194525 3180768751292481626149405 := by
  unfold tailWord_6194525
  simp only [CollatzResearch.WordTrace]
  refine ⟨225932887883301340488153029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150621925255534226992102019 225932887883301340488153029)
  ·
    refine ⟨42362416478119001341528693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225932887883301340488153029 42362416478119001341528693)
    ·
      refine ⟨3971476544823656375768315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42362416478119001341528693 3971476544823656375768315)
      ·
        refine ⟨5957214817235484563652473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971476544823656375768315 5957214817235484563652473)
        ·
          refine ⟨4467911112926613422739355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5957214817235484563652473 4467911112926613422739355)
          ·
            refine ⟨6701866669389920134109033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467911112926613422739355 6701866669389920134109033)
            ·
              refine ⟨5026400002042440100581775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6701866669389920134109033 5026400002042440100581775)
              ·
                refine ⟨7539600003063660150872663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026400002042440100581775 7539600003063660150872663)
                ·
                  refine ⟨11309400004595490226308995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539600003063660150872663 11309400004595490226308995)
                  ·
                    refine ⟨16964100006893235339463493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11309400004595490226308995 16964100006893235339463493)
                    ·
                      refine ⟨3180768751292481626149405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16964100006893235339463493 3180768751292481626149405)
                      ·
                        rfl

theorem cell23_6194525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6194525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194525 prefixEnd_6194525 := by exact prefixLift 6194525
  have htrace : WordTrace (prefixWord ++ tailWord_6194525) baseStart_6194525 baseEnd_6194525 := by
    simpa [prefixWord, tailWord_6194525, baseEnd_6194525] using wordTrace_append hprefix tailTrace_6194525
  have hstable : (prefixWord ++ tailWord_6194525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194525).length < 2 ^ (prefixWord ++ tailWord_6194525).sum := by decide
  have hdescent : baseEnd_6194525 < baseStart_6194525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194533 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6194533 : Nat := 118140960795 + 6194533 * 2 ^ 59
def prefixEnd_6194533 : Nat := 4983230072969 + 3 ^ 40 * 6194533 * 2
def baseEnd_6194533 : Nat := 3180772859137717594849367

theorem tailTrace_6194533 : CollatzResearch.WordTrace tailWord_6194533 prefixEnd_6194533 3180772859137717594849367 := by
  unfold tailWord_6194533
  simp only [CollatzResearch.WordTrace]
  refine ⟨225933179667272357854444253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150622119778181571902962835 225933179667272357854444253)
  ·
    refine ⟨84724942375227134195416595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225933179667272357854444253 84724942375227134195416595)
    ·
      refine ⟨127087413562840701293124893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84724942375227134195416595 127087413562840701293124893)
      ·
        refine ⟨47657780086065262984921835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127087413562840701293124893 47657780086065262984921835)
        ·
          refine ⟨71486670129097894477382753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47657780086065262984921835 71486670129097894477382753)
          ·
            refine ⟨53615002596823420858037065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71486670129097894477382753 53615002596823420858037065)
            ·
              refine ⟨40211251947617565643527799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53615002596823420858037065 40211251947617565643527799)
              ·
                refine ⟨60316877921426348465291699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40211251947617565643527799 60316877921426348465291699)
                ·
                  refine ⟨90475316882139522697937549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60316877921426348465291699 90475316882139522697937549)
                  ·
                    refine ⟨33928243830802321011726581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90475316882139522697937549 33928243830802321011726581)
                    ·
                      refine ⟨3180772859137717594849367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33928243830802321011726581 3180772859137717594849367)
                      ·
                        rfl

theorem cell23_6194533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6194533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194533 prefixEnd_6194533 := by exact prefixLift 6194533
  have htrace : WordTrace (prefixWord ++ tailWord_6194533) baseStart_6194533 baseEnd_6194533 := by
    simpa [prefixWord, tailWord_6194533, baseEnd_6194533] using wordTrace_append hprefix tailTrace_6194533
  have hstable : (prefixWord ++ tailWord_6194533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194533).length < 2 ^ (prefixWord ++ tailWord_6194533).sum := by decide
  have hdescent : baseEnd_6194533 < baseStart_6194533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194543 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_6194543 : Nat := 118140960795 + 6194543 * 2 ^ 59
def prefixEnd_6194543 : Nat := 4983230072969 + 3 ^ 40 * 6194543 * 2
def baseEnd_6194543 : Nat := 3180777993944262555724321

theorem tailTrace_6194543 : CollatzResearch.WordTrace tailWord_6194543 prefixEnd_6194543 3180777993944262555724321 := by
  unfold tailWord_6194543
  simp only [CollatzResearch.WordTrace]
  refine ⟨225933544397236129562308283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150622362931490753041538855 225933544397236129562308283)
  ·
    refine ⟨338900316595854194343462425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225933544397236129562308283 338900316595854194343462425)
    ·
      refine ⟨254175237446890645757596819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338900316595854194343462425 254175237446890645757596819)
      ·
        refine ⟨381262856170335968636395229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254175237446890645757596819 381262856170335968636395229)
        ·
          refine ⟨142973571063875988238648211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381262856170335968636395229 142973571063875988238648211)
          ·
            refine ⟨214460356595813982357972317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142973571063875988238648211 214460356595813982357972317)
            ·
              refine ⟨80422633723430243384239619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214460356595813982357972317 80422633723430243384239619)
              ·
                refine ⟨120633950585145365076359429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80422633723430243384239619 120633950585145365076359429)
                ·
                  refine ⟨22618865734714755951817393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120633950585145365076359429 22618865734714755951817393)
                  ·
                    refine ⟨16964149301036066963863045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22618865734714755951817393 16964149301036066963863045)
                    ·
                      refine ⟨3180777993944262555724321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16964149301036066963863045 3180777993944262555724321)
                      ·
                        rfl

theorem cell23_6194543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_6194543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194543 prefixEnd_6194543 := by exact prefixLift 6194543
  have htrace : WordTrace (prefixWord ++ tailWord_6194543) baseStart_6194543 baseEnd_6194543 := by
    simpa [prefixWord, tailWord_6194543, baseEnd_6194543] using wordTrace_append hprefix tailTrace_6194543
  have hstable : (prefixWord ++ tailWord_6194543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194543).length < 2 ^ (prefixWord ++ tailWord_6194543).sum := by decide
  have hdescent : baseEnd_6194543 < baseStart_6194543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194553 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 7]
def baseStart_6194553 : Nat := 118140960795 + 6194553 * 2 ^ 59
def prefixEnd_6194553 : Nat := 4983230072969 + 3 ^ 40 * 6194553 * 2
def baseEnd_6194553 : Nat := 353420347638978612955475

theorem tailTrace_6194553 : CollatzResearch.WordTrace tailWord_6194553 prefixEnd_6194553 353420347638978612955475 := by
  unfold tailWord_6194553
  simp only [CollatzResearch.WordTrace]
  refine ⟨225933909127199901270172313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150622606084799934180114875 225933909127199901270172313)
  ·
    refine ⟨169450431845399925952629235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225933909127199901270172313 169450431845399925952629235)
    ·
      refine ⟨254175647768099888928943853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169450431845399925952629235 254175647768099888928943853)
      ·
        refine ⟨95315867913037458348353945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254175647768099888928943853 95315867913037458348353945)
        ·
          refine ⟨71486900934778093761265459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95315867913037458348353945 71486900934778093761265459)
          ·
            refine ⟨107230351402167140641898189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71486900934778093761265459 107230351402167140641898189)
            ·
              refine ⟨40211381775812677740711821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107230351402167140641898189 40211381775812677740711821)
              ·
                refine ⟨15079268165929754152766933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40211381775812677740711821 15079268165929754152766933)
                ·
                  refine ⟨353420347638978612955475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15079268165929754152766933 353420347638978612955475)
                  ·
                    rfl

theorem cell23_6194553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_6194553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194553 prefixEnd_6194553 := by exact prefixLift 6194553
  have htrace : WordTrace (prefixWord ++ tailWord_6194553) baseStart_6194553 baseEnd_6194553 := by
    simpa [prefixWord, tailWord_6194553, baseEnd_6194553] using wordTrace_append hprefix tailTrace_6194553
  have hstable : (prefixWord ++ tailWord_6194553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194553).length < 2 ^ (prefixWord ++ tailWord_6194553).sum := by decide
  have hdescent : baseEnd_6194553 < baseStart_6194553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194558 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6194558 : Nat := 118140960795 + 6194558 * 2 ^ 59
def prefixEnd_6194558 : Nat := 4983230072969 + 3 ^ 40 * 6194558 * 2
def baseEnd_6194558 : Nat := 3180785696154079997036753

theorem tailTrace_6194558 : CollatzResearch.WordTrace tailWord_6194558 prefixEnd_6194558 3180785696154079997036753 := by
  unfold tailWord_6194558
  simp only [CollatzResearch.WordTrace]
  refine ⟨28241761436522723390513041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150622727661454524749402885 28241761436522723390513041)
  ·
    refine ⟨21181321077392042542884781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28241761436522723390513041 21181321077392042542884781)
    ·
      refine ⟨7942995404022015953581793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21181321077392042542884781 7942995404022015953581793)
      ·
        refine ⟨5957246553016511965186345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7942995404022015953581793 5957246553016511965186345)
        ·
          refine ⟨4467934914762383973889759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5957246553016511965186345 4467934914762383973889759)
          ·
            refine ⟨6701902372143575960834639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467934914762383973889759 6701902372143575960834639)
            ·
              refine ⟨10052853558215363941251959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701902372143575960834639 10052853558215363941251959)
              ·
                refine ⟨15079280337323045911877939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052853558215363941251959 15079280337323045911877939)
                ·
                  refine ⟨22618920505984568867816909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079280337323045911877939 22618920505984568867816909)
                  ·
                    refine ⟨8482095189744213325431341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22618920505984568867816909 8482095189744213325431341)
                    ·
                      refine ⟨3180785696154079997036753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482095189744213325431341 3180785696154079997036753)
                      ·
                        rfl

theorem cell23_6194558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6194558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194558 prefixEnd_6194558 := by exact prefixLift 6194558
  have htrace : WordTrace (prefixWord ++ tailWord_6194558) baseStart_6194558 baseEnd_6194558 := by
    simpa [prefixWord, tailWord_6194558, baseEnd_6194558] using wordTrace_append hprefix tailTrace_6194558
  have hstable : (prefixWord ++ tailWord_6194558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194558).length < 2 ^ (prefixWord ++ tailWord_6194558).sum := by decide
  have hdescent : baseEnd_6194558 < baseStart_6194558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194564 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_6194564 : Nat := 118140960795 + 6194564 * 2 ^ 59
def prefixEnd_6194564 : Nat := 4983230072969 + 3 ^ 40 * 6194564 * 2
def baseEnd_6194564 : Nat := 3180788777038006973561725

theorem tailTrace_6194564 : CollatzResearch.WordTrace tailWord_6194564 prefixEnd_6194564 3180788777038006973561725 := by
  unfold tailWord_6194564
  simp only [CollatzResearch.WordTrace]
  refine ⟨112967155165080025074411373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150622873553440033432548497 112967155165080025074411373)
  ·
    refine ⟨42362683186905009402904265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112967155165080025074411373 42362683186905009402904265)
    ·
      refine ⟨31772012390178757052178199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42362683186905009402904265 31772012390178757052178199)
      ·
        refine ⟨47658018585268135578267299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31772012390178757052178199 47658018585268135578267299)
        ·
          refine ⟨71487027877902203367400949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47658018585268135578267299 71487027877902203367400949)
          ·
            refine ⟨6701908863553331565693839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71487027877902203367400949 6701908863553331565693839)
            ·
              refine ⟨10052863295329997348540759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701908863553331565693839 10052863295329997348540759)
              ·
                refine ⟨15079294942994996022811139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052863295329997348540759 15079294942994996022811139)
                ·
                  refine ⟨22618942414492494034216709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079294942994996022811139 22618942414492494034216709)
                  ·
                    refine ⟨4241051702717342631415633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22618942414492494034216709 4241051702717342631415633)
                    ·
                      refine ⟨3180788777038006973561725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241051702717342631415633 3180788777038006973561725)
                      ·
                        rfl

theorem cell23_6194564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_6194564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194564 prefixEnd_6194564 := by exact prefixLift 6194564
  have htrace : WordTrace (prefixWord ++ tailWord_6194564) baseStart_6194564 baseEnd_6194564 := by
    simpa [prefixWord, tailWord_6194564, baseEnd_6194564] using wordTrace_append hprefix tailTrace_6194564
  have hstable : (prefixWord ++ tailWord_6194564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194564).length < 2 ^ (prefixWord ++ tailWord_6194564).sum := by decide
  have hdescent : baseEnd_6194564 < baseStart_6194564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194623 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_6194623 : Nat := 118140960795 + 6194623 * 2 ^ 59
def prefixEnd_6194623 : Nat := 4983230072969 + 3 ^ 40 * 6194623 * 2
def baseEnd_6194623 : Nat := 3180819072396622242723953

theorem tailTrace_6194623 : CollatzResearch.WordTrace tailWord_6194623 prefixEnd_6194623 3180819072396622242723953 := by
  unfold tailWord_6194623
  simp only [CollatzResearch.WordTrace]
  refine ⟨225936462236946303225220523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150624308157964202150147015 225936462236946303225220523)
  ·
    refine ⟨338904693355419454837830785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225936462236946303225220523 338904693355419454837830785)
    ·
      refine ⟨254178520016564591128373089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338904693355419454837830785 254178520016564591128373089)
      ·
        refine ⟨190633890012423443346279817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254178520016564591128373089 190633890012423443346279817)
        ·
          refine ⟨142975417509317582509709863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190633890012423443346279817 142975417509317582509709863)
          ·
            refine ⟨214463126263976373764564795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142975417509317582509709863 214463126263976373764564795)
            ·
              refine ⟨321694689395964560646847193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214463126263976373764564795 321694689395964560646847193)
              ·
                refine ⟨241271017046973420485135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321694689395964560646847193 241271017046973420485135395)
                ·
                  refine ⟨361906525570460130727703093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241271017046973420485135395 361906525570460130727703093)
                  ·
                    refine ⟨33928736772230637255722165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 361906525570460130727703093 33928736772230637255722165)
                    ·
                      refine ⟨3180819072396622242723953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33928736772230637255722165 3180819072396622242723953)
                      ·
                        rfl

theorem cell23_6194623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_6194623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194623 prefixEnd_6194623 := by exact prefixLift 6194623
  have htrace : WordTrace (prefixWord ++ tailWord_6194623) baseStart_6194623 baseEnd_6194623 := by
    simpa [prefixWord, tailWord_6194623, baseEnd_6194623] using wordTrace_append hprefix tailTrace_6194623
  have hstable : (prefixWord ++ tailWord_6194623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194623).length < 2 ^ (prefixWord ++ tailWord_6194623).sum := by decide
  have hdescent : baseEnd_6194623 < baseStart_6194623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194633 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_6194633 : Nat := 118140960795 + 6194633 * 2 ^ 59
def prefixEnd_6194633 : Nat := 4983230072969 + 3 ^ 40 * 6194633 * 2
def baseEnd_6194633 : Nat := 3180824207203167203598907

theorem tailTrace_6194633 : CollatzResearch.WordTrace tailWord_6194633 prefixEnd_6194633 3180824207203167203598907 := by
  unfold tailWord_6194633
  simp only [CollatzResearch.WordTrace]
  refine ⟨225936826966910074933084553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150624551311273383288723035 225936826966910074933084553)
  ·
    refine ⟨169452620225182556199813415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225936826966910074933084553 169452620225182556199813415)
    ·
      refine ⟨254178930337773834299720123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169452620225182556199813415 254178930337773834299720123)
      ·
        refine ⟨381268395506660751449580185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254178930337773834299720123 381268395506660751449580185)
        ·
          refine ⟨285951296629995563587185139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381268395506660751449580185 285951296629995563587185139)
          ·
            refine ⟨428926944944993345380777709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285951296629995563587185139 428926944944993345380777709)
            ·
              refine ⟨160847604354372504517791641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428926944944993345380777709 160847604354372504517791641)
              ·
                refine ⟨120635703265779378388343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160847604354372504517791641 120635703265779378388343731)
                ·
                  refine ⟨180953554898669067582515597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120635703265779378388343731 180953554898669067582515597)
                  ·
                    refine ⟨67857583087000900343443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180953554898669067582515597 67857583087000900343443349)
                    ·
                      refine ⟨3180824207203167203598907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67857583087000900343443349 3180824207203167203598907)
                      ·
                        rfl

theorem cell23_6194633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_6194633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194633 prefixEnd_6194633 := by exact prefixLift 6194633
  have htrace : WordTrace (prefixWord ++ tailWord_6194633) baseStart_6194633 baseEnd_6194633 := by
    simpa [prefixWord, tailWord_6194633, baseEnd_6194633] using wordTrace_append hprefix tailTrace_6194633
  have hstable : (prefixWord ++ tailWord_6194633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194633).length < 2 ^ (prefixWord ++ tailWord_6194633).sum := by decide
  have hdescent : baseEnd_6194633 < baseStart_6194633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194640 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_6194640 : Nat := 118140960795 + 6194640 * 2 ^ 59
def prefixEnd_6194640 : Nat := 4983230072969 + 3 ^ 40 * 6194640 * 2
def baseEnd_6194640 : Nat := 3180827801567748676211375

theorem tailTrace_6194640 : CollatzResearch.WordTrace tailWord_6194640 prefixEnd_6194640 3180827801567748676211375 := by
  unfold tailWord_6194640
  simp only [CollatzResearch.WordTrace]
  refine ⟨112968541138942357564294687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150624721518589810085726249 112968541138942357564294687)
  ·
    refine ⟨169452811708413536346442031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112968541138942357564294687 169452811708413536346442031)
    ·
      refine ⟨254179217562620304519663047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169452811708413536346442031 254179217562620304519663047)
      ·
        refine ⟨381268826343930456779494571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254179217562620304519663047 381268826343930456779494571)
        ·
          refine ⟨571903239515895685169241857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381268826343930456779494571 571903239515895685169241857)
          ·
            refine ⟨428927429636921763876931393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571903239515895685169241857 428927429636921763876931393)
            ·
              refine ⟨321695572227691322907698545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428927429636921763876931393 321695572227691322907698545)
              ·
                refine ⟨241271679170768492180773909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321695572227691322907698545 241271679170768492180773909)
                ·
                  refine ⟨11309609961129773070973777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241271679170768492180773909 11309609961129773070973777)
                  ·
                    refine ⟨8482207470847329803230333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11309609961129773070973777 8482207470847329803230333)
                    ·
                      refine ⟨3180827801567748676211375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482207470847329803230333 3180827801567748676211375)
                      ·
                        rfl

theorem cell23_6194640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_6194640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194640 prefixEnd_6194640 := by exact prefixLift 6194640
  have htrace : WordTrace (prefixWord ++ tailWord_6194640) baseStart_6194640 baseEnd_6194640 := by
    simpa [prefixWord, tailWord_6194640, baseEnd_6194640] using wordTrace_append hprefix tailTrace_6194640
  have hstable : (prefixWord ++ tailWord_6194640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194640).length < 2 ^ (prefixWord ++ tailWord_6194640).sum := by decide
  have hdescent : baseEnd_6194640 < baseStart_6194640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194657 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_6194657 : Nat := 118140960795 + 6194657 * 2 ^ 59
def prefixEnd_6194657 : Nat := 4983230072969 + 3 ^ 40 * 6194657 * 2
def baseEnd_6194657 : Nat := 3180836530738875109698797

theorem tailTrace_6194657 : CollatzResearch.WordTrace tailWord_6194657 prefixEnd_6194657 3180836530738875109698797 := by
  unfold tailWord_6194657
  simp only [CollatzResearch.WordTrace]
  refine ⟨225937702318823127031958225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150625134879215418021305483 225937702318823127031958225)
  ·
    refine ⟨169453276739117345273968669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225937702318823127031958225 169453276739117345273968669)
    ·
      refine ⟨63544978777169004477738251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169453276739117345273968669 63544978777169004477738251)
      ·
        refine ⟨95317468165753506716607377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63544978777169004477738251 95317468165753506716607377)
        ·
          refine ⟨71488101124315130037455533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95317468165753506716607377 71488101124315130037455533)
          ·
            refine ⟨26808037921618173764045825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71488101124315130037455533 26808037921618173764045825)
            ·
              refine ⟨20106028441213630323034369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26808037921618173764045825 20106028441213630323034369)
              ·
                refine ⟨15079521330910222742275777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20106028441213630323034369 15079521330910222742275777)
                ·
                  refine ⟨11309640998182667056706833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15079521330910222742275777 11309640998182667056706833)
                  ·
                    refine ⟨8482230748637000292530125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11309640998182667056706833 8482230748637000292530125)
                    ·
                      refine ⟨3180836530738875109698797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482230748637000292530125 3180836530738875109698797)
                      ·
                        rfl

theorem cell23_6194657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_6194657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194657 prefixEnd_6194657 := by exact prefixLift 6194657
  have htrace : WordTrace (prefixWord ++ tailWord_6194657) baseStart_6194657 baseEnd_6194657 := by
    simpa [prefixWord, tailWord_6194657, baseEnd_6194657] using wordTrace_append hprefix tailTrace_6194657
  have hstable : (prefixWord ++ tailWord_6194657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194657).length < 2 ^ (prefixWord ++ tailWord_6194657).sum := by decide
  have hdescent : baseEnd_6194657 < baseStart_6194657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194664 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 1, 4]
def baseStart_6194664 : Nat := 118140960795 + 6194664 * 2 ^ 59
def prefixEnd_6194664 : Nat := 4983230072969 + 3 ^ 40 * 6194664 * 2
def baseEnd_6194664 : Nat := 1060280041701152194103755

theorem tailTrace_6194664 : CollatzResearch.WordTrace tailWord_6194664 prefixEnd_6194664 1060280041701152194103755 := by
  unfold tailWord_6194664
  simp only [CollatzResearch.WordTrace]
  refine ⟨112968978814898883613731523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150625305086531844818308697 112968978814898883613731523)
  ·
    refine ⟨169453468222348325420597285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112968978814898883613731523 169453468222348325420597285)
    ·
      refine ⟨31772525291690311016361991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169453468222348325420597285 31772525291690311016361991)
      ·
        refine ⟨47658787937535466524542987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31772525291690311016361991 47658787937535466524542987)
        ·
          refine ⟨71488181906303199786814481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47658787937535466524542987 71488181906303199786814481)
          ·
            refine ⟨53616136429727399840110861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71488181906303199786814481 53616136429727399840110861)
            ·
              refine ⟨20106051161147774940041573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53616136429727399840110861 20106051161147774940041573)
              ·
                refine ⟨3769884592715207801257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20106051161147774940041573 3769884592715207801257795)
                ·
                  refine ⟨5654826889072811701886693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769884592715207801257795 5654826889072811701886693)
                  ·
                    refine ⟨1060280041701152194103755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5654826889072811701886693 1060280041701152194103755)
                    ·
                      rfl

theorem cell23_6194664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_6194664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194664 prefixEnd_6194664 := by exact prefixLift 6194664
  have htrace : WordTrace (prefixWord ++ tailWord_6194664) baseStart_6194664 baseEnd_6194664 := by
    simpa [prefixWord, tailWord_6194664, baseEnd_6194664] using wordTrace_append hprefix tailTrace_6194664
  have hstable : (prefixWord ++ tailWord_6194664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194664).length < 2 ^ (prefixWord ++ tailWord_6194664).sum := by decide
  have hdescent : baseEnd_6194664 < baseStart_6194664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194697 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 5, 2]
def baseStart_6194697 : Nat := 118140960795 + 6194697 * 2 ^ 59
def prefixEnd_6194697 : Nat := 4983230072969 + 3 ^ 40 * 6194697 * 2
def baseEnd_6194697 : Nat := 3180857069965054953198613

theorem tailTrace_6194697 : CollatzResearch.WordTrace tailWord_6194697 prefixEnd_6194697 3180857069965054953198613 := by
  unfold tailWord_6194697
  simp only [CollatzResearch.WordTrace]
  refine ⟨225939161238678213863414345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150626107492452142575609563 225939161238678213863414345)
  ·
    refine ⟨169454370929008660397560759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225939161238678213863414345 169454370929008660397560759)
    ·
      refine ⟨254181556393512990596341139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169454370929008660397560759 254181556393512990596341139)
      ·
        refine ⟨381272334590269485894511709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254181556393512990596341139 381272334590269485894511709)
        ·
          refine ⟨142977125471351057210441891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381272334590269485894511709 142977125471351057210441891)
          ·
            refine ⟨214465688207026585815662837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142977125471351057210441891 214465688207026585815662837)
            ·
              refine ⟨20106158269408742420218391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214465688207026585815662837 20106158269408742420218391)
              ·
                refine ⟨30159237404113113630327587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20106158269408742420218391 30159237404113113630327587)
                ·
                  refine ⟨45238856106169670445491381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30159237404113113630327587 45238856106169670445491381)
                  ·
                    refine ⟨4241142759953406604264817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45238856106169670445491381 4241142759953406604264817)
                    ·
                      refine ⟨3180857069965054953198613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241142759953406604264817 3180857069965054953198613)
                      ·
                        rfl

theorem cell23_6194697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5, 2].length) (baseStart_6194697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194697 prefixEnd_6194697 := by exact prefixLift 6194697
  have htrace : WordTrace (prefixWord ++ tailWord_6194697) baseStart_6194697 baseEnd_6194697 := by
    simpa [prefixWord, tailWord_6194697, baseEnd_6194697] using wordTrace_append hprefix tailTrace_6194697
  have hstable : (prefixWord ++ tailWord_6194697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194697).length < 2 ^ (prefixWord ++ tailWord_6194697).sum := by decide
  have hdescent : baseEnd_6194697 < baseStart_6194697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194707 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 1, 5]
def baseStart_6194707 : Nat := 118140960795 + 6194707 * 2 ^ 59
def prefixEnd_6194707 : Nat := 4983230072969 + 3 ^ 40 * 6194707 * 2
def baseEnd_6194707 : Nat := 1060287401590533304691189

theorem tailTrace_6194707 : CollatzResearch.WordTrace tailWord_6194707 prefixEnd_6194707 1060287401590533304691189 := by
  unfold tailWord_6194707
  simp only [CollatzResearch.WordTrace]
  refine ⟨225939525968641985571278375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150626350645761323714185583 225939525968641985571278375)
  ·
    refine ⟨338909288952962978356917563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225939525968641985571278375 338909288952962978356917563)
    ·
      refine ⟨508363933429444467535376345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338909288952962978356917563 508363933429444467535376345)
      ·
        refine ⟨381272950072083350651532259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508363933429444467535376345 381272950072083350651532259)
        ·
          refine ⟨571909425108125025977298389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381272950072083350651532259 571909425108125025977298389)
          ·
            refine ⟨13404127150971680296342931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 571909425108125025977298389 13404127150971680296342931)
            ·
              refine ⟨20106190726457520444514397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13404127150971680296342931 20106190726457520444514397)
              ·
                refine ⟨7539821522421570166692899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20106190726457520444514397 7539821522421570166692899)
                ·
                  refine ⟨11309732283632355250039349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539821522421570166692899 11309732283632355250039349)
                  ·
                    refine ⟨1060287401590533304691189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11309732283632355250039349 1060287401590533304691189)
                    ·
                      rfl

theorem cell23_6194707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 5].length) (baseStart_6194707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194707 prefixEnd_6194707 := by exact prefixLift 6194707
  have htrace : WordTrace (prefixWord ++ tailWord_6194707) baseStart_6194707 baseEnd_6194707 := by
    simpa [prefixWord, tailWord_6194707, baseEnd_6194707] using wordTrace_append hprefix tailTrace_6194707
  have hstable : (prefixWord ++ tailWord_6194707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194707).length < 2 ^ (prefixWord ++ tailWord_6194707).sum := by decide
  have hdescent : baseEnd_6194707 < baseStart_6194707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194721 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6194721 : Nat := 118140960795 + 6194721 * 2 ^ 59
def prefixEnd_6194721 : Nat := 4983230072969 + 3 ^ 40 * 6194721 * 2
def baseEnd_6194721 : Nat := 3180869393500762859298503

theorem tailTrace_6194721 : CollatzResearch.WordTrace tailWord_6194721 prefixEnd_6194721 3180869393500762859298503 := by
  unfold tailWord_6194721
  simp only [CollatzResearch.WordTrace]
  refine ⟨225940036590591265962288017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150626691060394177308192011 225940036590591265962288017)
  ·
    refine ⟨169455027442943449471716013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225940036590591265962288017 169455027442943449471716013)
    ·
      refine ⟨63545635291103793551893505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169455027442943449471716013 63545635291103793551893505)
      ·
        refine ⟨47659226468327845163920129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63545635291103793551893505 47659226468327845163920129)
        ·
          refine ⟨35744419851245883872940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47659226468327845163920129 35744419851245883872940097)
          ·
            refine ⟨26808314888434412904705073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35744419851245883872940097 26808314888434412904705073)
            ·
              refine ⟨20106236166325809678528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26808314888434412904705073 20106236166325809678528805)
              ·
                refine ⟨3769919281186089314724151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20106236166325809678528805 3769919281186089314724151)
                ·
                  refine ⟨5654878921779133972086227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769919281186089314724151 5654878921779133972086227)
                  ·
                    refine ⟨8482318382668700958129341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654878921779133972086227 8482318382668700958129341)
                    ·
                      refine ⟨3180869393500762859298503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482318382668700958129341 3180869393500762859298503)
                      ·
                        rfl

theorem cell23_6194721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6194721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194721 prefixEnd_6194721 := by exact prefixLift 6194721
  have htrace : WordTrace (prefixWord ++ tailWord_6194721) baseStart_6194721 baseEnd_6194721 := by
    simpa [prefixWord, tailWord_6194721, baseEnd_6194721] using wordTrace_append hprefix tailTrace_6194721
  have hstable : (prefixWord ++ tailWord_6194721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194721).length < 2 ^ (prefixWord ++ tailWord_6194721).sum := by decide
  have hdescent : baseEnd_6194721 < baseStart_6194721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194744 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_6194744 : Nat := 118140960795 + 6194744 * 2 ^ 59
def prefixEnd_6194744 : Nat := 4983230072969 + 3 ^ 40 * 6194744 * 2
def baseEnd_6194744 : Nat := 3180881203555816269310897

theorem tailTrace_6194744 : CollatzResearch.WordTrace tailWord_6194744 prefixEnd_6194744 3180881203555816269310897 := by
  unfold tailWord_6194744
  simp only [CollatzResearch.WordTrace]
  refine ⟨112970437734753970445187643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150627250313005293926916857 112970437734753970445187643)
  ·
    refine ⟨169455656602130955667781465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112970437734753970445187643 169455656602130955667781465)
    ·
      refine ⟨127091742451598216750836099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169455656602130955667781465 127091742451598216750836099)
      ·
        refine ⟨190637613677397325126254149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127091742451598216750836099 190637613677397325126254149)
        ·
          refine ⟨35744552564511998461172653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190637613677397325126254149 35744552564511998461172653)
          ·
            refine ⟨13404207211691999422939745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35744552564511998461172653 13404207211691999422939745)
            ·
              refine ⟨10053155408768999567204809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13404207211691999422939745 10053155408768999567204809)
              ·
                refine ⟨7539866556576749675403607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10053155408768999567204809 7539866556576749675403607)
                ·
                  refine ⟨11309799834865124513105411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539866556576749675403607 11309799834865124513105411)
                  ·
                    refine ⟨16964699752297686769658117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11309799834865124513105411 16964699752297686769658117)
                    ·
                      refine ⟨3180881203555816269310897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16964699752297686769658117 3180881203555816269310897)
                      ·
                        rfl

theorem cell23_6194744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_6194744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194744 prefixEnd_6194744 := by exact prefixLift 6194744
  have htrace : WordTrace (prefixWord ++ tailWord_6194744) baseStart_6194744 baseEnd_6194744 := by
    simpa [prefixWord, tailWord_6194744, baseEnd_6194744] using wordTrace_append hprefix tailTrace_6194744
  have hstable : (prefixWord ++ tailWord_6194744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194744).length < 2 ^ (prefixWord ++ tailWord_6194744).sum := by decide
  have hdescent : baseEnd_6194744 < baseStart_6194744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194764 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6194764 : Nat := 118140960795 + 6194764 * 2 ^ 59
def prefixEnd_6194764 : Nat := 4983230072969 + 3 ^ 40 * 6194764 * 2
def baseEnd_6194764 : Nat := 3180891473168906191060805

theorem tailTrace_6194764 : CollatzResearch.WordTrace tailWord_6194764 prefixEnd_6194764 3180891473168906191060805 := by
  unfold tailWord_6194764
  simp only [CollatzResearch.WordTrace]
  refine ⟨112970802464717742153051673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150627736619623656204068897 112970802464717742153051673)
  ·
    refine ⟨84728101848538306614788755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112970802464717742153051673 84728101848538306614788755)
    ·
      refine ⟨127092152772807459922183133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84728101848538306614788755 127092152772807459922183133)
      ·
        refine ⟨47659557289802797470818675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127092152772807459922183133 47659557289802797470818675)
        ·
          refine ⟨71489335934704196206228013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47659557289802797470818675 71489335934704196206228013)
          ·
            refine ⟨26808500975514073577335505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71489335934704196206228013 26808500975514073577335505)
            ·
              refine ⟨20106375731635555183001629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26808500975514073577335505 20106375731635555183001629)
              ·
                refine ⟨7539890899363333193625611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20106375731635555183001629 7539890899363333193625611)
                ·
                  refine ⟨11309836349044999790438417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539890899363333193625611 11309836349044999790438417)
                  ·
                    refine ⟨8482377261783749842828813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11309836349044999790438417 8482377261783749842828813)
                    ·
                      refine ⟨3180891473168906191060805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482377261783749842828813 3180891473168906191060805)
                      ·
                        rfl

theorem cell23_6194764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6194764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194764 prefixEnd_6194764 := by exact prefixLift 6194764
  have htrace : WordTrace (prefixWord ++ tailWord_6194764) baseStart_6194764 baseEnd_6194764 := by
    simpa [prefixWord, tailWord_6194764, baseEnd_6194764] using wordTrace_append hprefix tailTrace_6194764
  have hstable : (prefixWord ++ tailWord_6194764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194764).length < 2 ^ (prefixWord ++ tailWord_6194764).sum := by decide
  have hdescent : baseEnd_6194764 < baseStart_6194764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194798 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_6194798 : Nat := 118140960795 + 6194798 * 2 ^ 59
def prefixEnd_6194798 : Nat := 4983230072969 + 3 ^ 40 * 6194798 * 2
def baseEnd_6194798 : Nat := 3180908931511159058035649

theorem tailTrace_6194798 : CollatzResearch.WordTrace tailWord_6194798 prefixEnd_6194798 3180908931511159058035649 := by
  unfold tailWord_6194798
  simp only [CollatzResearch.WordTrace]
  refine ⟨28242855626414038514105131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150628563340874872075227365 28242855626414038514105131)
  ·
    refine ⟨42364283439621057771157697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28242855626414038514105131 42364283439621057771157697)
    ·
      refine ⟨31773212579715793328368273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42364283439621057771157697 31773212579715793328368273)
      ·
        refine ⟨23829909434786844996276205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31773212579715793328368273 23829909434786844996276205)
        ·
          refine ⟨8936216038045066873603577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23829909434786844996276205 8936216038045066873603577)
          ·
            refine ⟨6702162028533800155202683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8936216038045066873603577 6702162028533800155202683)
            ·
              refine ⟨10053243042800700232804025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702162028533800155202683 10053243042800700232804025)
              ·
                refine ⟨7539932282100525174603019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10053243042800700232804025 7539932282100525174603019)
                ·
                  refine ⟨11309898423150787761904529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539932282100525174603019 11309898423150787761904529)
                  ·
                    refine ⟨8482423817363090821428397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11309898423150787761904529 8482423817363090821428397)
                    ·
                      refine ⟨3180908931511159058035649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482423817363090821428397 3180908931511159058035649)
                      ·
                        rfl

theorem cell23_6194798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_6194798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194798 prefixEnd_6194798 := by exact prefixLift 6194798
  have htrace : WordTrace (prefixWord ++ tailWord_6194798) baseStart_6194798 baseEnd_6194798 := by
    simpa [prefixWord, tailWord_6194798, baseEnd_6194798] using wordTrace_append hprefix tailTrace_6194798
  have hstable : (prefixWord ++ tailWord_6194798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194798).length < 2 ^ (prefixWord ++ tailWord_6194798).sum := by decide
  have hdescent : baseEnd_6194798 < baseStart_6194798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194810 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_6194810 : Nat := 118140960795 + 6194810 * 2 ^ 59
def prefixEnd_6194810 : Nat := 4983230072969 + 3 ^ 40 * 6194810 * 2
def baseEnd_6194810 : Nat := 1060305031093004337028531

theorem tailTrace_6194810 : CollatzResearch.WordTrace tailWord_6194810 prefixEnd_6194810 1060305031093004337028531 := by
  unfold tailWord_6194810
  simp only [CollatzResearch.WordTrace]
  refine ⟨56485820671817208540569471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150628855124845889441518589 56485820671817208540569471)
  ·
    refine ⟨84728731007725812810854207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56485820671817208540569471 84728731007725812810854207)
    ·
      refine ⟨127093096511588719216281311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84728731007725812810854207 127093096511588719216281311)
      ·
        refine ⟨190639644767383078824421967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127093096511588719216281311 190639644767383078824421967)
        ·
          refine ⟨285959467151074618236632951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190639644767383078824421967 285959467151074618236632951)
          ·
            refine ⟨428939200726611927354949427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285959467151074618236632951 428939200726611927354949427)
            ·
              refine ⟨643408801089917891032424141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428939200726611927354949427 643408801089917891032424141)
              ·
                refine ⟨241278300408719209137159053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643408801089917891032424141 241278300408719209137159053)
                ·
                  refine ⟨90479362653269703426434645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241278300408719209137159053 90479362653269703426434645)
                  ·
                    refine ⟨1060305031093004337028531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90479362653269703426434645 1060305031093004337028531)
                    ·
                      rfl

theorem cell23_6194810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_6194810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194810 prefixEnd_6194810 := by exact prefixLift 6194810
  have htrace : WordTrace (prefixWord ++ tailWord_6194810) baseStart_6194810 baseEnd_6194810 := by
    simpa [prefixWord, tailWord_6194810, baseEnd_6194810] using wordTrace_append hprefix tailTrace_6194810
  have hstable : (prefixWord ++ tailWord_6194810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194810).length < 2 ^ (prefixWord ++ tailWord_6194810).sum := by decide
  have hdescent : baseEnd_6194810 < baseStart_6194810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194844 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6194844 : Nat := 118140960795 + 6194844 * 2 ^ 59
def prefixEnd_6194844 : Nat := 4983230072969 + 3 ^ 40 * 6194844 * 2
def baseEnd_6194844 : Nat := 1060310850540421959353479

theorem tailTrace_6194844 : CollatzResearch.WordTrace tailWord_6194844 prefixEnd_6194844 1060310850540421959353479 := by
  unfold tailWord_6194844
  simp only [CollatzResearch.WordTrace]
  refine ⟨112972261384572828984507793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150629681846097105312677057 112972261384572828984507793)
  ·
    refine ⟨84729196038429621738380845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112972261384572828984507793 84729196038429621738380845)
    ·
      refine ⟨31773448514411108151892817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84729196038429621738380845 31773448514411108151892817)
      ·
        refine ⟨23830086385808331113919613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31773448514411108151892817 23830086385808331113919613)
        ·
          refine ⟨8936282394678124167719855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23830086385808331113919613 8936282394678124167719855)
          ·
            refine ⟨13404423592017186251579783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936282394678124167719855 13404423592017186251579783)
            ·
              refine ⟨20106635388025779377369675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13404423592017186251579783 20106635388025779377369675)
              ·
                refine ⟨30159953082038669066054513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20106635388025779377369675 30159953082038669066054513)
                ·
                  refine ⟨22619964811529001799540885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30159953082038669066054513 22619964811529001799540885)
                  ·
                    refine ⟨1060310850540421959353479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22619964811529001799540885 1060310850540421959353479)
                    ·
                      rfl

theorem cell23_6194844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6194844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194844 prefixEnd_6194844 := by exact prefixLift 6194844
  have htrace : WordTrace (prefixWord ++ tailWord_6194844) baseStart_6194844 baseEnd_6194844 := by
    simpa [prefixWord, tailWord_6194844, baseEnd_6194844] using wordTrace_append hprefix tailTrace_6194844
  have hstable : (prefixWord ++ tailWord_6194844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194844).length < 2 ^ (prefixWord ++ tailWord_6194844).sum := by decide
  have hdescent : baseEnd_6194844 < baseStart_6194844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194851 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 2, 2, 2]
def baseStart_6194851 : Nat := 118140960795 + 6194851 * 2 ^ 59
def prefixEnd_6194851 : Nat := 4983230072969 + 3 ^ 40 * 6194851 * 2
def baseEnd_6194851 : Nat := 3180936145985847350672905

theorem tailTrace_6194851 : CollatzResearch.WordTrace tailWord_6194851 prefixEnd_6194851 3180936145985847350672905 := by
  unfold tailWord_6194851
  simp only [CollatzResearch.WordTrace]
  refine ⟨225944778080120298164520407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150629852053413532109680271 225944778080120298164520407)
  ·
    refine ⟨338917167120180447246780611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225944778080120298164520407 338917167120180447246780611)
    ·
      refine ⟨508375750680270670870170917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338917167120180447246780611 508375750680270670870170917)
      ·
        refine ⟨95320453252550750788157047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 508375750680270670870170917 95320453252550750788157047)
        ·
          refine ⟨142980679878826126182235571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95320453252550750788157047 142980679878826126182235571)
          ·
            refine ⟨214471019818239189273353357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142980679878826126182235571 214471019818239189273353357)
            ·
              refine ⟨80426632431839695977507509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214471019818239189273353357 80426632431839695977507509)
              ·
                refine ⟨7539996790484971497891329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80426632431839695977507509 7539996790484971497891329)
                ·
                  refine ⟨5654997592863728623418497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539996790484971497891329 5654997592863728623418497)
                  ·
                    refine ⟨4241248194647796467563873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5654997592863728623418497 4241248194647796467563873)
                    ·
                      refine ⟨3180936145985847350672905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241248194647796467563873 3180936145985847350672905)
                      ·
                        rfl

theorem cell23_6194851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_6194851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194851 prefixEnd_6194851 := by exact prefixLift 6194851
  have htrace : WordTrace (prefixWord ++ tailWord_6194851) baseStart_6194851 baseEnd_6194851 := by
    simpa [prefixWord, tailWord_6194851, baseEnd_6194851] using wordTrace_append hprefix tailTrace_6194851
  have hstable : (prefixWord ++ tailWord_6194851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194851).length < 2 ^ (prefixWord ++ tailWord_6194851).sum := by decide
  have hdescent : baseEnd_6194851 < baseStart_6194851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194867 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3]
def baseStart_6194867 : Nat := 118140960795 + 6194867 * 2 ^ 59
def prefixEnd_6194867 : Nat := 4983230072969 + 3 ^ 40 * 6194867 * 2
def baseEnd_6194867 : Nat := 3180944361676319288072831

theorem tailTrace_6194867 : CollatzResearch.WordTrace tailWord_6194867 prefixEnd_6194867 3180944361676319288072831 := by
  unfold tailWord_6194867
  simp only [CollatzResearch.WordTrace]
  refine ⟨225945361648062332897102855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150630241098708221931401903 225945361648062332897102855)
  ·
    refine ⟨338918042472093499345654283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225945361648062332897102855 338918042472093499345654283)
    ·
      refine ⟨508377063708140249018481425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338918042472093499345654283 508377063708140249018481425)
      ·
        refine ⟨381282797781105186763861069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508377063708140249018481425 381282797781105186763861069)
        ·
          refine ⟨142981049167914445036447901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381282797781105186763861069 142981049167914445036447901)
          ·
            refine ⟨53617893437967916888667963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142981049167914445036447901 53617893437967916888667963)
            ·
              refine ⟨80426840156951875333001945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53617893437967916888667963 80426840156951875333001945)
              ·
                refine ⟨60320130117713906499751459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80426840156951875333001945 60320130117713906499751459)
                ·
                  refine ⟨90480195176570859749627189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60320130117713906499751459 90480195176570859749627189)
                  ·
                    refine ⟨8482518297803518101527549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90480195176570859749627189 8482518297803518101527549)
                    ·
                      refine ⟨3180944361676319288072831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482518297803518101527549 3180944361676319288072831)
                      ·
                        rfl

theorem cell23_6194867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_6194867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194867 prefixEnd_6194867 := by exact prefixLift 6194867
  have htrace : WordTrace (prefixWord ++ tailWord_6194867) baseStart_6194867 baseEnd_6194867 := by
    simpa [prefixWord, tailWord_6194867, baseEnd_6194867] using wordTrace_append hprefix tailTrace_6194867
  have hstable : (prefixWord ++ tailWord_6194867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194867).length < 2 ^ (prefixWord ++ tailWord_6194867).sum := by decide
  have hdescent : baseEnd_6194867 < baseStart_6194867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194874 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_6194874 : Nat := 118140960795 + 6194874 * 2 ^ 59
def prefixEnd_6194874 : Nat := 4983230072969 + 3 ^ 40 * 6194874 * 2
def baseEnd_6194874 : Nat := 353438661782322306742811

theorem tailTrace_6194874 : CollatzResearch.WordTrace tailWord_6194874 prefixEnd_6194874 353438661782322306742811 := by
  unfold tailWord_6194874
  simp only [CollatzResearch.WordTrace]
  refine ⟨56486404239759243273151919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150630411306024648728405117 56486404239759243273151919)
  ·
    refine ⟨84729606359638864909727879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56486404239759243273151919 84729606359638864909727879)
    ·
      refine ⟨127094409539458297364591819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84729606359638864909727879 127094409539458297364591819)
      ·
        refine ⟨190641614309187446046887729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127094409539458297364591819 190641614309187446046887729)
        ·
          refine ⟨142981210731890584535165797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190641614309187446046887729 142981210731890584535165797)
          ·
            refine ⟨26808977012229484600343587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142981210731890584535165797 26808977012229484600343587)
            ·
              refine ⟨40213465518344226900515381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26808977012229484600343587 40213465518344226900515381)
              ·
                refine ⟨3770012392344771271923317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40213465518344226900515381 3770012392344771271923317)
                ·
                  refine ⟨353438661782322306742811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3770012392344771271923317 353438661782322306742811)
                  ·
                    rfl

theorem cell23_6194874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_6194874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194874 prefixEnd_6194874 := by exact prefixLift 6194874
  have htrace : WordTrace (prefixWord ++ tailWord_6194874) baseStart_6194874 baseEnd_6194874 := by
    simpa [prefixWord, tailWord_6194874, baseEnd_6194874] using wordTrace_append hprefix tailTrace_6194874
  have hstable : (prefixWord ++ tailWord_6194874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194874).length < 2 ^ (prefixWord ++ tailWord_6194874).sum := by decide
  have hdescent : baseEnd_6194874 < baseStart_6194874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194884 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6194884 : Nat := 118140960795 + 6194884 * 2 ^ 59
def prefixEnd_6194884 : Nat := 4983230072969 + 3 ^ 40 * 6194884 * 2
def baseEnd_6194884 : Nat := 3180953090847445721560253

theorem tailTrace_6194884 : CollatzResearch.WordTrace tailWord_6194884 prefixEnd_6194884 3180953090847445721560253 := by
  unfold tailWord_6194884
  simp only [CollatzResearch.WordTrace]
  refine ⟨112972990844500372400235853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150630654459333829866981137 112972990844500372400235853)
  ·
    refine ⟨42364871566687639650088445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112972990844500372400235853 42364871566687639650088445)
    ·
      refine ⟨15886826837507864868783167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42364871566687639650088445 15886826837507864868783167)
      ·
        refine ⟨23830240256261797303174751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15886826837507864868783167 23830240256261797303174751)
        ·
          refine ⟨35745360384392695954762127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830240256261797303174751 35745360384392695954762127)
          ·
            refine ⟨53618040576589043932143191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35745360384392695954762127 53618040576589043932143191)
            ·
              refine ⟨80427060864883565898214787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53618040576589043932143191 80427060864883565898214787)
              ·
                refine ⟨120640591297325348847322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80427060864883565898214787 120640591297325348847322181)
                ·
                  refine ⟨22620110868248502908872909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120640591297325348847322181 22620110868248502908872909)
                  ·
                    refine ⟨8482541575593188590827341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22620110868248502908872909 8482541575593188590827341)
                    ·
                      refine ⟨3180953090847445721560253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482541575593188590827341 3180953090847445721560253)
                      ·
                        rfl

theorem cell23_6194884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6194884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194884 prefixEnd_6194884 := by exact prefixLift 6194884
  have htrace : WordTrace (prefixWord ++ tailWord_6194884) baseStart_6194884 baseEnd_6194884 := by
    simpa [prefixWord, tailWord_6194884, baseEnd_6194884] using wordTrace_append hprefix tailTrace_6194884
  have hstable : (prefixWord ++ tailWord_6194884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194884).length < 2 ^ (prefixWord ++ tailWord_6194884).sum := by decide
  have hdescent : baseEnd_6194884 < baseStart_6194884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194887 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 4, 5]
def baseStart_6194887 : Nat := 118140960795 + 6194887 * 2 ^ 59
def prefixEnd_6194887 : Nat := 4983230072969 + 3 ^ 40 * 6194887 * 2
def baseEnd_6194887 : Nat := 1060318210429803069940913

theorem tailTrace_6194887 : CollatzResearch.WordTrace tailWord_6194887 prefixEnd_6194887 1060318210429803069940913 := by
  unfold tailWord_6194887
  simp only [CollatzResearch.WordTrace]
  refine ⟨225946091107989876312830915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150630727405326584208553943 225946091107989876312830915)
  ·
    refine ⟨338919136661984814469246373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225946091107989876312830915 338919136661984814469246373)
    ·
      refine ⟨63547338124122152712983695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338919136661984814469246373 63547338124122152712983695)
      ·
        refine ⟨95321007186183229069475543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63547338124122152712983695 95321007186183229069475543)
        ·
          refine ⟨142981510779274843604213315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95321007186183229069475543 142981510779274843604213315)
          ·
            refine ⟨214472266168912265406319973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142981510779274843604213315 214472266168912265406319973)
            ·
              refine ⟨40213549906671049763684995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214472266168912265406319973 40213549906671049763684995)
              ·
                refine ⟨60320324860006574645527493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40213549906671049763684995 60320324860006574645527493)
                ·
                  refine ⟨11310060911251232746036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60320324860006574645527493 11310060911251232746036405)
                  ·
                    refine ⟨1060318210429803069940913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11310060911251232746036405 1060318210429803069940913)
                    ·
                      rfl

theorem cell23_6194887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_6194887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194887 prefixEnd_6194887 := by exact prefixLift 6194887
  have htrace : WordTrace (prefixWord ++ tailWord_6194887) baseStart_6194887 baseEnd_6194887 := by
    simpa [prefixWord, tailWord_6194887, baseEnd_6194887] using wordTrace_append hprefix tailTrace_6194887
  have hstable : (prefixWord ++ tailWord_6194887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194887).length < 2 ^ (prefixWord ++ tailWord_6194887).sum := by decide
  have hdescent : baseEnd_6194887 < baseStart_6194887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194902 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6194902 : Nat := 118140960795 + 6194902 * 2 ^ 59
def prefixEnd_6194902 : Nat := 4983230072969 + 3 ^ 40 * 6194902 * 2
def baseEnd_6194902 : Nat := 3180962333499226651135171

theorem tailTrace_6194902 : CollatzResearch.WordTrace tailWord_6194902 prefixEnd_6194902 3180962333499226651135171 := by
  unfold tailWord_6194902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121664887683470867164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150631092135290355916417973 14121664887683470867164185)
  ·
    refine ⟨10591248665762603150373139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14121664887683470867164185 10591248665762603150373139)
    ·
      refine ⟨15886872998643904725559709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591248665762603150373139 15886872998643904725559709)
      ·
        refine ⟨5957577374491464272084891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15886872998643904725559709 5957577374491464272084891)
        ·
          refine ⟨8936366061737196408127337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957577374491464272084891 8936366061737196408127337)
          ·
            refine ⟨6702274546302897306095503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8936366061737196408127337 6702274546302897306095503)
            ·
              refine ⟨10053411819454345959143255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702274546302897306095503 10053411819454345959143255)
              ·
                refine ⟨15080117729181518938714883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10053411819454345959143255 15080117729181518938714883)
                ·
                  refine ⟨22620176593772278408072325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15080117729181518938714883 22620176593772278408072325)
                  ·
                    refine ⟨4241283111332302201513561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22620176593772278408072325 4241283111332302201513561)
                    ·
                      refine ⟨3180962333499226651135171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241283111332302201513561 3180962333499226651135171)
                      ·
                        rfl

theorem cell23_6194902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6194902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194902 prefixEnd_6194902 := by exact prefixLift 6194902
  have htrace : WordTrace (prefixWord ++ tailWord_6194902) baseStart_6194902 baseEnd_6194902 := by
    simpa [prefixWord, tailWord_6194902, baseEnd_6194902] using wordTrace_append hprefix tailTrace_6194902
  have hstable : (prefixWord ++ tailWord_6194902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194902).length < 2 ^ (prefixWord ++ tailWord_6194902).sum := by decide
  have hdescent : baseEnd_6194902 < baseStart_6194902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194917 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_6194917 : Nat := 118140960795 + 6194917 * 2 ^ 59
def prefixEnd_6194917 : Nat := 4983230072969 + 3 ^ 40 * 6194917 * 2
def baseEnd_6194917 : Nat := 1060323345236348030815867

theorem tailTrace_6194917 : CollatzResearch.WordTrace tailWord_6194917 prefixEnd_6194917 1060323345236348030815867 := by
  unfold tailWord_6194917
  simp only [CollatzResearch.WordTrace]
  refine ⟨225947185297881191436423005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150631456865254127624282003 225947185297881191436423005)
  ·
    refine ⟨84730194486705446788658627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225947185297881191436423005 84730194486705446788658627)
    ·
      refine ⟨127095291730058170182987941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84730194486705446788658627 127095291730058170182987941)
      ·
        refine ⟨23830367199385906909310239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127095291730058170182987941 23830367199385906909310239)
        ·
          refine ⟨35745550799078860363965359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830367199385906909310239 35745550799078860363965359)
          ·
            refine ⟨53618326198618290545948039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35745550799078860363965359 53618326198618290545948039)
            ·
              refine ⟨80427489297927435818922059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53618326198618290545948039 80427489297927435818922059)
              ·
                refine ⟨120641233946891153728383089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80427489297927435818922059 120641233946891153728383089)
                ·
                  refine ⟨90480925460168365296287317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120641233946891153728383089 90480925460168365296287317)
                  ·
                    refine ⟨1060323345236348030815867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90480925460168365296287317 1060323345236348030815867)
                    ·
                      rfl

theorem cell23_6194917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_6194917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194917 prefixEnd_6194917 := by exact prefixLift 6194917
  have htrace : WordTrace (prefixWord ++ tailWord_6194917) baseStart_6194917 baseEnd_6194917 := by
    simpa [prefixWord, tailWord_6194917, baseEnd_6194917] using wordTrace_append hprefix tailTrace_6194917
  have hstable : (prefixWord ++ tailWord_6194917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194917).length < 2 ^ (prefixWord ++ tailWord_6194917).sum := by decide
  have hdescent : baseEnd_6194917 < baseStart_6194917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194924 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_6194924 : Nat := 118140960795 + 6194924 * 2 ^ 59
def prefixEnd_6194924 : Nat := 4983230072969 + 3 ^ 40 * 6194924 * 2
def baseEnd_6194924 : Nat := 3180973630073625565060069

theorem tailTrace_6194924 : CollatzResearch.WordTrace tailWord_6194924 prefixEnd_6194924 3180973630073625565060069 := by
  unfold tailWord_6194924
  simp only [CollatzResearch.WordTrace]
  refine ⟨112973720304427915815963913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150631627072570554421285217 112973720304427915815963913)
  ·
    refine ⟨84730290228320936861972935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112973720304427915815963913 84730290228320936861972935)
    ·
      refine ⟨127095435342481405292959403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84730290228320936861972935 127095435342481405292959403)
      ·
        refine ⟨190643153013722107939439105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127095435342481405292959403 190643153013722107939439105)
        ·
          refine ⟨142982364760291580954579329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190643153013722107939439105 142982364760291580954579329)
          ·
            refine ⟨107236773570218685715934497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142982364760291580954579329 107236773570218685715934497)
            ·
              refine ⟨80427580177664014286950873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107236773570218685715934497 80427580177664014286950873)
              ·
                refine ⟨60320685133248010715213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80427580177664014286950873 60320685133248010715213155)
                ·
                  refine ⟨90481027699872016072819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60320685133248010715213155 90481027699872016072819733)
                  ·
                    refine ⟨4241298173431500753413425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90481027699872016072819733 4241298173431500753413425)
                    ·
                      refine ⟨3180973630073625565060069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241298173431500753413425 3180973630073625565060069)
                      ·
                        rfl

theorem cell23_6194924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_6194924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194924 prefixEnd_6194924 := by exact prefixLift 6194924
  have htrace : WordTrace (prefixWord ++ tailWord_6194924) baseStart_6194924 baseEnd_6194924 := by
    simpa [prefixWord, tailWord_6194924, baseEnd_6194924] using wordTrace_append hprefix tailTrace_6194924
  have hstable : (prefixWord ++ tailWord_6194924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194924).length < 2 ^ (prefixWord ++ tailWord_6194924).sum := by decide
  have hdescent : baseEnd_6194924 < baseStart_6194924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194944 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_6194944 : Nat := 118140960795 + 6194944 * 2 ^ 59
def prefixEnd_6194944 : Nat := 4983230072969 + 3 ^ 40 * 6194944 * 2
def baseEnd_6194944 : Nat := 3180983899686715486809977

theorem tailTrace_6194944 : CollatzResearch.WordTrace tailWord_6194944 prefixEnd_6194944 3180983899686715486809977 := by
  unfold tailWord_6194944
  simp only [CollatzResearch.WordTrace]
  refine ⟨112974085034391687523827943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150632113379188916698437257 112974085034391687523827943)
  ·
    refine ⟨169461127551587531285741915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112974085034391687523827943 169461127551587531285741915)
    ·
      refine ⟨254191691327381296928612873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169461127551587531285741915 254191691327381296928612873)
      ·
        refine ⟨190643768495535972696459655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254191691327381296928612873 190643768495535972696459655)
        ·
          refine ⟨285965652743303959044689483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190643768495535972696459655 285965652743303959044689483)
          ·
            refine ⟨428948479114955938567034225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285965652743303959044689483 428948479114955938567034225)
            ·
              refine ⟨321711359336216953925275669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428948479114955938567034225 321711359336216953925275669)
              ·
                refine ⟨15080219968885169715247297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321711359336216953925275669 15080219968885169715247297)
                ·
                  refine ⟨11310164976663877286435473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15080219968885169715247297 11310164976663877286435473)
                  ·
                    refine ⟨8482623732497907964826605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11310164976663877286435473 8482623732497907964826605)
                    ·
                      refine ⟨3180983899686715486809977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482623732497907964826605 3180983899686715486809977)
                      ·
                        rfl

theorem cell23_6194944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_6194944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194944 prefixEnd_6194944 := by exact prefixLift 6194944
  have htrace : WordTrace (prefixWord ++ tailWord_6194944) baseStart_6194944 baseEnd_6194944 := by
    simpa [prefixWord, tailWord_6194944, baseEnd_6194944] using wordTrace_append hprefix tailTrace_6194944
  have hstable : (prefixWord ++ tailWord_6194944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194944).length < 2 ^ (prefixWord ++ tailWord_6194944).sum := by decide
  have hdescent : baseEnd_6194944 < baseStart_6194944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194947 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 8]
def baseStart_6194947 : Nat := 118140960795 + 6194947 * 2 ^ 59
def prefixEnd_6194947 : Nat := 4983230072969 + 3 ^ 40 * 6194947 * 2
def baseEnd_6194947 : Nat := 353442826680964330563607

theorem tailTrace_6194947 : CollatzResearch.WordTrace tailWord_6194947 prefixEnd_6194947 353442826680964330563607 := by
  unfold tailWord_6194947
  simp only [CollatzResearch.WordTrace]
  refine ⟨225948279487772506560015095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150632186325181671040010063 225948279487772506560015095)
  ·
    refine ⟨338922419231658759840022643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225948279487772506560015095 338922419231658759840022643)
    ·
      refine ⟨508383628847488139760033965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338922419231658759840022643 508383628847488139760033965)
      ·
        refine ⟨190643860817808052410012737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508383628847488139760033965 190643860817808052410012737)
        ·
          refine ⟨142982895613356039307509553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190643860817808052410012737 142982895613356039307509553)
          ·
            refine ⟨107237171710017029480632165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142982895613356039307509553 107237171710017029480632165)
            ·
              refine ⟨20106969695628193027618531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107237171710017029480632165 20106969695628193027618531)
              ·
                refine ⟨30160454543442289541427797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20106969695628193027618531 30160454543442289541427797)
                ·
                  refine ⟨353442826680964330563607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30160454543442289541427797 353442826680964330563607)
                  ·
                    rfl

theorem cell23_6194947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 8].length) (baseStart_6194947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194947 prefixEnd_6194947 := by exact prefixLift 6194947
  have htrace : WordTrace (prefixWord ++ tailWord_6194947) baseStart_6194947 baseEnd_6194947 := by
    simpa [prefixWord, tailWord_6194947, baseEnd_6194947] using wordTrace_append hprefix tailTrace_6194947
  have hstable : (prefixWord ++ tailWord_6194947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194947).length < 2 ^ (prefixWord ++ tailWord_6194947).sum := by decide
  have hdescent : baseEnd_6194947 < baseStart_6194947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6194998 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_6194998 : Nat := 118140960795 + 6194998 * 2 ^ 59
def prefixEnd_6194998 : Nat := 4983230072969 + 3 ^ 40 * 6194998 * 2
def baseEnd_6194998 : Nat := 353445736404673141726081

theorem tailTrace_6194998 : CollatzResearch.WordTrace tailWord_6194998 prefixEnd_6194998 353445736404673141726081 := by
  unfold tailWord_6194998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14121883725661733891882603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150633426407058494846747765 14121883725661733891882603)
  ·
    refine ⟨21182825588492600837823905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14121883725661733891882603 21182825588492600837823905)
    ·
      refine ⟨15887119191369450628367929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21182825588492600837823905 15887119191369450628367929)
      ·
        refine ⟨11915339393527087971275947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15887119191369450628367929 11915339393527087971275947)
        ·
          refine ⟨17873009090290631956913921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11915339393527087971275947 17873009090290631956913921)
          ·
            refine ⟨13404756817717973967685441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17873009090290631956913921 13404756817717973967685441)
            ·
              refine ⟨10053567613288480475764081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13404756817717973967685441 10053567613288480475764081)
              ·
                refine ⟨7540175709966360356823061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10053567613288480475764081 7540175709966360356823061)
                ·
                  refine ⟨353445736404673141726081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7540175709966360356823061 353445736404673141726081)
                  ·
                    rfl

theorem cell23_6194998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_6194998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6194998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6194998 prefixEnd_6194998 := by exact prefixLift 6194998
  have htrace : WordTrace (prefixWord ++ tailWord_6194998) baseStart_6194998 baseEnd_6194998 := by
    simpa [prefixWord, tailWord_6194998, baseEnd_6194998] using wordTrace_append hprefix tailTrace_6194998
  have hstable : (prefixWord ++ tailWord_6194998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6194998).length < 2 ^ (prefixWord ++ tailWord_6194998).sum := by decide
  have hdescent : baseEnd_6194998 < baseStart_6194998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6194998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195024 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_6195024 : Nat := 118140960795 + 6195024 * 2 ^ 59
def prefixEnd_6195024 : Nat := 4983230072969 + 3 ^ 40 * 6195024 * 2
def baseEnd_6195024 : Nat := 1060341659379691724603203

theorem tailTrace_6195024 : CollatzResearch.WordTrace tailWord_6195024 prefixEnd_6195024 1060341659379691724603203 := by
  unfold tailWord_6195024
  simp only [CollatzResearch.WordTrace]
  refine ⟨112975543954246774355284063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150634058605662365807045417 112975543954246774355284063)
  ·
    refine ⟨169463315931370161532926095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112975543954246774355284063 169463315931370161532926095)
    ·
      refine ⟨254194973897055242299389143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169463315931370161532926095 254194973897055242299389143)
      ·
        refine ⟨381292460845582863449083715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254194973897055242299389143 381292460845582863449083715)
        ·
          refine ⟨571938691268374295173625573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381292460845582863449083715 571938691268374295173625573)
          ·
            refine ⟨107238504612820180345054795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571938691268374295173625573 107238504612820180345054795)
            ·
              refine ⟨160857756919230270517582193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107238504612820180345054795 160857756919230270517582193)
              ·
                refine ⟨120643317689422702888186645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160857756919230270517582193 120643317689422702888186645)
                ·
                  refine ⟨5655155516691689197883749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120643317689422702888186645 5655155516691689197883749)
                  ·
                    refine ⟨1060341659379691724603203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5655155516691689197883749 1060341659379691724603203)
                    ·
                      rfl

theorem cell23_6195024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_6195024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195024 prefixEnd_6195024 := by exact prefixLift 6195024
  have htrace : WordTrace (prefixWord ++ tailWord_6195024) baseStart_6195024 baseEnd_6195024 := by
    simpa [prefixWord, tailWord_6195024, baseEnd_6195024] using wordTrace_append hprefix tailTrace_6195024
  have hstable : (prefixWord ++ tailWord_6195024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195024).length < 2 ^ (prefixWord ++ tailWord_6195024).sum := by decide
  have hdescent : baseEnd_6195024 < baseStart_6195024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195042 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6195042 : Nat := 118140960795 + 6195042 * 2 ^ 59
def prefixEnd_6195042 : Nat := 4983230072969 + 3 ^ 40 * 6195042 * 2
def baseEnd_6195042 : Nat := 3181034220790856103384527

theorem tailTrace_6195042 : CollatzResearch.WordTrace tailWord_6195042 prefixEnd_6195042 3181034220790856103384527 := by
  unfold tailWord_6195042
  simp only [CollatzResearch.WordTrace]
  refine ⟨56487936105607084446180845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150634496281618891856482253 56487936105607084446180845)
  ·
    refine ⟨21182976039602656667317817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56487936105607084446180845 21182976039602656667317817)
    ·
      refine ⟨15887232029701992500488363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21182976039602656667317817 15887232029701992500488363)
      ·
        refine ⟨23830848044552988750732545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887232029701992500488363 23830848044552988750732545)
        ·
          refine ⟨17873136033414741563049409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23830848044552988750732545 17873136033414741563049409)
          ·
            refine ⟨13404852025061056172287057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17873136033414741563049409 13404852025061056172287057)
            ·
              refine ⟨10053639018795792129215293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13404852025061056172287057 10053639018795792129215293)
              ·
                refine ⟨3770114632048422048455735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10053639018795792129215293 3770114632048422048455735)
                ·
                  refine ⟨5655171948072633072683603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770114632048422048455735 5655171948072633072683603)
                  ·
                    refine ⟨8482757922108949609025405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655171948072633072683603 8482757922108949609025405)
                    ·
                      refine ⟨3181034220790856103384527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482757922108949609025405 3181034220790856103384527)
                      ·
                        rfl

theorem cell23_6195042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6195042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195042 prefixEnd_6195042 := by exact prefixLift 6195042
  have htrace : WordTrace (prefixWord ++ tailWord_6195042) baseStart_6195042 baseEnd_6195042 := by
    simpa [prefixWord, tailWord_6195042, baseEnd_6195042] using wordTrace_append hprefix tailTrace_6195042
  have hstable : (prefixWord ++ tailWord_6195042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195042).length < 2 ^ (prefixWord ++ tailWord_6195042).sum := by decide
  have hdescent : baseEnd_6195042 < baseStart_6195042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195048 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6195048 : Nat := 118140960795 + 6195048 * 2 ^ 59
def prefixEnd_6195048 : Nat := 4983230072969 + 3 ^ 40 * 6195048 * 2
def baseEnd_6195048 : Nat := 3181037301674783079909499

theorem tailTrace_6195048 : CollatzResearch.WordTrace tailWord_6195048 prefixEnd_6195048 3181037301674783079909499 := by
  unfold tailWord_6195048
  simp only [CollatzResearch.WordTrace]
  refine ⟨112975981630203300404720899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150634642173604400539627865 112975981630203300404720899)
  ·
    refine ⟨169463972445304950607081349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112975981630203300404720899 169463972445304950607081349)
    ·
      refine ⟨31774494833494678238827753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169463972445304950607081349 31774494833494678238827753)
      ·
        refine ⟨23830871125121008679120815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31774494833494678238827753 23830871125121008679120815)
        ·
          refine ⟨35746306687681513018681223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830871125121008679120815 35746306687681513018681223)
          ·
            refine ⟨53619460031522269528021835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35746306687681513018681223 53619460031522269528021835)
            ·
              refine ⟨80429190047283404292032753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53619460031522269528021835 80429190047283404292032753)
              ·
                refine ⟨60321892535462553219024565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80429190047283404292032753 60321892535462553219024565)
                ·
                  refine ⟨5655177425199614364283553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60321892535462553219024565 5655177425199614364283553)
                  ·
                    refine ⟨4241383068899710773212665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5655177425199614364283553 4241383068899710773212665)
                    ·
                      refine ⟨3181037301674783079909499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241383068899710773212665 3181037301674783079909499)
                      ·
                        rfl

theorem cell23_6195048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6195048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195048 prefixEnd_6195048 := by exact prefixLift 6195048
  have htrace : WordTrace (prefixWord ++ tailWord_6195048) baseStart_6195048 baseEnd_6195048 := by
    simpa [prefixWord, tailWord_6195048, baseEnd_6195048] using wordTrace_append hprefix tailTrace_6195048
  have hstable : (prefixWord ++ tailWord_6195048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195048).length < 2 ^ (prefixWord ++ tailWord_6195048).sum := by decide
  have hdescent : baseEnd_6195048 < baseStart_6195048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195065 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 1, 2, 2]
def baseStart_6195065 : Nat := 118140960795 + 6195065 * 2 ^ 59
def prefixEnd_6195065 : Nat := 4983230072969 + 3 ^ 40 * 6195065 * 2
def baseEnd_6195065 : Nat := 3181046030845909513396921

theorem tailTrace_6195065 : CollatzResearch.WordTrace tailWord_6195065 prefixEnd_6195065 3181046030845909513396921 := by
  unfold tailWord_6195065
  simp only [CollatzResearch.WordTrace]
  refine ⟨225952583301345012712810649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150635055534230008475207099 225952583301345012712810649)
  ·
    refine ⟨169464437476008759534607987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225952583301345012712810649 169464437476008759534607987)
    ·
      refine ⟨254196656214013139301911981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169464437476008759534607987 254196656214013139301911981)
      ·
        refine ⟨95323746080254927238216993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254196656214013139301911981 95323746080254927238216993)
        ·
          refine ⟨71492809560191195428662745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95323746080254927238216993 71492809560191195428662745)
          ·
            refine ⟨53619607170143396571497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71492809560191195428662745 53619607170143396571497059)
            ·
              refine ⟨80429410755215094857245589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53619607170143396571497059 80429410755215094857245589)
              ·
                refine ⟨3770128629150707571433387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80429410755215094857245589 3770128629150707571433387)
                ·
                  refine ⟨5655192943726061357150081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770128629150707571433387 5655192943726061357150081)
                  ·
                    refine ⟨4241394707794546017862561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5655192943726061357150081 4241394707794546017862561)
                    ·
                      refine ⟨3181046030845909513396921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241394707794546017862561 3181046030845909513396921)
                      ·
                        rfl

theorem cell23_6195065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_6195065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195065 prefixEnd_6195065 := by exact prefixLift 6195065
  have htrace : WordTrace (prefixWord ++ tailWord_6195065) baseStart_6195065 baseEnd_6195065 := by
    simpa [prefixWord, tailWord_6195065, baseEnd_6195065] using wordTrace_append hprefix tailTrace_6195065
  have hstable : (prefixWord ++ tailWord_6195065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195065).length < 2 ^ (prefixWord ++ tailWord_6195065).sum := by decide
  have hdescent : baseEnd_6195065 < baseStart_6195065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195091 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 7, 3, 2]
def baseStart_6195091 : Nat := 118140960795 + 6195091 * 2 ^ 59
def prefixEnd_6195091 : Nat := 4983230072969 + 3 ^ 40 * 6195091 * 2
def baseEnd_6195091 : Nat := 3181059381342926411671801

theorem tailTrace_6195091 : CollatzResearch.WordTrace tailWord_6195091 prefixEnd_6195091 3181059381342926411671801 := by
  unfold tailWord_6195091
  simp only [CollatzResearch.WordTrace]
  refine ⟨225953531599250819153257127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150635687732833879435504751 225953531599250819153257127)
  ·
    refine ⟨338930297398876228729885691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225953531599250819153257127 338930297398876228729885691)
    ·
      refine ⟨508395446098314343094828537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338930297398876228729885691 508395446098314343094828537)
      ·
        refine ⟨381296584573735757321121403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508395446098314343094828537 381296584573735757321121403)
        ·
          refine ⟨571944876860603635981682105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381296584573735757321121403 571944876860603635981682105)
          ·
            refine ⟨428958657645452726986261579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571944876860603635981682105 428958657645452726986261579)
            ·
              refine ⟨643437986468179090479392369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428958657645452726986261579 643437986468179090479392369)
              ·
                refine ⟨482578489851134317859544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643437986468179090479392369 482578489851134317859544277)
                ·
                  refine ⟨11310433355885960574833069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 482578489851134317859544277 11310433355885960574833069)
                  ·
                    refine ⟨4241412508457235215562401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11310433355885960574833069 4241412508457235215562401)
                    ·
                      refine ⟨3181059381342926411671801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241412508457235215562401 3181059381342926411671801)
                      ·
                        rfl

theorem cell23_6195091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3, 2].length) (baseStart_6195091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195091 prefixEnd_6195091 := by exact prefixLift 6195091
  have htrace : WordTrace (prefixWord ++ tailWord_6195091) baseStart_6195091 baseEnd_6195091 := by
    simpa [prefixWord, tailWord_6195091, baseEnd_6195091] using wordTrace_append hprefix tailTrace_6195091
  have hstable : (prefixWord ++ tailWord_6195091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195091).length < 2 ^ (prefixWord ++ tailWord_6195091).sum := by decide
  have hdescent : baseEnd_6195091 < baseStart_6195091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195098 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6195098 : Nat := 118140960795 + 6195098 * 2 ^ 59
def prefixEnd_6195098 : Nat := 4983230072969 + 3 ^ 40 * 6195098 * 2
def baseEnd_6195098 : Nat := 3181062975707507884284269

theorem tailTrace_6195098 : CollatzResearch.WordTrace tailWord_6195098 prefixEnd_6195098 3181062975707507884284269 := by
  unfold tailWord_6195098
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488446727556364837190487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150635857940150306232507965 56488446727556364837190487)
  ·
    refine ⟨84732670091334547255785731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56488446727556364837190487 84732670091334547255785731)
    ·
      refine ⟨127099005137001820883678597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84732670091334547255785731 127099005137001820883678597)
      ·
        refine ⟨23831063463187841415689737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127099005137001820883678597 23831063463187841415689737)
        ·
          refine ⟨17873297597390881061767303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23831063463187841415689737 17873297597390881061767303)
          ·
            refine ⟨26809946396086321592650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17873297597390881061767303 26809946396086321592650955)
            ·
              refine ⟨40214919594129482388976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26809946396086321592650955 40214919594129482388976433)
              ·
                refine ⟨30161189695597111791732325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40214919594129482388976433 30161189695597111791732325)
                ·
                  refine ⟨5655223067924458460949811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30161189695597111791732325 5655223067924458460949811)
                  ·
                    refine ⟨8482834601886687691424717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655223067924458460949811 8482834601886687691424717)
                    ·
                      refine ⟨3181062975707507884284269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482834601886687691424717 3181062975707507884284269)
                      ·
                        rfl

theorem cell23_6195098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6195098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195098 prefixEnd_6195098 := by exact prefixLift 6195098
  have htrace : WordTrace (prefixWord ++ tailWord_6195098) baseStart_6195098 baseEnd_6195098 := by
    simpa [prefixWord, tailWord_6195098, baseEnd_6195098] using wordTrace_append hprefix tailTrace_6195098
  have hstable : (prefixWord ++ tailWord_6195098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195098).length < 2 ^ (prefixWord ++ tailWord_6195098).sum := by decide
  have hdescent : baseEnd_6195098 < baseStart_6195098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195104 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6195104 : Nat := 118140960795 + 6195104 * 2 ^ 59
def prefixEnd_6195104 : Nat := 4983230072969 + 3 ^ 40 * 6195104 * 2
def baseEnd_6195104 : Nat := 3181066056591434860809241

theorem tailTrace_6195104 : CollatzResearch.WordTrace tailWord_6195104 prefixEnd_6195104 3181066056591434860809241 := by
  unfold tailWord_6195104
  simp only [CollatzResearch.WordTrace]
  refine ⟨112977002874101861186740183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150636003832135814915653577 112977002874101861186740183)
  ·
    refine ⟨169465504311152791780110275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112977002874101861186740183 169465504311152791780110275)
    ·
      refine ⟨254198256466729187670165413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169465504311152791780110275 254198256466729187670165413)
      ·
        refine ⟨47662173087511722688156015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254198256466729187670165413 47662173087511722688156015)
        ·
          refine ⟨71493259631267584032234023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47662173087511722688156015 71493259631267584032234023)
          ·
            refine ⟨107239889446901376048351035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71493259631267584032234023 107239889446901376048351035)
            ·
              refine ⟨160859834170352064072526553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107239889446901376048351035 160859834170352064072526553)
              ·
                refine ⟨120644875627764048054394915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160859834170352064072526553 120644875627764048054394915)
                ·
                  refine ⟨180967313441646072081592373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120644875627764048054394915 180967313441646072081592373)
                  ·
                    refine ⟨16965685635154319257649285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180967313441646072081592373 16965685635154319257649285)
                    ·
                      refine ⟨3181066056591434860809241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16965685635154319257649285 3181066056591434860809241)
                      ·
                        rfl

theorem cell23_6195104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6195104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195104 prefixEnd_6195104 := by exact prefixLift 6195104
  have htrace : WordTrace (prefixWord ++ tailWord_6195104) baseStart_6195104 baseEnd_6195104 := by
    simpa [prefixWord, tailWord_6195104, baseEnd_6195104] using wordTrace_append hprefix tailTrace_6195104
  have hstable : (prefixWord ++ tailWord_6195104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195104).length < 2 ^ (prefixWord ++ tailWord_6195104).sum := by decide
  have hdescent : baseEnd_6195104 < baseStart_6195104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195132 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6195132 : Nat := 118140960795 + 6195132 * 2 ^ 59
def prefixEnd_6195132 : Nat := 4983230072969 + 3 ^ 40 * 6195132 * 2
def baseEnd_6195132 : Nat := 3181080434049760751259113

theorem tailTrace_6195132 : CollatzResearch.WordTrace tailWord_6195132 prefixEnd_6195132 3181080434049760751259113 := by
  unfold tailWord_6195132
  simp only [CollatzResearch.WordTrace]
  refine ⟨112977513496051141577749825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150636684661401522103666433 112977513496051141577749825)
  ·
    refine ⟨84733135122038356183312369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112977513496051141577749825 84733135122038356183312369)
    ·
      refine ⟨63549851341528767137484277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84733135122038356183312369 63549851341528767137484277)
      ·
        refine ⟨5957798563268321919139151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63549851341528767137484277 5957798563268321919139151)
        ·
          refine ⟨8936697844902482878708727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957798563268321919139151 8936697844902482878708727)
          ·
            refine ⟨13405046767353724318063091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936697844902482878708727 13405046767353724318063091)
            ·
              refine ⟨20107570151030586477094637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13405046767353724318063091 20107570151030586477094637)
              ·
                refine ⟨7540338806636469928910489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20107570151030586477094637 7540338806636469928910489)
                ·
                  refine ⟨5655254104977352446682867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7540338806636469928910489 5655254104977352446682867)
                  ·
                    refine ⟨8482881157466028670024301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655254104977352446682867 8482881157466028670024301)
                    ·
                      refine ⟨3181080434049760751259113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8482881157466028670024301 3181080434049760751259113)
                      ·
                        rfl

theorem cell23_6195132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6195132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195132 prefixEnd_6195132 := by exact prefixLift 6195132
  have htrace : WordTrace (prefixWord ++ tailWord_6195132) baseStart_6195132 baseEnd_6195132 := by
    simpa [prefixWord, tailWord_6195132, baseEnd_6195132] using wordTrace_append hprefix tailTrace_6195132
  have hstable : (prefixWord ++ tailWord_6195132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195132).length < 2 ^ (prefixWord ++ tailWord_6195132).sum := by decide
  have hdescent : baseEnd_6195132 < baseStart_6195132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195178 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_6195178 : Nat := 118140960795 + 6195178 * 2 ^ 59
def prefixEnd_6195178 : Nat := 4983230072969 + 3 ^ 40 * 6195178 * 2
def baseEnd_6195178 : Nat := 353456006017763063475989

theorem tailTrace_6195178 : CollatzResearch.WordTrace tailWord_6195178 prefixEnd_6195178 353456006017763063475989 := by
  unfold tailWord_6195178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56489176187483908252918547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150637803166623755341116125 56489176187483908252918547)
  ·
    refine ⟨84733764281225862379377821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56489176187483908252918547 84733764281225862379377821)
    ·
      refine ⟨31775161605459698392266683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84733764281225862379377821 31775161605459698392266683)
      ·
        refine ⟨47662742408189547588400025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31775161605459698392266683 47662742408189547588400025)
        ·
          refine ⟨35747056806142160691300019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47662742408189547588400025 35747056806142160691300019)
          ·
            refine ⟨53620585209213241036950029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35747056806142160691300019 53620585209213241036950029)
            ·
              refine ⟨20107719453454965388856261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53620585209213241036950029 20107719453454965388856261)
              ·
                refine ⟨3770197397522806010410549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20107719453454965388856261 3770197397522806010410549)
                ·
                  refine ⟨353456006017763063475989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3770197397522806010410549 353456006017763063475989)
                  ·
                    rfl

theorem cell23_6195178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_6195178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195178 prefixEnd_6195178 := by exact prefixLift 6195178
  have htrace : WordTrace (prefixWord ++ tailWord_6195178) baseStart_6195178 baseEnd_6195178 := by
    simpa [prefixWord, tailWord_6195178, baseEnd_6195178] using wordTrace_append hprefix tailTrace_6195178
  have hstable : (prefixWord ++ tailWord_6195178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195178).length < 2 ^ (prefixWord ++ tailWord_6195178).sum := by decide
  have hdescent : baseEnd_6195178 < baseStart_6195178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195211 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_6195211 : Nat := 118140960795 + 6195211 * 2 ^ 59
def prefixEnd_6195211 : Nat := 4983230072969 + 3 ^ 40 * 6195211 * 2
def baseEnd_6195211 : Nat := 3181120999021465942171249

theorem tailTrace_6195211 : CollatzResearch.WordTrace tailWord_6195211 prefixEnd_6195211 3181120999021465942171249 := by
  unfold tailWord_6195211
  simp only [CollatzResearch.WordTrace]
  refine ⟨225957908358816079647625487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150638605572544053098416991 225957908358816079647625487)
  ·
    refine ⟨338936862538224119471438231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225957908358816079647625487 338936862538224119471438231)
    ·
      refine ⟨508405293807336179207157347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338936862538224119471438231 508405293807336179207157347)
      ·
        refine ⟨762607940711004268810736021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508405293807336179207157347 762607940711004268810736021)
        ·
          refine ⟨35747247220828325100503251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 762607940711004268810736021 35747247220828325100503251)
          ·
            refine ⟨53620870831242487650754877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35747247220828325100503251 53620870831242487650754877)
            ·
              refine ⟨20107826561715932869033079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53620870831242487650754877 20107826561715932869033079)
              ·
                refine ⟨30161739842573899303549619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20107826561715932869033079 30161739842573899303549619)
                ·
                  refine ⟨45242609763860848955324429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30161739842573899303549619 45242609763860848955324429)
                  ·
                    refine ⟨16965978661447818358246661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45242609763860848955324429 16965978661447818358246661)
                    ·
                      refine ⟨3181120999021465942171249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16965978661447818358246661 3181120999021465942171249)
                      ·
                        rfl

theorem cell23_6195211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_6195211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195211 prefixEnd_6195211 := by exact prefixLift 6195211
  have htrace : WordTrace (prefixWord ++ tailWord_6195211) baseStart_6195211 baseEnd_6195211 := by
    simpa [prefixWord, tailWord_6195211, baseEnd_6195211] using wordTrace_append hprefix tailTrace_6195211
  have hstable : (prefixWord ++ tailWord_6195211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195211).length < 2 ^ (prefixWord ++ tailWord_6195211).sum := by decide
  have hdescent : baseEnd_6195211 < baseStart_6195211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195251 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 6]
def baseStart_6195251 : Nat := 118140960795 + 6195251 * 2 ^ 59
def prefixEnd_6195251 : Nat := 4983230072969 + 3 ^ 40 * 6195251 * 2
def baseEnd_6195251 : Nat := 353460170916405087296785

theorem tailTrace_6195251 : CollatzResearch.WordTrace tailWord_6195251 prefixEnd_6195251 353460170916405087296785 := by
  unfold tailWord_6195251
  simp only [CollatzResearch.WordTrace]
  refine ⟨225959367278671166479081607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150639578185780777652721071 225959367278671166479081607)
  ·
    refine ⟨338939050918006749718622411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225959367278671166479081607 338939050918006749718622411)
    ·
      refine ⟨508408576377010124577933617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338939050918006749718622411 508408576377010124577933617)
      ·
        refine ⟨381306432282757593433450213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508408576377010124577933617 381306432282757593433450213)
        ·
          refine ⟨71494956053017048768771915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381306432282757593433450213 71494956053017048768771915)
          ·
            refine ⟨107242434079525573153157873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71494956053017048768771915 107242434079525573153157873)
            ·
              refine ⟨80431825559644179864868405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107242434079525573153157873 80431825559644179864868405)
              ·
                refine ⟨7540483646216641862331413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80431825559644179864868405 7540483646216641862331413)
                ·
                  refine ⟨353460170916405087296785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7540483646216641862331413 353460170916405087296785)
                  ·
                    rfl

theorem cell23_6195251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 6].length) (baseStart_6195251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195251 prefixEnd_6195251 := by exact prefixLift 6195251
  have htrace : WordTrace (prefixWord ++ tailWord_6195251) baseStart_6195251 baseEnd_6195251 := by
    simpa [prefixWord, tailWord_6195251, baseEnd_6195251] using wordTrace_append hprefix tailTrace_6195251
  have hstable : (prefixWord ++ tailWord_6195251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195251).length < 2 ^ (prefixWord ++ tailWord_6195251).sum := by decide
  have hdescent : baseEnd_6195251 < baseStart_6195251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195281 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_6195281 : Nat := 118140960795 + 6195281 * 2 ^ 59
def prefixEnd_6195281 : Nat := 4983230072969 + 3 ^ 40 * 6195281 * 2
def baseEnd_6195281 : Nat := 1060385647555760222765309

theorem tailTrace_6195281 : CollatzResearch.WordTrace tailWord_6195281 prefixEnd_6195281 1060385647555760222765309 := by
  unfold tailWord_6195281
  simp only [CollatzResearch.WordTrace]
  refine ⟨225960461468562481602673697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150640307645708321068449131 225960461468562481602673697)
  ·
    refine ⟨169470346101421861202005273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225960461468562481602673697 169470346101421861202005273)
    ·
      refine ⟨127102759576066395901503955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169470346101421861202005273 127102759576066395901503955)
      ·
        refine ⟨190654139364099593852255933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127102759576066395901503955 190654139364099593852255933)
        ·
          refine ⟨71495302261537347694595975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190654139364099593852255933 71495302261537347694595975)
          ·
            refine ⟨107242953392306021541893963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71495302261537347694595975 107242953392306021541893963)
            ·
              refine ⟨160864430088459032312840945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107242953392306021541893963 160864430088459032312840945)
              ·
                refine ⟨120648322566344274234630709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160864430088459032312840945 120648322566344274234630709)
                ·
                  refine ⟨11310780240594775709496629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120648322566344274234630709 11310780240594775709496629)
                  ·
                    refine ⟨1060385647555760222765309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11310780240594775709496629 1060385647555760222765309)
                    ·
                      rfl

theorem cell23_6195281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_6195281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195281 prefixEnd_6195281 := by exact prefixLift 6195281
  have htrace : WordTrace (prefixWord ++ tailWord_6195281) baseStart_6195281 baseEnd_6195281 := by
    simpa [prefixWord, tailWord_6195281, baseEnd_6195281] using wordTrace_append hprefix tailTrace_6195281
  have hstable : (prefixWord ++ tailWord_6195281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195281).length < 2 ^ (prefixWord ++ tailWord_6195281).sum := by decide
  have hdescent : baseEnd_6195281 < baseStart_6195281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195362 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6195362 : Nat := 118140960795 + 6195362 * 2 ^ 59
def prefixEnd_6195362 : Nat := 4983230072969 + 3 ^ 40 * 6195362 * 2
def baseEnd_6195362 : Nat := 1060399511533431617127685

theorem tailTrace_6195362 : CollatzResearch.WordTrace tailWord_6195362 prefixEnd_6195362 1060399511533431617127685 := by
  unfold tailWord_6195362
  simp only [CollatzResearch.WordTrace]
  refine ⟨56490853945317258109093085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150642277187512688290914893 56490853945317258109093085)
  ·
    refine ⟨21184070229493971790909907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56490853945317258109093085 21184070229493971790909907)
    ·
      refine ⟨31776105344240957686364861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21184070229493971790909907 31776105344240957686364861)
      ·
        refine ⟨11916039504090359132386823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31776105344240957686364861 11916039504090359132386823)
        ·
          refine ⟨17874059256135538698580235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916039504090359132386823 17874059256135538698580235)
          ·
            refine ⟨26811088884203308047870353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17874059256135538698580235 26811088884203308047870353)
            ·
              refine ⟨20108316663152481035902765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26811088884203308047870353 20108316663152481035902765)
              ·
                refine ⟨7540618748682180388463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20108316663152481035902765 7540618748682180388463537)
                ·
                  refine ⟨5655464061511635291347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7540618748682180388463537 5655464061511635291347653)
                  ·
                    refine ⟨1060399511533431617127685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5655464061511635291347653 1060399511533431617127685)
                    ·
                      rfl

theorem cell23_6195362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6195362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195362 prefixEnd_6195362 := by exact prefixLift 6195362
  have htrace : WordTrace (prefixWord ++ tailWord_6195362) baseStart_6195362 baseEnd_6195362 := by
    simpa [prefixWord, tailWord_6195362, baseEnd_6195362] using wordTrace_append hprefix tailTrace_6195362
  have hstable : (prefixWord ++ tailWord_6195362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195362).length < 2 ^ (prefixWord ++ tailWord_6195362).sum := by decide
  have hdescent : baseEnd_6195362 < baseStart_6195362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195380 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6195380 : Nat := 118140960795 + 6195380 * 2 ^ 59
def prefixEnd_6195380 : Nat := 4983230072969 + 3 ^ 40 * 6195380 * 2
def baseEnd_6195380 : Nat := 3181207777252075780957973

theorem tailTrace_6195380 : CollatzResearch.WordTrace tailWord_6195380 prefixEnd_6195380 3181207777252075780957973 := by
  unfold tailWord_6195380
  simp only [CollatzResearch.WordTrace]
  refine ⟨112982036147601910755263797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150642714863469214340351729 112982036147601910755263797)
  ·
    refine ⟨10592065888837679133305981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112982036147601910755263797 10592065888837679133305981)
    ·
      refine ⟨3972024708314129674989743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10592065888837679133305981 3972024708314129674989743)
      ·
        refine ⟨5958037062471194512484615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972024708314129674989743 5958037062471194512484615)
        ·
          refine ⟨8937055593706791768726923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958037062471194512484615 8937055593706791768726923)
          ·
            refine ⟨13405583390560187653090385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937055593706791768726923 13405583390560187653090385)
            ·
              refine ⟨10054187542920140739817789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13405583390560187653090385 10054187542920140739817789)
              ·
                refine ⟨3770320328595052777431671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054187542920140739817789 3770320328595052777431671)
                ·
                  refine ⟨5655480492892579166147507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770320328595052777431671 5655480492892579166147507)
                  ·
                    refine ⟨8483220739338868749221261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655480492892579166147507 8483220739338868749221261)
                    ·
                      refine ⟨3181207777252075780957973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483220739338868749221261 3181207777252075780957973)
                      ·
                        rfl

theorem cell23_6195380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6195380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195380 prefixEnd_6195380 := by exact prefixLift 6195380
  have htrace : WordTrace (prefixWord ++ tailWord_6195380) baseStart_6195380 baseEnd_6195380 := by
    simpa [prefixWord, tailWord_6195380, baseEnd_6195380] using wordTrace_append hprefix tailTrace_6195380
  have hstable : (prefixWord ++ tailWord_6195380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195380).length < 2 ^ (prefixWord ++ tailWord_6195380).sum := by decide
  have hdescent : baseEnd_6195380 < baseStart_6195380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195385 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6195385 : Nat := 118140960795 + 6195385 * 2 ^ 59
def prefixEnd_6195385 : Nat := 4983230072969 + 3 ^ 40 * 6195385 * 2
def baseEnd_6195385 : Nat := 3181210344655348261395449

theorem tailTrace_6195385 : CollatzResearch.WordTrace tailWord_6195385 prefixEnd_6195385 3181210344655348261395449 := by
  unfold tailWord_6195385
  simp only [CollatzResearch.WordTrace]
  refine ⟨225964254660185707364459609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150642836440123804909639739 225964254660185707364459609)
  ·
    refine ⟨169473190995139280523344707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225964254660185707364459609 169473190995139280523344707)
    ·
      refine ⟨254209786492708920785017061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169473190995139280523344707 254209786492708920785017061)
      ·
        refine ⟨47664334967382922647190699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254209786492708920785017061 47664334967382922647190699)
        ·
          refine ⟨71496502451074383970786049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47664334967382922647190699 71496502451074383970786049)
          ·
            refine ⟨53622376838305787978089537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71496502451074383970786049 53622376838305787978089537)
            ·
              refine ⟨40216782628729340983567153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53622376838305787978089537 40216782628729340983567153)
              ·
                refine ⟨30162586971547005737675365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40216782628729340983567153 30162586971547005737675365)
                ·
                  refine ⟨5655485057165063575814131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30162586971547005737675365 5655485057165063575814131)
                  ·
                    refine ⟨8483227585747595363721197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655485057165063575814131 8483227585747595363721197)
                    ·
                      refine ⟨3181210344655348261395449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483227585747595363721197 3181210344655348261395449)
                      ·
                        rfl

theorem cell23_6195385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6195385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195385 prefixEnd_6195385 := by exact prefixLift 6195385
  have htrace : WordTrace (prefixWord ++ tailWord_6195385) baseStart_6195385 baseEnd_6195385 := by
    simpa [prefixWord, tailWord_6195385, baseEnd_6195385] using wordTrace_append hprefix tailTrace_6195385
  have hstable : (prefixWord ++ tailWord_6195385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195385).length < 2 ^ (prefixWord ++ tailWord_6195385).sum := by decide
  have hdescent : baseEnd_6195385 < baseStart_6195385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195418 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_6195418 : Nat := 118140960795 + 6195418 * 2 ^ 59
def prefixEnd_6195418 : Nat := 4983230072969 + 3 ^ 40 * 6195418 * 2
def baseEnd_6195418 : Nat := 1060409096505648877427599

theorem tailTrace_6195418 : CollatzResearch.WordTrace tailWord_6195418 prefixEnd_6195418 1060409096505648877427599 := by
  unfold tailWord_6195418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56491364567266538500102727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150643638846044102666940605 56491364567266538500102727)
  ·
    refine ⟨84737046850899807750154091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56491364567266538500102727 84737046850899807750154091)
    ·
      refine ⟨127105570276349711625231137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84737046850899807750154091 127105570276349711625231137)
      ·
        refine ⟨95329177707262283718923353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127105570276349711625231137 95329177707262283718923353)
        ·
          refine ⟨71496883280446712789192515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95329177707262283718923353 71496883280446712789192515)
          ·
            refine ⟨107245324920670069183788773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71496883280446712789192515 107245324920670069183788773)
            ·
              refine ⟨20108498422625637971960395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107245324920670069183788773 20108498422625637971960395)
              ·
                refine ⟨30162747633938456957940593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20108498422625637971960395 30162747633938456957940593)
                ·
                  refine ⟨22622060725453842718455445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30162747633938456957940593 22622060725453842718455445)
                  ·
                    refine ⟨1060409096505648877427599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22622060725453842718455445 1060409096505648877427599)
                    ·
                      rfl

theorem cell23_6195418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_6195418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195418 prefixEnd_6195418 := by exact prefixLift 6195418
  have htrace : WordTrace (prefixWord ++ tailWord_6195418) baseStart_6195418 baseEnd_6195418 := by
    simpa [prefixWord, tailWord_6195418, baseEnd_6195418] using wordTrace_append hprefix tailTrace_6195418
  have hstable : (prefixWord ++ tailWord_6195418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195418).length < 2 ^ (prefixWord ++ tailWord_6195418).sum := by decide
  have hdescent : baseEnd_6195418 < baseStart_6195418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195426 : List Nat := [3, 3, 4, 1, 1, 2, 2, 7]
def baseStart_6195426 : Nat := 118140960795 + 6195426 * 2 ^ 59
def prefixEnd_6195426 : Nat := 4983230072969 + 3 ^ 40 * 6195426 * 2
def baseEnd_6195426 : Nat := 117823385087488244480843

theorem tailTrace_6195426 : CollatzResearch.WordTrace tailWord_6195426 prefixEnd_6195426 117823385087488244480843 := by
  unfold tailWord_6195426
  simp only [CollatzResearch.WordTrace]
  refine ⟨56491437513259292841675533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150643833368691447577801421 56491437513259292841675533)
  ·
    refine ⟨21184289067472234815628325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56491437513259292841675533 21184289067472234815628325)
    ·
      refine ⟨3972054200151044027930311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21184289067472234815628325 3972054200151044027930311)
      ·
        refine ⟨5958081300226566041895467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972054200151044027930311 5958081300226566041895467)
        ·
          refine ⟨8937121950339849062843201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958081300226566041895467 8937121950339849062843201)
          ·
            refine ⟨6702841462754886797132401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8937121950339849062843201 6702841462754886797132401)
            ·
              refine ⟨5027131097066165097849301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702841462754886797132401 5027131097066165097849301)
              ·
                refine ⟨117823385087488244480843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5027131097066165097849301 117823385087488244480843)
                ·
                  rfl

theorem cell23_6195426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_6195426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195426 prefixEnd_6195426 := by exact prefixLift 6195426
  have htrace : WordTrace (prefixWord ++ tailWord_6195426) baseStart_6195426 baseEnd_6195426 := by
    simpa [prefixWord, tailWord_6195426, baseEnd_6195426] using wordTrace_append hprefix tailTrace_6195426
  have hstable : (prefixWord ++ tailWord_6195426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195426).length < 2 ^ (prefixWord ++ tailWord_6195426).sum := by decide
  have hdescent : baseEnd_6195426 < baseStart_6195426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195428 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_6195428 : Nat := 118140960795 + 6195428 * 2 ^ 59
def prefixEnd_6195428 : Nat := 4983230072969 + 3 ^ 40 * 6195428 * 2
def baseEnd_6195428 : Nat := 3181232424323491593157751

theorem tailTrace_6195428 : CollatzResearch.WordTrace tailWord_6195428 prefixEnd_6195428 3181232424323491593157751 := by
  unfold tailWord_6195428
  simp only [CollatzResearch.WordTrace]
  refine ⟨112982911499514962854137469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150643881999353283805516625 112982911499514962854137469)
  ·
    refine ⟨42368591812318111070301551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112982911499514962854137469 42368591812318111070301551)
    ·
      refine ⟨63552887718477166605452327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42368591812318111070301551 63552887718477166605452327)
      ·
        refine ⟨95329331577715749908178491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63552887718477166605452327 95329331577715749908178491)
        ·
          refine ⟨142993997366573624862267737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95329331577715749908178491 142993997366573624862267737)
          ·
            refine ⟨107245498024930218646700803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142993997366573624862267737 107245498024930218646700803)
            ·
              refine ⟨160868247037395327970051205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107245498024930218646700803 160868247037395327970051205)
              ·
                refine ⟨30162796319511623994384601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160868247037395327970051205 30162796319511623994384601)
                ·
                  refine ⟨22622097239633717995788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30162796319511623994384601 22622097239633717995788451)
                  ·
                    refine ⟨33933145859450576993682677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22622097239633717995788451 33933145859450576993682677)
                    ·
                      refine ⟨3181232424323491593157751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33933145859450576993682677 3181232424323491593157751)
                      ·
                        rfl

theorem cell23_6195428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_6195428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195428 prefixEnd_6195428 := by exact prefixLift 6195428
  have htrace : WordTrace (prefixWord ++ tailWord_6195428) baseStart_6195428 baseEnd_6195428 := by
    simpa [prefixWord, tailWord_6195428, baseEnd_6195428] using wordTrace_append hprefix tailTrace_6195428
  have hstable : (prefixWord ++ tailWord_6195428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195428).length < 2 ^ (prefixWord ++ tailWord_6195428).sum := by decide
  have hdescent : baseEnd_6195428 < baseStart_6195428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195429 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6195429 : Nat := 118140960795 + 6195429 * 2 ^ 59
def prefixEnd_6195429 : Nat := 4983230072969 + 3 ^ 40 * 6195429 * 2
def baseEnd_6195429 : Nat := 3181232937804146089245247

theorem tailTrace_6195429 : CollatzResearch.WordTrace tailWord_6195429 prefixEnd_6195429 3181232937804146089245247 := by
  unfold tailWord_6195429
  simp only [CollatzResearch.WordTrace]
  refine ⟨225965859472026302879061341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150643906314684201919374227 225965859472026302879061341)
  ·
    refine ⟨84737197302009863579648003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225965859472026302879061341 84737197302009863579648003)
    ·
      refine ⟨127105795953014795369472005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84737197302009863579648003 127105795953014795369472005)
      ·
        refine ⟨23832336741190274131776001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127105795953014795369472005 23832336741190274131776001)
        ·
          refine ⟨17874252555892705598832001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23832336741190274131776001 17874252555892705598832001)
          ·
            refine ⟨13405689416919529199124001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17874252555892705598832001 13405689416919529199124001)
            ·
              refine ⟨10054267062689646899343001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13405689416919529199124001 10054267062689646899343001)
              ·
                refine ⟨7540700297017235174507251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10054267062689646899343001 7540700297017235174507251)
                ·
                  refine ⟨11311050445525852761760877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7540700297017235174507251 11311050445525852761760877)
                  ·
                    refine ⟨4241643917072194785660329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11311050445525852761760877 4241643917072194785660329)
                    ·
                      refine ⟨3181232937804146089245247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241643917072194785660329 3181232937804146089245247)
                      ·
                        rfl

theorem cell23_6195429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6195429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195429 prefixEnd_6195429 := by exact prefixLift 6195429
  have htrace : WordTrace (prefixWord ++ tailWord_6195429) baseStart_6195429 baseEnd_6195429 := by
    simpa [prefixWord, tailWord_6195429, baseEnd_6195429] using wordTrace_append hprefix tailTrace_6195429
  have hstable : (prefixWord ++ tailWord_6195429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195429).length < 2 ^ (prefixWord ++ tailWord_6195429).sum := by decide
  have hdescent : baseEnd_6195429 < baseStart_6195429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195465 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 7]
def baseStart_6195465 : Nat := 118140960795 + 6195465 * 2 ^ 59
def prefixEnd_6195465 : Nat := 4983230072969 + 3 ^ 40 * 6195465 * 2
def baseEnd_6195465 : Nat := 353472380345300883155009

theorem tailTrace_6195465 : CollatzResearch.WordTrace tailWord_6195465 prefixEnd_6195465 353472380345300883155009 := by
  unfold tailWord_6195465
  simp only [CollatzResearch.WordTrace]
  refine ⟨225967172499895881027371849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150644781666597254018247899 225967172499895881027371849)
  ·
    refine ⟨169475379374921910770528887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225967172499895881027371849 169475379374921910770528887)
    ·
      refine ⟨254213069062382866155793331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169475379374921910770528887 254213069062382866155793331)
      ·
        refine ⟨381319603593574299233689997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254213069062382866155793331 381319603593574299233689997)
        ·
          refine ⟨142994851347590362212633749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381319603593574299233689997 142994851347590362212633749)
          ·
            refine ⟨6702883656918298228717207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142994851347590362212633749 6702883656918298228717207)
            ·
              refine ⟨10054325485377447343075811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702883656918298228717207 10054325485377447343075811)
              ·
                refine ⟨15081488228066171014613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10054325485377447343075811 15081488228066171014613717)
                ·
                  refine ⟨353472380345300883155009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15081488228066171014613717 353472380345300883155009)
                  ·
                    rfl

theorem cell23_6195465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_6195465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195465 prefixEnd_6195465 := by exact prefixLift 6195465
  have htrace : WordTrace (prefixWord ++ tailWord_6195465) baseStart_6195465 baseEnd_6195465 := by
    simpa [prefixWord, tailWord_6195465, baseEnd_6195465] using wordTrace_append hprefix tailTrace_6195465
  have hstable : (prefixWord ++ tailWord_6195465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195465).length < 2 ^ (prefixWord ++ tailWord_6195465).sum := by decide
  have hdescent : baseEnd_6195465 < baseStart_6195465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195532 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6195532 : Nat := 118140960795 + 6195532 * 2 ^ 59
def prefixEnd_6195532 : Nat := 4983230072969 + 3 ^ 40 * 6195532 * 2
def baseEnd_6195532 : Nat := 3181285826311559186257273

theorem tailTrace_6195532 : CollatzResearch.WordTrace tailWord_6195532 prefixEnd_6195532 3181285826311559186257273 := by
  unfold tailWord_6195532
  simp only [CollatzResearch.WordTrace]
  refine ⟨112984808095326575735030425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150646410793768767646707233 112984808095326575735030425)
  ·
    refine ⟨84738606071494931801272819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112984808095326575735030425 84738606071494931801272819)
    ·
      refine ⟨127107909107242397701909229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84738606071494931801272819 127107909107242397701909229)
      ·
        refine ⟨47665465915215899138215961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127107909107242397701909229 47665465915215899138215961)
        ·
          refine ⟨35749099436411924353661971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47665465915215899138215961 35749099436411924353661971)
          ·
            refine ⟨53623649154617886530492957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749099436411924353661971 53623649154617886530492957)
            ·
              refine ⟨20108868432981707448934859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53623649154617886530492957 20108868432981707448934859)
              ·
                refine ⟨30163302649472561173402289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20108868432981707448934859 30163302649472561173402289)
                ·
                  refine ⟨22622476987104420880051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30163302649472561173402289 22622476987104420880051717)
                  ·
                    refine ⟨4241714435082078915009697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22622476987104420880051717 4241714435082078915009697)
                    ·
                      refine ⟨3181285826311559186257273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241714435082078915009697 3181285826311559186257273)
                      ·
                        rfl

theorem cell23_6195532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6195532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195532 prefixEnd_6195532 := by exact prefixLift 6195532
  have htrace : WordTrace (prefixWord ++ tailWord_6195532) baseStart_6195532 baseEnd_6195532 := by
    simpa [prefixWord, tailWord_6195532, baseEnd_6195532] using wordTrace_append hprefix tailTrace_6195532
  have hstable : (prefixWord ++ tailWord_6195532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195532).length < 2 ^ (prefixWord ++ tailWord_6195532).sum := by decide
  have hdescent : baseEnd_6195532 < baseStart_6195532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195550 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6195550 : Nat := 118140960795 + 6195550 * 2 ^ 59
def prefixEnd_6195550 : Nat := 4983230072969 + 3 ^ 40 * 6195550 * 2
def baseEnd_6195550 : Nat := 353477229884815568425799

theorem tailTrace_6195550 : CollatzResearch.WordTrace tailWord_6195550 prefixEnd_6195550 353477229884815568425799 := by
  unfold tailWord_6195550
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246284088073492568027013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150646848469725293696144069 28246284088073492568027013)
  ·
    refine ⟨5296178266513779856505065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28246284088073492568027013 5296178266513779856505065)
    ·
      refine ⟨3972133699885334892378799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5296178266513779856505065 3972133699885334892378799)
      ·
        refine ⟨5958200549828002338568199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972133699885334892378799 5958200549828002338568199)
        ·
          refine ⟨8937300824742003507852299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958200549828002338568199 8937300824742003507852299)
          ·
            refine ⟨13405951237113005261778449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937300824742003507852299 13405951237113005261778449)
            ·
              refine ⟨10054463427834753946333837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13405951237113005261778449 10054463427834753946333837)
              ·
                refine ⟨3770423785438032729875189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054463427834753946333837 3770423785438032729875189)
                ·
                  refine ⟨353477229884815568425799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3770423785438032729875189 353477229884815568425799)
                  ·
                    rfl

theorem cell23_6195550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6195550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195550 prefixEnd_6195550 := by exact prefixLift 6195550
  have htrace : WordTrace (prefixWord ++ tailWord_6195550) baseStart_6195550 baseEnd_6195550 := by
    simpa [prefixWord, tailWord_6195550, baseEnd_6195550] using wordTrace_append hprefix tailTrace_6195550
  have hstable : (prefixWord ++ tailWord_6195550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195550).length < 2 ^ (prefixWord ++ tailWord_6195550).sum := by decide
  have hdescent : baseEnd_6195550 < baseStart_6195550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195552 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_6195552 : Nat := 118140960795 + 6195552 * 2 ^ 59
def prefixEnd_6195552 : Nat := 4983230072969 + 3 ^ 40 * 6195552 * 2
def baseEnd_6195552 : Nat := 3181296095924649108007181

theorem tailTrace_6195552 : CollatzResearch.WordTrace tailWord_6195552 prefixEnd_6195552 3181296095924649108007181 := by
  unfold tailWord_6195552
  simp only [CollatzResearch.WordTrace]
  refine ⟨112985172825290347442894455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150646897100387129923859273 112985172825290347442894455)
  ·
    refine ⟨169477759237935521164341683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112985172825290347442894455 169477759237935521164341683)
    ·
      refine ⟨254216638856903281746512525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169477759237935521164341683 254216638856903281746512525)
      ·
        refine ⟨95331239571338730654942197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254216638856903281746512525 95331239571338730654942197)
        ·
          refine ⟨8937303709813005998900831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95331239571338730654942197 8937303709813005998900831)
          ·
            refine ⟨13405955564719508998351247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937303709813005998900831 13405955564719508998351247)
            ·
              refine ⟨20108933347079263497526871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13405955564719508998351247 20108933347079263497526871)
              ·
                refine ⟨30163400020618895246290307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20108933347079263497526871 30163400020618895246290307)
                ·
                  refine ⟨45245100030928342869435461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30163400020618895246290307 45245100030928342869435461)
                  ·
                    refine ⟨8483456255799064288019149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45245100030928342869435461 8483456255799064288019149)
                    ·
                      refine ⟨3181296095924649108007181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483456255799064288019149 3181296095924649108007181)
                      ·
                        rfl

theorem cell23_6195552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_6195552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195552 prefixEnd_6195552 := by exact prefixLift 6195552
  have htrace : WordTrace (prefixWord ++ tailWord_6195552) baseStart_6195552 baseEnd_6195552 := by
    simpa [prefixWord, tailWord_6195552, baseEnd_6195552] using wordTrace_append hprefix tailTrace_6195552
  have hstable : (prefixWord ++ tailWord_6195552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195552).length < 2 ^ (prefixWord ++ tailWord_6195552).sum := by decide
  have hdescent : baseEnd_6195552 < baseStart_6195552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195559 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 1, 4]
def baseStart_6195559 : Nat := 118140960795 + 6195559 * 2 ^ 59
def prefixEnd_6195559 : Nat := 4983230072969 + 3 ^ 40 * 6195559 * 2
def baseEnd_6195559 : Nat := 1060433230096410193539883

theorem tailTrace_6195559 : CollatzResearch.WordTrace tailWord_6195559 prefixEnd_6195559 1060433230096410193539883 := by
  unfold tailWord_6195559
  simp only [CollatzResearch.WordTrace]
  refine ⟨225970600961555335081293731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150647067307703556720862487 225970600961555335081293731)
  ·
    refine ⟨338955901442333002621940597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225970600961555335081293731 338955901442333002621940597)
    ·
      refine ⟨31777115760218718995806931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338955901442333002621940597 31777115760218718995806931)
      ·
        refine ⟨47665673640328078493710397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31777115760218718995806931 47665673640328078493710397)
        ·
          refine ⟨17874627615123029435141399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47665673640328078493710397 17874627615123029435141399)
          ·
            refine ⟨26811941422684544152712099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17874627615123029435141399 26811941422684544152712099)
            ·
              refine ⟨40217912134026816229068149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26811941422684544152712099 40217912134026816229068149)
              ·
                refine ⟨3770429262565014021475139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40217912134026816229068149 3770429262565014021475139)
                ·
                  refine ⟨5655643893847521032212709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770429262565014021475139 5655643893847521032212709)
                  ·
                    refine ⟨1060433230096410193539883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5655643893847521032212709 1060433230096410193539883)
                    ·
                      rfl

theorem cell23_6195559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_6195559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195559 prefixEnd_6195559 := by exact prefixLift 6195559
  have htrace : WordTrace (prefixWord ++ tailWord_6195559) baseStart_6195559 baseEnd_6195559 := by
    simpa [prefixWord, tailWord_6195559, baseEnd_6195559] using wordTrace_append hprefix tailTrace_6195559
  have hstable : (prefixWord ++ tailWord_6195559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195559).length < 2 ^ (prefixWord ++ tailWord_6195559).sum := by decide
  have hdescent : baseEnd_6195559 < baseStart_6195559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195592 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_6195592 : Nat := 118140960795 + 6195592 * 2 ^ 59
def prefixEnd_6195592 : Nat := 4983230072969 + 3 ^ 40 * 6195592 * 2
def baseEnd_6195592 : Nat := 3181316635150828951506997

theorem tailTrace_6195592 : CollatzResearch.WordTrace tailWord_6195592 prefixEnd_6195592 3181316635150828951506997 := by
  unfold tailWord_6195592
  simp only [CollatzResearch.WordTrace]
  refine ⟨112985902285217890858622515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150647869713623854478163353 112985902285217890858622515)
  ·
    refine ⟨169478853427826836287933773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112985902285217890858622515 169478853427826836287933773)
    ·
      refine ⟨63554570035435063607975165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169478853427826836287933773 63554570035435063607975165)
      ·
        refine ⟨23832963763288148852990687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63554570035435063607975165 23832963763288148852990687)
        ·
          refine ⟨35749445644932223279486031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23832963763288148852990687 35749445644932223279486031)
          ·
            refine ⟨53624168467398334919229047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749445644932223279486031 53624168467398334919229047)
            ·
              refine ⟨80436252701097502378843571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53624168467398334919229047 80436252701097502378843571)
              ·
                refine ⟨120654379051646253568265357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80436252701097502378843571 120654379051646253568265357)
                ·
                  refine ⟨45245392144367345088099509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120654379051646253568265357 45245392144367345088099509)
                  ·
                    refine ⟨4241755513534438602009329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45245392144367345088099509 4241755513534438602009329)
                    ·
                      refine ⟨3181316635150828951506997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241755513534438602009329 3181316635150828951506997)
                      ·
                        rfl

theorem cell23_6195592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_6195592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195592 prefixEnd_6195592 := by exact prefixLift 6195592
  have htrace : WordTrace (prefixWord ++ tailWord_6195592) baseStart_6195592 baseEnd_6195592 := by
    simpa [prefixWord, tailWord_6195592, baseEnd_6195592] using wordTrace_append hprefix tailTrace_6195592
  have hstable : (prefixWord ++ tailWord_6195592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195592).length < 2 ^ (prefixWord ++ tailWord_6195592).sum := by decide
  have hdescent : baseEnd_6195592 < baseStart_6195592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195615 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 6]
def baseStart_6195615 : Nat := 118140960795 + 6195615 * 2 ^ 59
def prefixEnd_6195615 : Nat := 4983230072969 + 3 ^ 40 * 6195615 * 2
def baseEnd_6195615 : Nat := 1060442815068627453839797

theorem tailTrace_6195615 : CollatzResearch.WordTrace tailWord_6195615 prefixEnd_6195615 1060442815068627453839797 := by
  unfold tailWord_6195615
  simp only [CollatzResearch.WordTrace]
  refine ⟨225972643449352456645332299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150648428966234971096888199 225972643449352456645332299)
  ·
    refine ⟨338958965174028684967998449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225972643449352456645332299 338958965174028684967998449)
    ·
      refine ⟨254219223880521513725998837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338958965174028684967998449 254219223880521513725998837)
      ·
        refine ⟨23833052238798891911812391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254219223880521513725998837 23833052238798891911812391)
        ·
          refine ⟨35749578358198337867718587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23833052238798891911812391 35749578358198337867718587)
          ·
            refine ⟨53624367537297506801577881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35749578358198337867718587 53624367537297506801577881)
            ·
              refine ⟨40218275652973130101183411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53624367537297506801577881 40218275652973130101183411)
              ·
                refine ⟨60327413479459695151775117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40218275652973130101183411 60327413479459695151775117)
                ·
                  refine ⟨22622780054797385681915669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60327413479459695151775117 22622780054797385681915669)
                  ·
                    refine ⟨1060442815068627453839797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22622780054797385681915669 1060442815068627453839797)
                    ·
                      rfl

theorem cell23_6195615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_6195615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195615 prefixEnd_6195615 := by exact prefixLift 6195615
  have htrace : WordTrace (prefixWord ++ tailWord_6195615) baseStart_6195615 baseEnd_6195615 := by
    simpa [prefixWord, tailWord_6195615, baseEnd_6195615] using wordTrace_append hprefix tailTrace_6195615
  have hstable : (prefixWord ++ tailWord_6195615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195615).length < 2 ^ (prefixWord ++ tailWord_6195615).sum := by decide
  have hdescent : baseEnd_6195615 < baseStart_6195615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195616 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 1, 1, 3]
def baseStart_6195616 : Nat := 118140960795 + 6195616 * 2 ^ 59
def prefixEnd_6195616 : Nat := 4983230072969 + 3 ^ 40 * 6195616 * 2
def baseEnd_6195616 : Nat := 3181328958686536857606887

theorem tailTrace_6195616 : CollatzResearch.WordTrace tailWord_6195616 prefixEnd_6195616 3181328958686536857606887 := by
  unfold tailWord_6195616
  simp only [CollatzResearch.WordTrace]
  refine ⟨112986339961174416908059351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150648453281565889210745801 112986339961174416908059351)
  ·
    refine ⟨169479509941761625362089027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112986339961174416908059351 169479509941761625362089027)
    ·
      refine ⟨254219264912642438043133541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169479509941761625362089027 254219264912642438043133541)
      ·
        refine ⟨47666112171120457133087539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254219264912642438043133541 47666112171120457133087539)
        ·
          refine ⟨71499168256680685699631309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47666112171120457133087539 71499168256680685699631309)
          ·
            refine ⟨26812188096255257137361741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71499168256680685699631309 26812188096255257137361741)
            ·
              refine ⟨10054570536095721426510653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26812188096255257137361741 10054570536095721426510653)
              ·
                refine ⟨3770463951035895534941495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054570536095721426510653 3770463951035895534941495)
                ·
                  refine ⟨5655695926553843302412243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770463951035895534941495 5655695926553843302412243)
                  ·
                    refine ⟨8483543889830764953618365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655695926553843302412243 8483543889830764953618365)
                    ·
                      refine ⟨3181328958686536857606887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483543889830764953618365 3181328958686536857606887)
                      ·
                        rfl

theorem cell23_6195616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_6195616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195616 prefixEnd_6195616 := by exact prefixLift 6195616
  have htrace : WordTrace (prefixWord ++ tailWord_6195616) baseStart_6195616 baseEnd_6195616 := by
    simpa [prefixWord, tailWord_6195616, baseEnd_6195616] using wordTrace_append hprefix tailTrace_6195616
  have hstable : (prefixWord ++ tailWord_6195616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195616).length < 2 ^ (prefixWord ++ tailWord_6195616).sum := by decide
  have hdescent : baseEnd_6195616 < baseStart_6195616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195633 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6195633 : Nat := 118140960795 + 6195633 * 2 ^ 59
def prefixEnd_6195633 : Nat := 4983230072969 + 3 ^ 40 * 6195633 * 2
def baseEnd_6195633 : Nat := 3181337687857663291094309

theorem tailTrace_6195633 : CollatzResearch.WordTrace tailWord_6195633 prefixEnd_6195633 3181337687857663291094309 := by
  unfold tailWord_6195633
  simp only [CollatzResearch.WordTrace]
  refine ⟨225973299963287245719487553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150648866642191497146325035 225973299963287245719487553)
  ·
    refine ⟨169479974972465434289615665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225973299963287245719487553 169479974972465434289615665)
    ·
      refine ⟨127109981229349075717211749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169479974972465434289615665 127109981229349075717211749)
      ·
        refine ⟨23833121480502951696977203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127109981229349075717211749 23833121480502951696977203)
        ·
          refine ⟨35749682220754427545465805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23833121480502951696977203 35749682220754427545465805)
          ·
            refine ⟨13406130832782910329549677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35749682220754427545465805 13406130832782910329549677)
            ·
              refine ⟨5027299062293591373581129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13406130832782910329549677 5027299062293591373581129)
              ·
                refine ⟨3770474296720193530185847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5027299062293591373581129 3770474296720193530185847)
                ·
                  refine ⟨5655711445080290295278771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770474296720193530185847 5655711445080290295278771)
                  ·
                    refine ⟨8483567167620435442918157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655711445080290295278771 8483567167620435442918157)
                    ·
                      refine ⟨3181337687857663291094309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483567167620435442918157 3181337687857663291094309)
                      ·
                        rfl

theorem cell23_6195633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6195633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195633 prefixEnd_6195633 := by exact prefixLift 6195633
  have htrace : WordTrace (prefixWord ++ tailWord_6195633) baseStart_6195633 baseEnd_6195633 := by
    simpa [prefixWord, tailWord_6195633, baseEnd_6195633] using wordTrace_append hprefix tailTrace_6195633
  have hstable : (prefixWord ++ tailWord_6195633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195633).length < 2 ^ (prefixWord ++ tailWord_6195633).sum := by decide
  have hdescent : baseEnd_6195633 < baseStart_6195633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195645 : List Nat := [1, 4, 1, 2, 2, 2, 1, 10]
def baseStart_6195645 : Nat := 118140960795 + 6195645 * 2 ^ 59
def prefixEnd_6195645 : Nat := 4983230072969 + 3 ^ 40 * 6195645 * 2
def baseEnd_6195645 : Nat := 117827549986130268301639

theorem tailTrace_6195645 : CollatzResearch.WordTrace tailWord_6195645 prefixEnd_6195645 117827549986130268301639 := by
  unfold tailWord_6195645
  simp only [CollatzResearch.WordTrace]
  refine ⟨225973737639243771768924389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150649158426162514512616259 225973737639243771768924389)
  ·
    refine ⟨42370075807358207206673323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225973737639243771768924389 42370075807358207206673323)
    ·
      refine ⟨63555113711037310810009985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42370075807358207206673323 63555113711037310810009985)
      ·
        refine ⟨47666335283277983107507489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63555113711037310810009985 47666335283277983107507489)
        ·
          refine ⟨35749751462458487330630617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47666335283277983107507489 35749751462458487330630617)
          ·
            refine ⟨26812313596843865497972963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35749751462458487330630617 26812313596843865497972963)
            ·
              refine ⟨40218470395265798246959445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26812313596843865497972963 40218470395265798246959445)
              ·
                refine ⟨117827549986130268301639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40218470395265798246959445 117827549986130268301639)
                ·
                  rfl

theorem cell23_6195645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 10].length) (baseStart_6195645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195645 prefixEnd_6195645 := by exact prefixLift 6195645
  have htrace : WordTrace (prefixWord ++ tailWord_6195645) baseStart_6195645 baseEnd_6195645 := by
    simpa [prefixWord, tailWord_6195645, baseEnd_6195645] using wordTrace_append hprefix tailTrace_6195645
  have hstable : (prefixWord ++ tailWord_6195645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195645).length < 2 ^ (prefixWord ++ tailWord_6195645).sum := by decide
  have hdescent : baseEnd_6195645 < baseStart_6195645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195690 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_6195690 : Nat := 118140960795 + 6195690 * 2 ^ 59
def prefixEnd_6195690 : Nat := 4983230072969 + 3 ^ 40 * 6195690 * 2
def baseEnd_6195690 : Nat := 3181366956254969568081547

theorem tailTrace_6195690 : CollatzResearch.WordTrace tailWord_6195690 prefixEnd_6195690 3181366956254969568081547 := by
  unfold tailWord_6195690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56493844731020186113578131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150650252616053829636208349 56493844731020186113578131)
  ·
    refine ⟨84740767096530279170367197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56493844731020186113578131 84740767096530279170367197)
    ·
      refine ⟨31777787661198854688887699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84740767096530279170367197 31777787661198854688887699)
      ·
        refine ⟨47666681491798282033331549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31777787661198854688887699 47666681491798282033331549)
        ·
          refine ⟨17875005559424355762499331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47666681491798282033331549 17875005559424355762499331)
          ·
            refine ⟨26812508339136533643748997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17875005559424355762499331 26812508339136533643748997)
            ·
              refine ⟨5027345313588100058202937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26812508339136533643748997 5027345313588100058202937)
              ·
                refine ⟨3770508985191075043652203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5027345313588100058202937 3770508985191075043652203)
                ·
                  refine ⟨5655763477786612565478305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770508985191075043652203 5655763477786612565478305)
                  ·
                    refine ⟨4241822608339959424108729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5655763477786612565478305 4241822608339959424108729)
                    ·
                      refine ⟨3181366956254969568081547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241822608339959424108729 3181366956254969568081547)
                      ·
                        rfl

theorem cell23_6195690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_6195690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195690 prefixEnd_6195690 := by exact prefixLift 6195690
  have htrace : WordTrace (prefixWord ++ tailWord_6195690) baseStart_6195690 baseEnd_6195690 := by
    simpa [prefixWord, tailWord_6195690, baseEnd_6195690] using wordTrace_append hprefix tailTrace_6195690
  have hstable : (prefixWord ++ tailWord_6195690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195690).length < 2 ^ (prefixWord ++ tailWord_6195690).sum := by decide
  have hdescent : baseEnd_6195690 < baseStart_6195690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195705 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_6195705 : Nat := 118140960795 + 6195705 * 2 ^ 59
def prefixEnd_6195705 : Nat := 4983230072969 + 3 ^ 40 * 6195705 * 2
def baseEnd_6195705 : Nat := 1060458219488262336464659

theorem tailTrace_6195705 : CollatzResearch.WordTrace tailWord_6195705 prefixEnd_6195705 1060458219488262336464659 := by
  unfold tailWord_6195705
  simp only [CollatzResearch.WordTrace]
  refine ⟨225975926019026402016108569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150650617346017601344072379 225975926019026402016108569)
  ·
    refine ⟨169481944514269801512081427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225975926019026402016108569 169481944514269801512081427)
    ·
      refine ⟨254222916771404702268122141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169481944514269801512081427 254222916771404702268122141)
      ·
        refine ⟨95333593789276763350545803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254222916771404702268122141 95333593789276763350545803)
        ·
          refine ⟨143000390683915145025818705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95333593789276763350545803 143000390683915145025818705)
          ·
            refine ⟨107250293012936358769364029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143000390683915145025818705 107250293012936358769364029)
            ·
              refine ⟨40218859879851134538511511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107250293012936358769364029 40218859879851134538511511)
              ·
                refine ⟨60328289819776701807767267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40218859879851134538511511 60328289819776701807767267)
                ·
                  refine ⟨90492434729665052711650901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60328289819776701807767267 90492434729665052711650901)
                  ·
                    refine ⟨1060458219488262336464659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90492434729665052711650901 1060458219488262336464659)
                    ·
                      rfl

theorem cell23_6195705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_6195705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195705 prefixEnd_6195705 := by exact prefixLift 6195705
  have htrace : WordTrace (prefixWord ++ tailWord_6195705) baseStart_6195705 baseEnd_6195705 := by
    simpa [prefixWord, tailWord_6195705, baseEnd_6195705] using wordTrace_append hprefix tailTrace_6195705
  have hstable : (prefixWord ++ tailWord_6195705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195705).length < 2 ^ (prefixWord ++ tailWord_6195705).sum := by decide
  have hdescent : baseEnd_6195705 < baseStart_6195705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195716 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6195716 : Nat := 118140960795 + 6195716 * 2 ^ 59
def prefixEnd_6195716 : Nat := 4983230072969 + 3 ^ 40 * 6195716 * 2
def baseEnd_6195716 : Nat := 3181380306751986466356427

theorem tailTrace_6195716 : CollatzResearch.WordTrace tailWord_6195716 prefixEnd_6195716 3181380306751986466356427 := by
  unfold tailWord_6195716
  simp only [CollatzResearch.WordTrace]
  refine ⟨112988163610993275447379501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150650884814657700596506001 112988163610993275447379501)
  ·
    refine ⟨42370561354122478292767313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112988163610993275447379501 42370561354122478292767313)
    ·
      refine ⟨31777921015591858719575485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42370561354122478292767313 31777921015591858719575485)
      ·
        refine ⟨11916720380846947019840807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31777921015591858719575485 11916720380846947019840807)
        ·
          refine ⟨17875080571270420529761211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916720380846947019840807 17875080571270420529761211)
          ·
            refine ⟨26812620856905630794641817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17875080571270420529761211 26812620856905630794641817)
            ·
              refine ⟨20109465642679223095981363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26812620856905630794641817 20109465642679223095981363)
              ·
                refine ⟨30164198464018834643972045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20109465642679223095981363 30164198464018834643972045)
                ·
                  refine ⟨11311574424007062991489517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30164198464018834643972045 11311574424007062991489517)
                  ·
                    refine ⟨4241840409002648621808569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11311574424007062991489517 4241840409002648621808569)
                    ·
                      refine ⟨3181380306751986466356427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241840409002648621808569 3181380306751986466356427)
                      ·
                        rfl

theorem cell23_6195716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6195716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195716 prefixEnd_6195716 := by exact prefixLift 6195716
  have htrace : WordTrace (prefixWord ++ tailWord_6195716) baseStart_6195716 baseEnd_6195716 := by
    simpa [prefixWord, tailWord_6195716, baseEnd_6195716] using wordTrace_append hprefix tailTrace_6195716
  have hstable : (prefixWord ++ tailWord_6195716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195716).length < 2 ^ (prefixWord ++ tailWord_6195716).sum := by decide
  have hdescent : baseEnd_6195716 < baseStart_6195716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195757 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6195757 : Nat := 118140960795 + 6195757 * 2 ^ 59
def prefixEnd_6195757 : Nat := 4983230072969 + 3 ^ 40 * 6195757 * 2
def baseEnd_6195757 : Nat := 3181401359458820805943739

theorem tailTrace_6195757 : CollatzResearch.WordTrace tailWord_6195757 prefixEnd_6195757 3181401359458820805943739 := by
  unfold tailWord_6195757
  simp only [CollatzResearch.WordTrace]
  refine ⟨225977822614838014897001525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150651881743225343264667683 225977822614838014897001525)
  ·
    refine ⟨21185420870141063896593893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225977822614838014897001525 21185420870141063896593893)
    ·
      refine ⟨3972266413151449480611355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21185420870141063896593893 3972266413151449480611355)
      ·
        refine ⟨5958399619727174220917033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972266413151449480611355 5958399619727174220917033)
        ·
          refine ⟨4468799714795380665687775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958399619727174220917033 4468799714795380665687775)
          ·
            refine ⟨6703199572193070998531663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468799714795380665687775 6703199572193070998531663)
            ·
              refine ⟨10054799358289606497797495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703199572193070998531663 10054799358289606497797495)
              ·
                refine ⟨15082199037434409746696243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10054799358289606497797495 15082199037434409746696243)
                ·
                  refine ⟨22623298556151614620044365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15082199037434409746696243 22623298556151614620044365)
                  ·
                    refine ⟨8483736958556855482516637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22623298556151614620044365 8483736958556855482516637)
                    ·
                      refine ⟨3181401359458820805943739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483736958556855482516637 3181401359458820805943739)
                      ·
                        rfl

theorem cell23_6195757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6195757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195757 prefixEnd_6195757 := by exact prefixLift 6195757
  have htrace : WordTrace (prefixWord ++ tailWord_6195757) baseStart_6195757 baseEnd_6195757 := by
    simpa [prefixWord, tailWord_6195757, baseEnd_6195757] using wordTrace_append hprefix tailTrace_6195757
  have hstable : (prefixWord ++ tailWord_6195757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195757).length < 2 ^ (prefixWord ++ tailWord_6195757).sum := by decide
  have hdescent : baseEnd_6195757 < baseStart_6195757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195763 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 2, 2, 2]
def baseStart_6195763 : Nat := 118140960795 + 6195763 * 2 ^ 59
def prefixEnd_6195763 : Nat := 4983230072969 + 3 ^ 40 * 6195763 * 2
def baseEnd_6195763 : Nat := 3181404440342747782468711

theorem tailTrace_6195763 : CollatzResearch.WordTrace tailWord_6195763 prefixEnd_6195763 3181404440342747782468711 := by
  unfold tailWord_6195763
  simp only [CollatzResearch.WordTrace]
  refine ⟨225978041452816277921719943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150652027635210851947813295 225978041452816277921719943)
  ·
    refine ⟨338967062179224416882579915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225978041452816277921719943 338967062179224416882579915)
    ·
      refine ⟨508450593268836625323869873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338967062179224416882579915 508450593268836625323869873)
      ·
        refine ⟨381337944951627468992902405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508450593268836625323869873 381337944951627468992902405)
        ·
          refine ⟨71500864678430150436169201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381337944951627468992902405 71500864678430150436169201)
          ·
            refine ⟨53625648508822612827126901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71500864678430150436169201 53625648508822612827126901)
            ·
              refine ⟨5027404547702119952543147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53625648508822612827126901 5027404547702119952543147)
              ·
                refine ⟨7541106821553179928814721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027404547702119952543147 7541106821553179928814721)
                ·
                  refine ⟨5655830116164884946611041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541106821553179928814721 5655830116164884946611041)
                  ·
                    refine ⟨4241872587123663709958281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5655830116164884946611041 4241872587123663709958281)
                    ·
                      refine ⟨3181404440342747782468711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4241872587123663709958281 3181404440342747782468711)
                      ·
                        rfl

theorem cell23_6195763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 2, 2].length) (baseStart_6195763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195763 prefixEnd_6195763 := by exact prefixLift 6195763
  have htrace : WordTrace (prefixWord ++ tailWord_6195763) baseStart_6195763 baseEnd_6195763 := by
    simpa [prefixWord, tailWord_6195763, baseEnd_6195763] using wordTrace_append hprefix tailTrace_6195763
  have hstable : (prefixWord ++ tailWord_6195763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195763).length < 2 ^ (prefixWord ++ tailWord_6195763).sum := by decide
  have hdescent : baseEnd_6195763 < baseStart_6195763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195786 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_6195786 : Nat := 118140960795 + 6195786 * 2 ^ 59
def prefixEnd_6195786 : Nat := 4983230072969 + 3 ^ 40 * 6195786 * 2
def baseEnd_6195786 : Nat := 353490694488644576942345

theorem tailTrace_6195786 : CollatzResearch.WordTrace tailWord_6195786 prefixEnd_6195786 353490694488644576942345 := by
  unfold tailWord_6195786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56494720082933238212451803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150652586887821968566538141 56494720082933238212451803)
  ·
    refine ⟨84742080124399857318677705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56494720082933238212451803 84742080124399857318677705)
    ·
      refine ⟨63556560093299892989008279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84742080124399857318677705 63556560093299892989008279)
      ·
        refine ⟨95334840139949839483512419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63556560093299892989008279 95334840139949839483512419)
        ·
          refine ⟨143002260209924759225268629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95334840139949839483512419 143002260209924759225268629)
          ·
            refine ⟨6703230947340223088684467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143002260209924759225268629 6703230947340223088684467)
            ·
              refine ⟨10054846421010334633026701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703230947340223088684467 10054846421010334633026701)
              ·
                refine ⟨3770567407878875487385013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10054846421010334633026701 3770567407878875487385013)
                ·
                  refine ⟨353490694488644576942345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3770567407878875487385013 353490694488644576942345)
                  ·
                    rfl

theorem cell23_6195786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_6195786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195786 prefixEnd_6195786 := by exact prefixLift 6195786
  have htrace : WordTrace (prefixWord ++ tailWord_6195786) baseStart_6195786 baseEnd_6195786 := by
    simpa [prefixWord, tailWord_6195786, baseEnd_6195786] using wordTrace_append hprefix tailTrace_6195786
  have hstable : (prefixWord ++ tailWord_6195786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195786).length < 2 ^ (prefixWord ++ tailWord_6195786).sum := by decide
  have hdescent : baseEnd_6195786 < baseStart_6195786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195903 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 1, 1, 3]
def baseStart_6195903 : Nat := 118140960795 + 6195903 * 2 ^ 59
def prefixEnd_6195903 : Nat := 4983230072969 + 3 ^ 40 * 6195903 * 2
def baseEnd_6195903 : Nat := 3181476327634377234718067

theorem tailTrace_6195903 : CollatzResearch.WordTrace tailWord_6195903 prefixEnd_6195903 3181476327634377234718067 := by
  unfold tailWord_6195903
  simp only [CollatzResearch.WordTrace]
  refine ⟨225983147672309081831816363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150655431781539387887877575 225983147672309081831816363)
  ·
    refine ⟨338974721508463622747724545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225983147672309081831816363 338974721508463622747724545)
    ·
      refine ⟨254231041131347717060793409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338974721508463622747724545 254231041131347717060793409)
      ·
        refine ⟨190673280848510787795595057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254231041131347717060793409 190673280848510787795595057)
        ·
          refine ⟨143004960636383090846696293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190673280848510787795595057 143004960636383090846696293)
          ·
            refine ⟨26813430119321829533755555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143004960636383090846696293 26813430119321829533755555)
            ·
              refine ⟨40220145178982744300633333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26813430119321829533755555 40220145178982744300633333)
              ·
                refine ⟨3770638610529632278184375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40220145178982744300633333 3770638610529632278184375)
                ·
                  refine ⟨5655957915794448417276563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770638610529632278184375 5655957915794448417276563)
                  ·
                    refine ⟨8483936873691672625914845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5655957915794448417276563 8483936873691672625914845)
                    ·
                      refine ⟨3181476327634377234718067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8483936873691672625914845 3181476327634377234718067)
                      ·
                        rfl

theorem cell23_6195903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_6195903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195903 prefixEnd_6195903 := by exact prefixLift 6195903
  have htrace : WordTrace (prefixWord ++ tailWord_6195903) baseStart_6195903 baseEnd_6195903 := by
    simpa [prefixWord, tailWord_6195903, baseEnd_6195903] using wordTrace_append hprefix tailTrace_6195903
  have hstable : (prefixWord ++ tailWord_6195903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195903).length < 2 ^ (prefixWord ++ tailWord_6195903).sum := by decide
  have hdescent : baseEnd_6195903 < baseStart_6195903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195929 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_6195929 : Nat := 118140960795 + 6195929 * 2 ^ 59
def prefixEnd_6195929 : Nat := 4983230072969 + 3 ^ 40 * 6195929 * 2
def baseEnd_6195929 : Nat := 3181489678131394132992947

theorem tailTrace_6195929 : CollatzResearch.WordTrace tailWord_6195929 prefixEnd_6195929 3181489678131394132992947 := by
  unfold tailWord_6195929
  simp only [CollatzResearch.WordTrace]
  refine ⟨225984095970214888272262841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150656063980143258848175227 225984095970214888272262841)
  ·
    refine ⟨169488071977661166204197131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225984095970214888272262841 169488071977661166204197131)
    ·
      refine ⟨254232107966491749306295697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169488071977661166204197131 254232107966491749306295697)
      ·
        refine ⟨190674080974868811979721773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254232107966491749306295697 190674080974868811979721773)
        ·
          refine ⟨71502780365575804492395665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190674080974868811979721773 71502780365575804492395665)
          ·
            refine ⟨53627085274181853369296749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71502780365575804492395665 53627085274181853369296749)
            ·
              refine ⟨20110156977818195013486281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53627085274181853369296749 20110156977818195013486281)
              ·
                refine ⟨15082617733363646260114711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20110156977818195013486281 15082617733363646260114711)
                ·
                  refine ⟨22623926600045469390172067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15082617733363646260114711 22623926600045469390172067)
                  ·
                    refine ⟨33935889900068204085258101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22623926600045469390172067 33935889900068204085258101)
                    ·
                      refine ⟨3181489678131394132992947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33935889900068204085258101 3181489678131394132992947)
                      ·
                        rfl

theorem cell23_6195929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_6195929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195929 prefixEnd_6195929 := by exact prefixLift 6195929
  have htrace : WordTrace (prefixWord ++ tailWord_6195929) baseStart_6195929 baseEnd_6195929 := by
    simpa [prefixWord, tailWord_6195929, baseEnd_6195929] using wordTrace_append hprefix tailTrace_6195929
  have hstable : (prefixWord ++ tailWord_6195929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195929).length < 2 ^ (prefixWord ++ tailWord_6195929).sum := by decide
  have hdescent : baseEnd_6195929 < baseStart_6195929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195949 : List Nat := [1, 5, 1, 2, 1, 1, 3, 9]
def baseStart_6195949 : Nat := 118140960795 + 6195949 * 2 ^ 59
def prefixEnd_6195949 : Nat := 4983230072969 + 3 ^ 40 * 6195949 * 2
def baseEnd_6195949 : Nat := 117833331397943853879365

theorem tailTrace_6195949 : CollatzResearch.WordTrace tailWord_6195949 prefixEnd_6195949 117833331397943853879365 := by
  unfold tailWord_6195949
  simp only [CollatzResearch.WordTrace]
  refine ⟨225984825430142431687990901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150656550286761621125327267 225984825430142431687990901)
  ·
    refine ⟨21186077384075852970749147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225984825430142431687990901 21186077384075852970749147)
    ·
      refine ⟨31779116076113779456123721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21186077384075852970749147 31779116076113779456123721)
      ·
        refine ⟨23834337057085334592092791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31779116076113779456123721 23834337057085334592092791)
        ·
          refine ⟨35751505585628001888139187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23834337057085334592092791 35751505585628001888139187)
          ·
            refine ⟨53627258378442002832208781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35751505585628001888139187 53627258378442002832208781)
            ·
              refine ⟨20110221891915751062078293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53627258378442002832208781 20110221891915751062078293)
              ·
                refine ⟨117833331397943853879365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20110221891915751062078293 117833331397943853879365)
                ·
                  rfl

theorem cell23_6195949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 9].length) (baseStart_6195949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195949 prefixEnd_6195949 := by exact prefixLift 6195949
  have htrace : WordTrace (prefixWord ++ tailWord_6195949) baseStart_6195949 baseEnd_6195949 := by
    simpa [prefixWord, tailWord_6195949, baseEnd_6195949] using wordTrace_append hprefix tailTrace_6195949
  have hstable : (prefixWord ++ tailWord_6195949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195949).length < 2 ^ (prefixWord ++ tailWord_6195949).sum := by decide
  have hdescent : baseEnd_6195949 < baseStart_6195949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195959 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_6195959 : Nat := 118140960795 + 6195959 * 2 ^ 59
def prefixEnd_6195959 : Nat := 4983230072969 + 3 ^ 40 * 6195959 * 2
def baseEnd_6195959 : Nat := 3181505082551029015617809

theorem tailTrace_6195959 : CollatzResearch.WordTrace tailWord_6195959 prefixEnd_6195959 3181505082551029015617809 := by
  unfold tailWord_6195959
  simp only [CollatzResearch.WordTrace]
  refine ⟨225985190160106203395854931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150656793440070802263903287 225985190160106203395854931)
  ·
    refine ⟨338977785240159305093782397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225985190160106203395854931 338977785240159305093782397)
    ·
      refine ⟨127116669465059739410168399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338977785240159305093782397 127116669465059739410168399)
      ·
        refine ⟨190675004197589609115252599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127116669465059739410168399 190675004197589609115252599)
        ·
          refine ⟨286012506296384413672878899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190675004197589609115252599 286012506296384413672878899)
          ·
            refine ⟨429018759444576620509318349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286012506296384413672878899 429018759444576620509318349)
            ·
              refine ⟨160882034791716232690994381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429018759444576620509318349 160882034791716232690994381)
              ·
                refine ⟨60330763046893587259122893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160882034791716232690994381 60330763046893587259122893)
                ·
                  refine ⟨22624036142585095222171085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60330763046893587259122893 22624036142585095222171085)
                  ·
                    refine ⟨8484013553469410708314157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22624036142585095222171085 8484013553469410708314157)
                    ·
                      refine ⟨3181505082551029015617809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484013553469410708314157 3181505082551029015617809)
                      ·
                        rfl

theorem cell23_6195959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_6195959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195959 prefixEnd_6195959 := by exact prefixLift 6195959
  have htrace : WordTrace (prefixWord ++ tailWord_6195959) baseStart_6195959 baseEnd_6195959 := by
    simpa [prefixWord, tailWord_6195959, baseEnd_6195959] using wordTrace_append hprefix tailTrace_6195959
  have hstable : (prefixWord ++ tailWord_6195959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195959).length < 2 ^ (prefixWord ++ tailWord_6195959).sum := by decide
  have hdescent : baseEnd_6195959 < baseStart_6195959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195966 : List Nat := [4, 2, 2, 1, 2, 3, 9]
def baseStart_6195966 : Nat := 118140960795 + 6195966 * 2 ^ 59
def prefixEnd_6195966 : Nat := 4983230072969 + 3 ^ 40 * 6195966 * 2
def baseEnd_6195966 : Nat := 39277884900192722076917

theorem tailTrace_6195966 : CollatzResearch.WordTrace tailWord_6195966 prefixEnd_6195966 39277884900192722076917 := by
  unfold tailWord_6195966
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248180683885105448919969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150656963647387229060906501 28248180683885105448919969)
  ·
    refine ⟨21186135512913829086689977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28248180683885105448919969 21186135512913829086689977)
    ·
      refine ⟨15889601634685371815017483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21186135512913829086689977 15889601634685371815017483)
      ·
        refine ⟨23834402452028057722526225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15889601634685371815017483 23834402452028057722526225)
        ·
          refine ⟨17875801839021043291894669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23834402452028057722526225 17875801839021043291894669)
          ·
            refine ⟨6703425689632891234460501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17875801839021043291894669 6703425689632891234460501)
            ·
              refine ⟨39277884900192722076917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6703425689632891234460501 39277884900192722076917)
              ·
                rfl

theorem cell23_6195966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 9].length) (baseStart_6195966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195966 prefixEnd_6195966 := by exact prefixLift 6195966
  have htrace : WordTrace (prefixWord ++ tailWord_6195966) baseStart_6195966 baseEnd_6195966 := by
    simpa [prefixWord, tailWord_6195966, baseEnd_6195966] using wordTrace_append hprefix tailTrace_6195966
  have hstable : (prefixWord ++ tailWord_6195966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195966).length < 2 ^ (prefixWord ++ tailWord_6195966).sum := by decide
  have hdescent : baseEnd_6195966 < baseStart_6195966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6195997 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6195997 : Nat := 118140960795 + 6195997 * 2 ^ 59
def prefixEnd_6195997 : Nat := 4983230072969 + 3 ^ 40 * 6195997 * 2
def baseEnd_6195997 : Nat := 3181524594815899866942635

theorem tailTrace_6195997 : CollatzResearch.WordTrace tailWord_6195997 prefixEnd_6195997 3181524594815899866942635 := by
  unfold tailWord_6195997
  simp only [CollatzResearch.WordTrace]
  refine ⟨225986576133968535885738245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150657717422645690590492163 225986576133968535885738245)
  ·
    refine ⟨42372483025119100478575921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225986576133968535885738245 42372483025119100478575921)
    ·
      refine ⟨31779362268839325358931941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42372483025119100478575921 31779362268839325358931941)
      ·
        refine ⟨5958630425407373504799739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31779362268839325358931941 5958630425407373504799739)
        ·
          refine ⟨8937945638111060257199609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958630425407373504799739 8937945638111060257199609)
          ·
            refine ⟨6703459228583295192899707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8937945638111060257199609 6703459228583295192899707)
            ·
              refine ⟨10055188842874942789349561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703459228583295192899707 10055188842874942789349561)
              ·
                refine ⟨7541391632156207092012171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055188842874942789349561 7541391632156207092012171)
                ·
                  refine ⟨11312087448234310638018257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541391632156207092012171 11312087448234310638018257)
                  ·
                    refine ⟨8484065586175732978513693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11312087448234310638018257 8484065586175732978513693)
                    ·
                      refine ⟨3181524594815899866942635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484065586175732978513693 3181524594815899866942635)
                      ·
                        rfl

theorem cell23_6195997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6195997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6195997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6195997 prefixEnd_6195997 := by exact prefixLift 6195997
  have htrace : WordTrace (prefixWord ++ tailWord_6195997) baseStart_6195997 baseEnd_6195997 := by
    simpa [prefixWord, tailWord_6195997, baseEnd_6195997] using wordTrace_append hprefix tailTrace_6195997
  have hstable : (prefixWord ++ tailWord_6195997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6195997).length < 2 ^ (prefixWord ++ tailWord_6195997).sum := by decide
  have hdescent : baseEnd_6195997 < baseStart_6195997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6195997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196010 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6196010 : Nat := 118140960795 + 6196010 * 2 ^ 59
def prefixEnd_6196010 : Nat := 4983230072969 + 3 ^ 40 * 6196010 * 2
def baseEnd_6196010 : Nat := 3181531270064408316080075

theorem tailTrace_6196010 : CollatzResearch.WordTrace tailWord_6196010 prefixEnd_6196010 3181531270064408316080075 := by
  unfold tailWord_6196010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56496762570730359776490371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150658033521947626070640989 56496762570730359776490371)
  ·
    refine ⟨84745143856095539664735557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56496762570730359776490371 84745143856095539664735557)
    ·
      refine ⟨15889714473017913687137917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84745143856095539664735557 15889714473017913687137917)
      ·
        refine ⟨5958642927381717632676719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15889714473017913687137917 5958642927381717632676719)
        ·
          refine ⟨8937964391072576449015079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958642927381717632676719 8937964391072576449015079)
          ·
            refine ⟨13406946586608864673522619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937964391072576449015079 13406946586608864673522619)
            ·
              refine ⟨20110419879913297010283929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406946586608864673522619 20110419879913297010283929)
              ·
                refine ⟨15082814909934972757712947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20110419879913297010283929 15082814909934972757712947)
                ·
                  refine ⟨22624222364902459136569421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15082814909934972757712947 22624222364902459136569421)
                  ·
                    refine ⟨8484083386838422176213533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22624222364902459136569421 8484083386838422176213533)
                    ·
                      refine ⟨3181531270064408316080075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484083386838422176213533 3181531270064408316080075)
                      ·
                        rfl

theorem cell23_6196010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6196010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196010 prefixEnd_6196010 := by exact prefixLift 6196010
  have htrace : WordTrace (prefixWord ++ tailWord_6196010) baseStart_6196010 baseEnd_6196010 := by
    simpa [prefixWord, tailWord_6196010, baseEnd_6196010] using wordTrace_append hprefix tailTrace_6196010
  have hstable : (prefixWord ++ tailWord_6196010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196010).length < 2 ^ (prefixWord ++ tailWord_6196010).sum := by decide
  have hdescent : baseEnd_6196010 < baseStart_6196010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196039 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 7]
def baseStart_6196039 : Nat := 118140960795 + 6196039 * 2 ^ 59
def prefixEnd_6196039 : Nat := 4983230072969 + 3 ^ 40 * 6196039 * 2
def baseEnd_6196039 : Nat := 353505129000376522513049

theorem tailTrace_6196039 : CollatzResearch.WordTrace tailWord_6196039 prefixEnd_6196039 353505129000376522513049 := by
  unfold tailWord_6196039
  simp only [CollatzResearch.WordTrace]
  refine ⟨225988107999816377058767171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150658738666544251372511447 225988107999816377058767171)
  ·
    refine ⟨338982161999724565588150757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225988107999816377058767171 338982161999724565588150757)
    ·
      refine ⟨63559155374948356047778267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338982161999724565588150757 63559155374948356047778267)
      ·
        refine ⟨95338733062422534071667401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63559155374948356047778267 95338733062422534071667401)
        ·
          refine ⟨71504049796816900553750551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95338733062422534071667401 71504049796816900553750551)
          ·
            refine ⟨107256074695225350830625827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71504049796816900553750551 107256074695225350830625827)
            ·
              refine ⟨160884112042838026245938741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107256074695225350830625827 160884112042838026245938741)
              ·
                refine ⟨15082885504016064960556757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160884112042838026245938741 15082885504016064960556757)
                ·
                  refine ⟨353505129000376522513049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15082885504016064960556757 353505129000376522513049)
                  ·
                    rfl

theorem cell23_6196039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 7].length) (baseStart_6196039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196039 prefixEnd_6196039 := by exact prefixLift 6196039
  have htrace : WordTrace (prefixWord ++ tailWord_6196039) baseStart_6196039 baseEnd_6196039 := by
    simpa [prefixWord, tailWord_6196039, baseEnd_6196039] using wordTrace_append hprefix tailTrace_6196039
  have hstable : (prefixWord ++ tailWord_6196039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196039).length < 2 ^ (prefixWord ++ tailWord_6196039).sum := by decide
  have hdescent : baseEnd_6196039 < baseStart_6196039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196050 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_6196050 : Nat := 118140960795 + 6196050 * 2 ^ 59
def prefixEnd_6196050 : Nat := 4983230072969 + 3 ^ 40 * 6196050 * 2
def baseEnd_6196050 : Nat := 3181551809290588159579891

theorem tailTrace_6196050 : CollatzResearch.WordTrace tailWord_6196050 prefixEnd_6196050 3181551809290588159579891 := by
  unfold tailWord_6196050
  simp only [CollatzResearch.WordTrace]
  refine ⟨56497127300694131484354401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150659006135184350624945069 56497127300694131484354401)
  ·
    refine ⟨42372845475520598613265801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56497127300694131484354401 42372845475520598613265801)
    ·
      refine ⟨31779634106640448959949351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42372845475520598613265801 31779634106640448959949351)
      ·
        refine ⟨47669451159960673439924027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31779634106640448959949351 47669451159960673439924027)
        ·
          refine ⟨71504176739941010159886041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47669451159960673439924027 71504176739941010159886041)
          ·
            refine ⟨53628132554955757619914531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71504176739941010159886041 53628132554955757619914531)
            ·
              refine ⟨80442198832433636429871797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53628132554955757619914531 80442198832433636429871797)
              ·
                refine ⟨7541456140540653415300481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80442198832433636429871797 7541456140540653415300481)
                ·
                  refine ⟨5656092105405490061475361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541456140540653415300481 5656092105405490061475361)
                  ·
                    refine ⟨4242069079054117546106521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5656092105405490061475361 4242069079054117546106521)
                    ·
                      refine ⟨3181551809290588159579891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242069079054117546106521 3181551809290588159579891)
                      ·
                        rfl

theorem cell23_6196050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_6196050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196050 prefixEnd_6196050 := by exact prefixLift 6196050
  have htrace : WordTrace (prefixWord ++ tailWord_6196050) baseStart_6196050 baseEnd_6196050 := by
    simpa [prefixWord, tailWord_6196050, baseEnd_6196050] using wordTrace_append hprefix tailTrace_6196050
  have hstable : (prefixWord ++ tailWord_6196050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196050).length < 2 ^ (prefixWord ++ tailWord_6196050).sum := by decide
  have hdescent : baseEnd_6196050 < baseStart_6196050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196079 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_6196079 : Nat := 118140960795 + 6196079 * 2 ^ 59
def prefixEnd_6196079 : Nat := 4983230072969 + 3 ^ 40 * 6196079 * 2
def baseEnd_6196079 : Nat := 3181566700229568546117257

theorem tailTrace_6196079 : CollatzResearch.WordTrace tailWord_6196079 prefixEnd_6196079 3181566700229568546117257 := by
  unfold tailWord_6196079
  simp only [CollatzResearch.WordTrace]
  refine ⟨225989566919671463890223291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150659711279780975926815527 225989566919671463890223291)
  ·
    refine ⟨338984350379507195835334937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225989566919671463890223291 338984350379507195835334937)
    ·
      refine ⟨254238262784630396876501203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338984350379507195835334937 254238262784630396876501203)
      ·
        refine ⟨381357394176945595314751805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254238262784630396876501203 381357394176945595314751805)
        ·
          refine ⟨143009022816354598243031927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381357394176945595314751805 143009022816354598243031927)
          ·
            refine ⟨214513534224531897364547891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143009022816354598243031927 214513534224531897364547891)
            ·
              refine ⟨321770301336797846046821837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214513534224531897364547891 321770301336797846046821837)
              ·
                refine ⟨120663863001299192267558189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321770301336797846046821837 120663863001299192267558189)
                ·
                  refine ⟨45248948625487197100334321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120663863001299192267558189 45248948625487197100334321)
                  ·
                    refine ⟨33936711469115397825250741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45248948625487197100334321 33936711469115397825250741)
                    ·
                      refine ⟨3181566700229568546117257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33936711469115397825250741 3181566700229568546117257)
                      ·
                        rfl

theorem cell23_6196079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_6196079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196079 prefixEnd_6196079 := by exact prefixLift 6196079
  have htrace : WordTrace (prefixWord ++ tailWord_6196079) baseStart_6196079 baseEnd_6196079 := by
    simpa [prefixWord, tailWord_6196079, baseEnd_6196079] using wordTrace_append hprefix tailTrace_6196079
  have hstable : (prefixWord ++ tailWord_6196079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196079).length < 2 ^ (prefixWord ++ tailWord_6196079).sum := by decide
  have hdescent : baseEnd_6196079 < baseStart_6196079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196116 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6196116 : Nat := 118140960795 + 6196116 * 2 ^ 59
def prefixEnd_6196116 : Nat := 4983230072969 + 3 ^ 40 * 6196116 * 2
def baseEnd_6196116 : Nat := 1060528566337928300451529

theorem tailTrace_6196116 : CollatzResearch.WordTrace tailWord_6196116 prefixEnd_6196116 1060528566337928300451529 := by
  unfold tailWord_6196116
  simp only [CollatzResearch.WordTrace]
  refine ⟨112995458210268709604660101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150660610947024946139546801 112995458210268709604660101)
  ·
    refine ⟨21186648414425383050873769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112995458210268709604660101 21186648414425383050873769)
    ·
      refine ⟨15889986310819037288155327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21186648414425383050873769 15889986310819037288155327)
      ·
        refine ⟨23834979466228555932232991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15889986310819037288155327 23834979466228555932232991)
        ·
          refine ⟨35752469199342833898349487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23834979466228555932232991 35752469199342833898349487)
          ·
            refine ⟨53628703799014250847524231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35752469199342833898349487 53628703799014250847524231)
            ·
              refine ⟨80443055698521376271286347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53628703799014250847524231 80443055698521376271286347)
              ·
                refine ⟨120664583547782064406929521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80443055698521376271286347 120664583547782064406929521)
                ·
                  refine ⟨90498437660836548305197141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120664583547782064406929521 90498437660836548305197141)
                  ·
                    refine ⟨1060528566337928300451529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90498437660836548305197141 1060528566337928300451529)
                    ·
                      rfl

theorem cell23_6196116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6196116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196116 prefixEnd_6196116 := by exact prefixLift 6196116
  have htrace : WordTrace (prefixWord ++ tailWord_6196116) baseStart_6196116 baseEnd_6196116 := by
    simpa [prefixWord, tailWord_6196116, baseEnd_6196116] using wordTrace_append hprefix tailTrace_6196116
  have hstable : (prefixWord ++ tailWord_6196116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196116).length < 2 ^ (prefixWord ++ tailWord_6196116).sum := by decide
  have hdescent : baseEnd_6196116 < baseStart_6196116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196200 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6196200 : Nat := 118140960795 + 6196200 * 2 ^ 59
def prefixEnd_6196200 : Nat := 4983230072969 + 3 ^ 40 * 6196200 * 2
def baseEnd_6196200 : Nat := 3181628831388762572704201

theorem tailTrace_6196200 : CollatzResearch.WordTrace tailWord_6196200 prefixEnd_6196200 3181628831388762572704201 := by
  unfold tailWord_6196200
  simp only [CollatzResearch.WordTrace]
  refine ⟨112996990076116550777689027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150662653434822067703585369 112996990076116550777689027)
  ·
    refine ⟨169495485114174826166533541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112996990076116550777689027 169495485114174826166533541)
    ·
      refine ⟨31780403458907779906225039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169495485114174826166533541 31780403458907779906225039)
      ·
        refine ⟨47670605188361669859337559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31780403458907779906225039 47670605188361669859337559)
        ·
          refine ⟨71505907782542504789006339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47670605188361669859337559 71505907782542504789006339)
          ·
            refine ⟨107258861673813757183509509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71505907782542504789006339 107258861673813757183509509)
            ·
              refine ⟨20111036563840079471908033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107258861673813757183509509 20111036563840079471908033)
              ·
                refine ⟨15083277422880059603931025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20111036563840079471908033 15083277422880059603931025)
                ·
                  refine ⟨11312458067160044702948269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15083277422880059603931025 11312458067160044702948269)
                  ·
                    refine ⟨4242171775185016763605601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11312458067160044702948269 4242171775185016763605601)
                    ·
                      refine ⟨3181628831388762572704201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242171775185016763605601 3181628831388762572704201)
                      ·
                        rfl

theorem cell23_6196200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6196200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196200 prefixEnd_6196200 := by exact prefixLift 6196200
  have htrace : WordTrace (prefixWord ++ tailWord_6196200) baseStart_6196200 baseEnd_6196200 := by
    simpa [prefixWord, tailWord_6196200, baseEnd_6196200] using wordTrace_append hprefix tailTrace_6196200
  have hstable : (prefixWord ++ tailWord_6196200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196200).length < 2 ^ (prefixWord ++ tailWord_6196200).sum := by decide
  have hdescent : baseEnd_6196200 < baseStart_6196200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196207 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 1, 1, 3]
def baseStart_6196207 : Nat := 118140960795 + 6196207 * 2 ^ 59
def prefixEnd_6196207 : Nat := 4983230072969 + 3 ^ 40 * 6196207 * 2
def baseEnd_6196207 : Nat := 3181632425753344045316669

theorem tailTrace_6196207 : CollatzResearch.WordTrace tailWord_6196207 prefixEnd_6196207 3181632425753344045316669 := by
  unfold tailWord_6196207
  simp only [CollatzResearch.WordTrace]
  refine ⟨225994235463207741750882875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150662823642138494500588583 225994235463207741750882875)
  ·
    refine ⟨338991353194811612626324313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225994235463207741750882875 338991353194811612626324313)
    ·
      refine ⟨254243514896108709469743235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338991353194811612626324313 254243514896108709469743235)
      ·
        refine ⟨381365272344163064204614853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254243514896108709469743235 381365272344163064204614853)
        ·
          refine ⟨71505988564530574538365285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381365272344163064204614853 71505988564530574538365285)
          ·
            refine ⟨13407372855849482725943491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71505988564530574538365285 13407372855849482725943491)
            ·
              refine ⟨20111059283774224088915237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13407372855849482725943491 20111059283774224088915237)
              ·
                refine ⟨3770823615707667016671607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20111059283774224088915237 3770823615707667016671607)
                ·
                  refine ⟨5656235423561500525007411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3770823615707667016671607 5656235423561500525007411)
                  ·
                    refine ⟨8484353135342250787511117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656235423561500525007411 8484353135342250787511117)
                    ·
                      refine ⟨3181632425753344045316669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484353135342250787511117 3181632425753344045316669)
                      ·
                        rfl

theorem cell23_6196207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 1, 3].length) (baseStart_6196207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196207 prefixEnd_6196207 := by exact prefixLift 6196207
  have htrace : WordTrace (prefixWord ++ tailWord_6196207) baseStart_6196207 baseEnd_6196207 := by
    simpa [prefixWord, tailWord_6196207, baseEnd_6196207] using wordTrace_append hprefix tailTrace_6196207
  have hstable : (prefixWord ++ tailWord_6196207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196207).length < 2 ^ (prefixWord ++ tailWord_6196207).sum := by decide
  have hdescent : baseEnd_6196207 < baseStart_6196207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196216 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_6196216 : Nat := 118140960795 + 6196216 * 2 ^ 59
def prefixEnd_6196216 : Nat := 4983230072969 + 3 ^ 40 * 6196216 * 2
def baseEnd_6196216 : Nat := 3181637047079234510104127

theorem tailTrace_6196216 : CollatzResearch.WordTrace tailWord_6196216 prefixEnd_6196216 3181637047079234510104127 := by
  unfold tailWord_6196216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112997281860087568143980251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150663042480116757525307001 112997281860087568143980251)
  ·
    refine ⟨169495922790131352215970377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112997281860087568143980251 169495922790131352215970377)
    ·
      refine ⟨127121942092598514161977783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169495922790131352215970377 127121942092598514161977783)
      ·
        refine ⟨190682913138897771242966675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127121942092598514161977783 190682913138897771242966675)
        ·
          refine ⟨286024369708346656864450013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190682913138897771242966675 286024369708346656864450013)
          ·
            refine ⟨107259138640629996324168755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286024369708346656864450013 107259138640629996324168755)
            ·
              refine ⟨160888707960944994486253133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107259138640629996324168755 160888707960944994486253133)
              ·
                refine ⟨60333265485354372932344925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160888707960944994486253133 60333265485354372932344925)
                ·
                  refine ⟨22624974557007889849629347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60333265485354372932344925 22624974557007889849629347)
                  ·
                    refine ⟨33937461835511834774444021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22624974557007889849629347 33937461835511834774444021)
                    ·
                      refine ⟨3181637047079234510104127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33937461835511834774444021 3181637047079234510104127)
                      ·
                        rfl

theorem cell23_6196216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_6196216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196216 prefixEnd_6196216 := by exact prefixLift 6196216
  have htrace : WordTrace (prefixWord ++ tailWord_6196216) baseStart_6196216 baseEnd_6196216 := by
    simpa [prefixWord, tailWord_6196216, baseEnd_6196216] using wordTrace_append hprefix tailTrace_6196216
  have hstable : (prefixWord ++ tailWord_6196216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196216).length < 2 ^ (prefixWord ++ tailWord_6196216).sum := by decide
  have hdescent : baseEnd_6196216 < baseStart_6196216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196247 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6196247 : Nat := 118140960795 + 6196247 * 2 ^ 59
def prefixEnd_6196247 : Nat := 4983230072969 + 3 ^ 40 * 6196247 * 2
def baseEnd_6196247 : Nat := 3181652964979523888816485

theorem tailTrace_6196247 : CollatzResearch.WordTrace tailWord_6196247 prefixEnd_6196247 3181652964979523888816485 := by
  unfold tailWord_6196247
  simp only [CollatzResearch.WordTrace]
  refine ⟨225995694383062828582338995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150663796255375219054892663 225995694383062828582338995)
  ·
    refine ⟨338993541574594242873508493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225995694383062828582338995 338993541574594242873508493)
    ·
      refine ⟨127122578090472841077565685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338993541574594242873508493 127122578090472841077565685)
      ·
        refine ⟨11917741695981828851021783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127122578090472841077565685 11917741695981828851021783)
        ·
          refine ⟨17876612543972743276532675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11917741695981828851021783 17876612543972743276532675)
          ·
            refine ⟨26814918815959114914799013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17876612543972743276532675 26814918815959114914799013)
            ·
              refine ⟨5027797277992334046524815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26814918815959114914799013 5027797277992334046524815)
              ·
                refine ⟨7541695916988501069787223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027797277992334046524815 7541695916988501069787223)
                ·
                  refine ⟨11312543875482751604680835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541695916988501069787223 11312543875482751604680835)
                  ·
                    refine ⟨16968815813224127407021253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11312543875482751604680835 16968815813224127407021253)
                    ·
                      refine ⟨3181652964979523888816485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16968815813224127407021253 3181652964979523888816485)
                      ·
                        rfl

theorem cell23_6196247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6196247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196247 prefixEnd_6196247 := by exact prefixLift 6196247
  have htrace : WordTrace (prefixWord ++ tailWord_6196247) baseStart_6196247 baseEnd_6196247 := by
    simpa [prefixWord, tailWord_6196247, baseEnd_6196247] using wordTrace_append hprefix tailTrace_6196247
  have hstable : (prefixWord ++ tailWord_6196247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196247).length < 2 ^ (prefixWord ++ tailWord_6196247).sum := by decide
  have hdescent : baseEnd_6196247 < baseStart_6196247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196250 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_6196250 : Nat := 118140960795 + 6196250 * 2 ^ 59
def prefixEnd_6196250 : Nat := 4983230072969 + 3 ^ 40 * 6196250 * 2
def baseEnd_6196250 : Nat := 3181654505421487377078971

theorem tailTrace_6196250 : CollatzResearch.WordTrace tailWord_6196250 prefixEnd_6196250 3181654505421487377078971 := by
  unfold tailWord_6196250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56498950950512990023674551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150663869201367973396465469 56498950950512990023674551)
  ·
    refine ⟨84748426425769485035511827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56498950950512990023674551 84748426425769485035511827)
    ·
      refine ⟨127122639638654227553267741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84748426425769485035511827 127122639638654227553267741)
      ·
        refine ⟨47670989864495335332475403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127122639638654227553267741 47670989864495335332475403)
        ·
          refine ⟨71506484796743002998713105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47670989864495335332475403 71506484796743002998713105)
          ·
            refine ⟨53629863597557252249034829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71506484796743002998713105 53629863597557252249034829)
            ·
              refine ⟨20111198849083969593388061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53629863597557252249034829 20111198849083969593388061)
              ·
                refine ⟨7541699568406488597520523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20111198849083969593388061 7541699568406488597520523)
                ·
                  refine ⟨11312549352609732896280785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541699568406488597520523 11312549352609732896280785)
                  ·
                    refine ⟨8484412014457299672210589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11312549352609732896280785 8484412014457299672210589)
                    ·
                      refine ⟨3181654505421487377078971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484412014457299672210589 3181654505421487377078971)
                      ·
                        rfl

theorem cell23_6196250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_6196250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196250 prefixEnd_6196250 := by exact prefixLift 6196250
  have htrace : WordTrace (prefixWord ++ tailWord_6196250) baseStart_6196250 baseEnd_6196250 := by
    simpa [prefixWord, tailWord_6196250, baseEnd_6196250] using wordTrace_append hprefix tailTrace_6196250
  have hstable : (prefixWord ++ tailWord_6196250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196250).length < 2 ^ (prefixWord ++ tailWord_6196250).sum := by decide
  have hdescent : baseEnd_6196250 < baseStart_6196250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196253 : List Nat := [1, 4, 2, 2, 3, 1, 10]
def baseStart_6196253 : Nat := 118140960795 + 6196253 * 2 ^ 59
def prefixEnd_6196253 : Nat := 4983230072969 + 3 ^ 40 * 6196253 * 2
def baseEnd_6196253 : Nat := 39279704269919146485697

theorem tailTrace_6196253 : CollatzResearch.WordTrace tailWord_6196253 prefixEnd_6196253 39279704269919146485697 := by
  unfold tailWord_6196253
  simp only [CollatzResearch.WordTrace]
  refine ⟨225995913221041091607057413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150663942147360727738038275 225995913221041091607057413)
  ·
    refine ⟨42374233728945204676323265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225995913221041091607057413 42374233728945204676323265)
    ·
      refine ⟨31780675296708903507242449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42374233728945204676323265 31780675296708903507242449)
      ·
        refine ⟨23835506472531677630431837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31780675296708903507242449 23835506472531677630431837)
        ·
          refine ⟨8938314927199379111411939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23835506472531677630431837 8938314927199379111411939)
          ·
            refine ⟨13407472390799068667117909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938314927199379111411939 13407472390799068667117909)
            ·
              refine ⟨39279704269919146485697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13407472390799068667117909 39279704269919146485697)
              ·
                rfl

theorem cell23_6196253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 10].length) (baseStart_6196253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196253 prefixEnd_6196253 := by exact prefixLift 6196253
  have htrace : WordTrace (prefixWord ++ tailWord_6196253) baseStart_6196253 baseEnd_6196253 := by
    simpa [prefixWord, tailWord_6196253, baseEnd_6196253] using wordTrace_append hprefix tailTrace_6196253
  have hstable : (prefixWord ++ tailWord_6196253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196253).length < 2 ^ (prefixWord ++ tailWord_6196253).sum := by decide
  have hdescent : baseEnd_6196253 < baseStart_6196253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196257 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6196257 : Nat := 118140960795 + 6196257 * 2 ^ 59
def prefixEnd_6196257 : Nat := 4983230072969 + 3 ^ 40 * 6196257 * 2
def baseEnd_6196257 : Nat := 1060552699928689616563813

theorem tailTrace_6196257 : CollatzResearch.WordTrace tailWord_6196257 prefixEnd_6196257 1060552699928689616563813 := by
  unfold tailWord_6196257
  simp only [CollatzResearch.WordTrace]
  refine ⟨225996059113026600290203025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150664039408684400193468683 225996059113026600290203025)
  ·
    refine ⟨169497044334769950217652269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225996059113026600290203025 169497044334769950217652269)
    ·
      refine ⟨63561391625538731331619601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169497044334769950217652269 63561391625538731331619601)
      ·
        refine ⟨47671043719154048498714701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63561391625538731331619601 47671043719154048498714701)
        ·
          refine ⟨17876641394682768187018013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47671043719154048498714701 17876641394682768187018013)
          ·
            refine ⟨6703740523006038070131755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17876641394682768187018013 6703740523006038070131755)
            ·
              refine ⟨10055610784509057105197633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703740523006038070131755 10055610784509057105197633)
              ·
                refine ⟨7541708088381792828898225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055610784509057105197633 7541708088381792828898225)
                ·
                  refine ⟨5656281066286344621673669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541708088381792828898225 5656281066286344621673669)
                  ·
                    refine ⟨1060552699928689616563813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656281066286344621673669 1060552699928689616563813)
                    ·
                      rfl

theorem cell23_6196257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6196257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196257 prefixEnd_6196257 := by exact prefixLift 6196257
  have htrace : WordTrace (prefixWord ++ tailWord_6196257) baseStart_6196257 baseEnd_6196257 := by
    simpa [prefixWord, tailWord_6196257, baseEnd_6196257] using wordTrace_append hprefix tailTrace_6196257
  have hstable : (prefixWord ++ tailWord_6196257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196257).length < 2 ^ (prefixWord ++ tailWord_6196257).sum := by decide
  have hdescent : baseEnd_6196257 < baseStart_6196257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196280 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_6196280 : Nat := 118140960795 + 6196280 * 2 ^ 59
def prefixEnd_6196280 : Nat := 4983230072969 + 3 ^ 40 * 6196280 * 2
def baseEnd_6196280 : Nat := 3181669909841122259703833

theorem tailTrace_6196280 : CollatzResearch.WordTrace tailWord_6196280 prefixEnd_6196280 3181669909841122259703833 := by
  unfold tailWord_6196280
  simp only [CollatzResearch.WordTrace]
  refine ⟨112998448995971637609145147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150664598661295516812193529 112998448995971637609145147)
  ·
    refine ⟨169497673493957456413717721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112998448995971637609145147 169497673493957456413717721)
    ·
      refine ⟨127123255120468092310288291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169497673493957456413717721 127123255120468092310288291)
      ·
        refine ⟨190684882680702138465432437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127123255120468092310288291 190684882680702138465432437)
        ·
          refine ⟨17876707751315825481134291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190684882680702138465432437 17876707751315825481134291)
          ·
            refine ⟨26815061626973738221701437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17876707751315825481134291 26815061626973738221701437)
            ·
              refine ⟨10055648110115151833138039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26815061626973738221701437 10055648110115151833138039)
              ·
                refine ⟨15083472165172727749707059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055648110115151833138039 15083472165172727749707059)
                ·
                  refine ⟨22625208247759091624560589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15083472165172727749707059 22625208247759091624560589)
                  ·
                    refine ⟨8484453092909659359210221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22625208247759091624560589 8484453092909659359210221)
                    ·
                      refine ⟨3181669909841122259703833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484453092909659359210221 3181669909841122259703833)
                      ·
                        rfl

theorem cell23_6196280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_6196280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196280 prefixEnd_6196280 := by exact prefixLift 6196280
  have htrace : WordTrace (prefixWord ++ tailWord_6196280) baseStart_6196280 baseEnd_6196280 := by
    simpa [prefixWord, tailWord_6196280, baseEnd_6196280] using wordTrace_append hprefix tailTrace_6196280
  have hstable : (prefixWord ++ tailWord_6196280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196280).length < 2 ^ (prefixWord ++ tailWord_6196280).sum := by decide
  have hdescent : baseEnd_6196280 < baseStart_6196280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196323 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3]
def baseStart_6196323 : Nat := 118140960795 + 6196323 * 2 ^ 59
def prefixEnd_6196323 : Nat := 4983230072969 + 3 ^ 40 * 6196323 * 2
def baseEnd_6196323 : Nat := 3181691989509265591466135

theorem tailTrace_6196323 : CollatzResearch.WordTrace tailWord_6196323 prefixEnd_6196323 3181691989509265591466135 := by
  unfold tailWord_6196323
  simp only [CollatzResearch.WordTrace]
  refine ⟨225998466330787493562105623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150665644220524995708070415 225998466330787493562105623)
  ·
    refine ⟨338997699496181240343158435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225998466330787493562105623 338997699496181240343158435)
    ·
      refine ⟨508496549244271860514737653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338997699496181240343158435 508496549244271860514737653)
      ·
        refine ⟨47671551491650486923256655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 508496549244271860514737653 47671551491650486923256655)
        ·
          refine ⟨71507327237475730384884983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47671551491650486923256655 71507327237475730384884983)
          ·
            refine ⟨107260990856213595577327475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71507327237475730384884983 107260990856213595577327475)
            ·
              refine ⟨160891486284320393365991213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107260990856213595577327475 160891486284320393365991213)
              ·
                refine ⟨60334307356620147512246705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160891486284320393365991213 60334307356620147512246705)
                ·
                  refine ⟨45250730517465110634185029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60334307356620147512246705 45250730517465110634185029)
                  ·
                    refine ⟨8484511972024708243909693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45250730517465110634185029 8484511972024708243909693)
                    ·
                      refine ⟨3181691989509265591466135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484511972024708243909693 3181691989509265591466135)
                      ·
                        rfl

theorem cell23_6196323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_6196323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196323 prefixEnd_6196323 := by exact prefixLift 6196323
  have htrace : WordTrace (prefixWord ++ tailWord_6196323) baseStart_6196323 baseEnd_6196323 := by
    simpa [prefixWord, tailWord_6196323, baseEnd_6196323] using wordTrace_append hprefix tailTrace_6196323
  have hstable : (prefixWord ++ tailWord_6196323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196323).length < 2 ^ (prefixWord ++ tailWord_6196323).sum := by decide
  have hdescent : baseEnd_6196323 < baseStart_6196323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196373 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_6196373 : Nat := 118140960795 + 6196373 * 2 ^ 59
def prefixEnd_6196373 : Nat := 4983230072969 + 3 ^ 40 * 6196373 * 2
def baseEnd_6196373 : Nat := 1060572554513996798613635

theorem tailTrace_6196373 : CollatzResearch.WordTrace tailWord_6196373 prefixEnd_6196373 1060572554513996798613635 := by
  unfold tailWord_6196373
  simp only [CollatzResearch.WordTrace]
  refine ⟨226000289980606352101425773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150666859987070901400950515 226000289980606352101425773)
  ·
    refine ⟨84750108742727382038034665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226000289980606352101425773 84750108742727382038034665)
    ·
      refine ⟨63562581557045536528525999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84750108742727382038034665 63562581557045536528525999)
      ·
        refine ⟨95343872335568304792788999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63562581557045536528525999 95343872335568304792788999)
        ·
          refine ⟨143015808503352457189183499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95343872335568304792788999 143015808503352457189183499)
          ·
            refine ⟨214523712755028685783775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143015808503352457189183499 214523712755028685783775249)
            ·
              refine ⟨160892784566271514337831437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214523712755028685783775249 160892784566271514337831437)
              ·
                refine ⟨60334794212351817876686789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160892784566271514337831437 60334794212351817876686789)
                ·
                  refine ⟨11312773914815965851878773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60334794212351817876686789 11312773914815965851878773)
                  ·
                    refine ⟨1060572554513996798613635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11312773914815965851878773 1060572554513996798613635)
                    ·
                      rfl

theorem cell23_6196373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_6196373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196373 prefixEnd_6196373 := by exact prefixLift 6196373
  have htrace : WordTrace (prefixWord ++ tailWord_6196373) baseStart_6196373 baseEnd_6196373 := by
    simpa [prefixWord, tailWord_6196373, baseEnd_6196373] using wordTrace_append hprefix tailTrace_6196373
  have hstable : (prefixWord ++ tailWord_6196373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196373).length < 2 ^ (prefixWord ++ tailWord_6196373).sum := by decide
  have hdescent : baseEnd_6196373 < baseStart_6196373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196410 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_6196410 : Nat := 118140960795 + 6196410 * 2 ^ 59
def prefixEnd_6196410 : Nat := 4983230072969 + 3 ^ 40 * 6196410 * 2
def baseEnd_6196410 : Nat := 3181736662326206751078235

theorem tailTrace_6196410 : CollatzResearch.WordTrace tailWord_6196410 prefixEnd_6196410 3181736662326206751078235 := by
  unfold tailWord_6196410
  simp only [CollatzResearch.WordTrace]
  refine ⟨56500409870368076855130671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150667759654314871613681789 56500409870368076855130671)
  ·
    refine ⟨84750614805552115282696007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56500409870368076855130671 84750614805552115282696007)
    ·
      refine ⟨127125922208328172924044011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84750614805552115282696007 127125922208328172924044011)
      ·
        refine ⟨190688883312492259386066017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127125922208328172924044011 190688883312492259386066017)
        ·
          refine ⟨143016662484369194539549513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190688883312492259386066017 143016662484369194539549513)
          ·
            refine ⟨107262496863276895904662135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143016662484369194539549513 107262496863276895904662135)
            ·
              refine ⟨160893745294915343856993203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107262496863276895904662135 160893745294915343856993203)
              ·
                refine ⟨241340617942373015785489805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160893745294915343856993203 241340617942373015785489805)
                ·
                  refine ⟨90502731728389880919558677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241340617942373015785489805 90502731728389880919558677)
                  ·
                    refine ⟨4242315549768275668104313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90502731728389880919558677 4242315549768275668104313)
                    ·
                      refine ⟨3181736662326206751078235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242315549768275668104313 3181736662326206751078235)
                      ·
                        rfl

theorem cell23_6196410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_6196410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196410 prefixEnd_6196410 := by exact prefixLift 6196410
  have htrace : WordTrace (prefixWord ++ tailWord_6196410) baseStart_6196410 baseEnd_6196410 := by
    simpa [prefixWord, tailWord_6196410, baseEnd_6196410] using wordTrace_append hprefix tailTrace_6196410
  have hstable : (prefixWord ++ tailWord_6196410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196410).length < 2 ^ (prefixWord ++ tailWord_6196410).sum := by decide
  have hdescent : baseEnd_6196410 < baseStart_6196410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196422 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6196422 : Nat := 118140960795 + 6196422 * 2 ^ 59
def prefixEnd_6196422 : Nat := 4983230072969 + 3 ^ 40 * 6196422 * 2
def baseEnd_6196422 : Nat := 3181742824094060704128181

theorem tailTrace_6196422 : CollatzResearch.WordTrace tailWord_6196422 prefixEnd_6196422 3181742824094060704128181 := by
  unfold tailWord_6196422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062564911169651045936235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150668051438285888979973013 7062564911169651045936235)
  ·
    refine ⟨10593847366754476568904353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7062564911169651045936235 10593847366754476568904353)
    ·
      refine ⟨7945385525065857426678265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10593847366754476568904353 7945385525065857426678265)
      ·
        refine ⟨5959039143799393070008699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945385525065857426678265 5959039143799393070008699)
        ·
          refine ⟨8938558715699089605013049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959039143799393070008699 8938558715699089605013049)
          ·
            refine ⟨6703919036774317203759787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8938558715699089605013049 6703919036774317203759787)
            ·
              refine ⟨10055878555161475805639681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703919036774317203759787 10055878555161475805639681)
              ·
                refine ⟨7541908916371106854229761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055878555161475805639681 7541908916371106854229761)
                ·
                  refine ⟨5656431687278330140672321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7541908916371106854229761 5656431687278330140672321)
                  ·
                    refine ⟨4242323765458747605504241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5656431687278330140672321 4242323765458747605504241)
                    ·
                      refine ⟨3181742824094060704128181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242323765458747605504241 3181742824094060704128181)
                      ·
                        rfl

theorem cell23_6196422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6196422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196422 prefixEnd_6196422 := by exact prefixLift 6196422
  have htrace : WordTrace (prefixWord ++ tailWord_6196422) baseStart_6196422 baseEnd_6196422 := by
    simpa [prefixWord, tailWord_6196422, baseEnd_6196422] using wordTrace_append hprefix tailTrace_6196422
  have hstable : (prefixWord ++ tailWord_6196422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196422).length < 2 ^ (prefixWord ++ tailWord_6196422).sum := by decide
  have hdescent : baseEnd_6196422 < baseStart_6196422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196423 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_6196423 : Nat := 118140960795 + 6196423 * 2 ^ 59
def prefixEnd_6196423 : Nat := 4983230072969 + 3 ^ 40 * 6196423 * 2
def baseEnd_6196423 : Nat := 3181743337574715200215675

theorem tailTrace_6196423 : CollatzResearch.WordTrace tailWord_6196423 prefixEnd_6196423 3181743337574715200215675 := by
  unfold tailWord_6196423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226002113630425210640745923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150668075753616807093830615 226002113630425210640745923)
  ·
    refine ⟨339003170445637815961118885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226002113630425210640745923 339003170445637815961118885)
    ·
      refine ⟨63563094458557090492709791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339003170445637815961118885 63563094458557090492709791)
      ·
        refine ⟨95344641687835635739064687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63563094458557090492709791 95344641687835635739064687)
        ·
          refine ⟨143016962531753453608597031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95344641687835635739064687 143016962531753453608597031)
          ·
            refine ⟨214525443797630180412895547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143016962531753453608597031 214525443797630180412895547)
            ·
              refine ⟨321788165696445270619343321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214525443797630180412895547 321788165696445270619343321)
              ·
                refine ⟨241341124272333952964507491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321788165696445270619343321 241341124272333952964507491)
                ·
                  refine ⟨362011686408500929446761237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241341124272333952964507491 362011686408500929446761237)
                  ·
                    refine ⟨16969297800398481067816933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 362011686408500929446761237 16969297800398481067816933)
                    ·
                      refine ⟨3181743337574715200215675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16969297800398481067816933 3181743337574715200215675)
                      ·
                        rfl

theorem cell23_6196423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_6196423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196423 prefixEnd_6196423 := by exact prefixLift 6196423
  have htrace : WordTrace (prefixWord ++ tailWord_6196423) baseStart_6196423 baseEnd_6196423 := by
    simpa [prefixWord, tailWord_6196423, baseEnd_6196423] using wordTrace_append hprefix tailTrace_6196423
  have hstable : (prefixWord ++ tailWord_6196423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196423).length < 2 ^ (prefixWord ++ tailWord_6196423).sum := by decide
  have hdescent : baseEnd_6196423 < baseStart_6196423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196437 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_6196437 : Nat := 118140960795 + 6196437 * 2 ^ 59
def prefixEnd_6196437 : Nat := 4983230072969 + 3 ^ 40 * 6196437 * 2
def baseEnd_6196437 : Nat := 1060583508767959381813537

theorem tailTrace_6196437 : CollatzResearch.WordTrace tailWord_6196437 prefixEnd_6196437 1060583508767959381813537 := by
  unfold tailWord_6196437
  simp only [CollatzResearch.WordTrace]
  refine ⟨226002624252374491031755565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150668416168249660687837043 226002624252374491031755565)
  ·
    refine ⟨84750984094640434136908337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226002624252374491031755565 84750984094640434136908337)
    ·
      refine ⟨63563238070980325602681253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84750984094640434136908337 63563238070980325602681253)
      ·
        refine ⟨11918107138308811050502735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63563238070980325602681253 11918107138308811050502735)
        ·
          refine ⟨17877160707463216575754103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918107138308811050502735 17877160707463216575754103)
          ·
            refine ⟨26815741061194824863631155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17877160707463216575754103 26815741061194824863631155)
            ·
              refine ⟨40223611591792237295446733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26815741061194824863631155 40223611591792237295446733)
              ·
                refine ⟨15083854346922088985792525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40223611591792237295446733 15083854346922088985792525)
                ·
                  refine ⟨5656445380095783369672197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15083854346922088985792525 5656445380095783369672197)
                  ·
                    refine ⟨1060583508767959381813537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656445380095783369672197 1060583508767959381813537)
                    ·
                      rfl

theorem cell23_6196437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_6196437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196437 prefixEnd_6196437 := by exact prefixLift 6196437
  have htrace : WordTrace (prefixWord ++ tailWord_6196437) baseStart_6196437 baseEnd_6196437 := by
    simpa [prefixWord, tailWord_6196437, baseEnd_6196437] using wordTrace_append hprefix tailTrace_6196437
  have hstable : (prefixWord ++ tailWord_6196437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196437).length < 2 ^ (prefixWord ++ tailWord_6196437).sum := by decide
  have hdescent : baseEnd_6196437 < baseStart_6196437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196494 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6196494 : Nat := 118140960795 + 6196494 * 2 ^ 59
def prefixEnd_6196494 : Nat := 4983230072969 + 3 ^ 40 * 6196494 * 2
def baseEnd_6196494 : Nat := 3181779794701184422427849

theorem tailTrace_6196494 : CollatzResearch.WordTrace tailWord_6196494 prefixEnd_6196494 3181779794701184422427849 := by
  unfold tailWord_6196494
  simp only [CollatzResearch.WordTrace]
  refine ⟨28250587901645998720822567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150669802142111993177720357 28250587901645998720822567)
  ·
    refine ⟨42375881852468998081233851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28250587901645998720822567 42375881852468998081233851)
    ·
      refine ⟨63563822778703497121850777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42375881852468998081233851 63563822778703497121850777)
      ·
        refine ⟨47672867084027622841388083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63563822778703497121850777 47672867084027622841388083)
        ·
          refine ⟨71509300626041434262082125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47672867084027622841388083 71509300626041434262082125)
          ·
            refine ⟨26815987734765537848280797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71509300626041434262082125 26815987734765537848280797)
            ·
              refine ⟨10055995400537076693105299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26815987734765537848280797 10055995400537076693105299)
              ·
                refine ⟨15083993100805615039657949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055995400537076693105299 15083993100805615039657949)
                ·
                  refine ⟨5656497412802105639871731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15083993100805615039657949 5656497412802105639871731)
                  ·
                    refine ⟨8484746119203158459807597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656497412802105639871731 8484746119203158459807597)
                    ·
                      refine ⟨3181779794701184422427849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484746119203158459807597 3181779794701184422427849)
                      ·
                        rfl

theorem cell23_6196494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6196494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196494 prefixEnd_6196494 := by exact prefixLift 6196494
  have htrace : WordTrace (prefixWord ++ tailWord_6196494) baseStart_6196494 baseEnd_6196494 := by
    simpa [prefixWord, tailWord_6196494, baseEnd_6196494] using wordTrace_append hprefix tailTrace_6196494
  have hstable : (prefixWord ++ tailWord_6196494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196494).length < 2 ^ (prefixWord ++ tailWord_6196494).sum := by decide
  have hdescent : baseEnd_6196494 < baseStart_6196494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196517 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_6196517 : Nat := 118140960795 + 6196517 * 2 ^ 59
def prefixEnd_6196517 : Nat := 4983230072969 + 3 ^ 40 * 6196517 * 2
def baseEnd_6196517 : Nat := 3181791604756237832440243

theorem tailTrace_6196517 : CollatzResearch.WordTrace tailWord_6196517 prefixEnd_6196517 3181791604756237832440243 := by
  unfold tailWord_6196517
  simp only [CollatzResearch.WordTrace]
  refine ⟨226005542092084664694667805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150670361394723109796445203 226005542092084664694667805)
  ·
    refine ⟨84752078284531749260500427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226005542092084664694667805 84752078284531749260500427)
    ·
      refine ⟨127128117426797623890750641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84752078284531749260500427 127128117426797623890750641)
      ·
        refine ⟨95346088070098217918062981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127128117426797623890750641 95346088070098217918062981)
        ·
          refine ⟨17877391513143415859636809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95346088070098217918062981 17877391513143415859636809)
          ·
            refine ⟨13408043634857561894727607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17877391513143415859636809 13408043634857561894727607)
            ·
              refine ⟨20112065452286342842091411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13408043634857561894727607 20112065452286342842091411)
              ·
                refine ⟨30168098178429514263137117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20112065452286342842091411 30168098178429514263137117)
                ·
                  refine ⟨11313036816911067848676419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30168098178429514263137117 11313036816911067848676419)
                  ·
                    refine ⟨16969555225366601773014629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11313036816911067848676419 16969555225366601773014629)
                    ·
                      refine ⟨3181791604756237832440243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16969555225366601773014629 3181791604756237832440243)
                      ·
                        rfl

theorem cell23_6196517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_6196517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196517 prefixEnd_6196517 := by exact prefixLift 6196517
  have htrace : WordTrace (prefixWord ++ tailWord_6196517) baseStart_6196517 baseEnd_6196517 := by
    simpa [prefixWord, tailWord_6196517, baseEnd_6196517] using wordTrace_append hprefix tailTrace_6196517
  have hstable : (prefixWord ++ tailWord_6196517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196517).length < 2 ^ (prefixWord ++ tailWord_6196517).sum := by decide
  have hdescent : baseEnd_6196517 < baseStart_6196517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196545 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6196545 : Nat := 118140960795 + 6196545 * 2 ^ 59
def prefixEnd_6196545 : Nat := 4983230072969 + 3 ^ 40 * 6196545 * 2
def baseEnd_6196545 : Nat := 3181805982214563722890115

theorem tailTrace_6196545 : CollatzResearch.WordTrace tailWord_6196545 prefixEnd_6196545 3181805982214563722890115 := by
  unfold tailWord_6196545
  simp only [CollatzResearch.WordTrace]
  refine ⟨226006563335983225476687089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150671042223988816984458059 226006563335983225476687089)
  ·
    refine ⟨169504922501987419107515317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226006563335983225476687089 169504922501987419107515317)
    ·
      refine ⟨15891086484561320541329561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169504922501987419107515317 15891086484561320541329561)
      ·
        refine ⟨11918314863420990405997171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15891086484561320541329561 11918314863420990405997171)
        ·
          refine ⟨17877472295131485608995757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918314863420990405997171 17877472295131485608995757)
          ·
            refine ⟨6704052110674307103373409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17877472295131485608995757 6704052110674307103373409)
            ·
              refine ⟨5028039083005730327530057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704052110674307103373409 5028039083005730327530057)
              ·
                refine ⟨3771029312254297745647543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028039083005730327530057 3771029312254297745647543)
                ·
                  refine ⟨5656543968381446618471315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771029312254297745647543 5656543968381446618471315)
                  ·
                    refine ⟨8484815952572169927706973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656543968381446618471315 8484815952572169927706973)
                    ·
                      refine ⟨3181805982214563722890115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484815952572169927706973 3181805982214563722890115)
                      ·
                        rfl

theorem cell23_6196545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6196545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196545 prefixEnd_6196545 := by exact prefixLift 6196545
  have htrace : WordTrace (prefixWord ++ tailWord_6196545) baseStart_6196545 baseEnd_6196545 := by
    simpa [prefixWord, tailWord_6196545, baseEnd_6196545] using wordTrace_append hprefix tailTrace_6196545
  have hstable : (prefixWord ++ tailWord_6196545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196545).length < 2 ^ (prefixWord ++ tailWord_6196545).sum := by decide
  have hdescent : baseEnd_6196545 < baseStart_6196545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196567 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_6196567 : Nat := 118140960795 + 6196567 * 2 ^ 59
def prefixEnd_6196567 : Nat := 4983230072969 + 3 ^ 40 * 6196567 * 2
def baseEnd_6196567 : Nat := 3181817278788962636815013

theorem tailTrace_6196567 : CollatzResearch.WordTrace tailWord_6196567 prefixEnd_6196567 3181817278788962636815013 := by
  unfold tailWord_6196567
  simp only [CollatzResearch.WordTrace]
  refine ⟨226007365741903523233987955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150671577161269015489325303 226007365741903523233987955)
  ·
    refine ⟨339011048612855284850981933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226007365741903523233987955 339011048612855284850981933)
    ·
      refine ⟨127129143229820731819118225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339011048612855284850981933 127129143229820731819118225)
      ·
        refine ⟨95346857422365548864338669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127129143229820731819118225 95346857422365548864338669)
        ·
          refine ⟨35755071533387080824127001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95346857422365548864338669 35755071533387080824127001)
          ·
            refine ⟨26816303650040310618095251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35755071533387080824127001 26816303650040310618095251)
            ·
              refine ⟨40224455475060465927142877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26816303650040310618095251 40224455475060465927142877)
              ·
                refine ⟨15084170803147674722678579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40224455475060465927142877 15084170803147674722678579)
                ·
                  refine ⟨22626256204721512084017869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15084170803147674722678579 22626256204721512084017869)
                  ·
                    refine ⟨8484846076770567031506701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22626256204721512084017869 8484846076770567031506701)
                    ·
                      refine ⟨3181817278788962636815013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8484846076770567031506701 3181817278788962636815013)
                      ·
                        rfl

theorem cell23_6196567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_6196567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196567 prefixEnd_6196567 := by exact prefixLift 6196567
  have htrace : WordTrace (prefixWord ++ tailWord_6196567) baseStart_6196567 baseEnd_6196567 := by
    simpa [prefixWord, tailWord_6196567, baseEnd_6196567] using wordTrace_append hprefix tailTrace_6196567
  have hstable : (prefixWord ++ tailWord_6196567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196567).length < 2 ^ (prefixWord ++ tailWord_6196567).sum := by decide
  have hdescent : baseEnd_6196567 < baseStart_6196567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196628 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6196628 : Nat := 118140960795 + 6196628 * 2 ^ 59
def prefixEnd_6196628 : Nat := 4983230072969 + 3 ^ 40 * 6196628 * 2
def baseEnd_6196628 : Nat := 3181848601108886898152233

theorem tailTrace_6196628 : CollatzResearch.WordTrace tailWord_6196628 prefixEnd_6196628 3181848601108886898152233 := by
  unfold tailWord_6196628
  simp only [CollatzResearch.WordTrace]
  refine ⟨113004795297341265325979269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150673060396455020434639025 113004795297341265325979269)
  ·
    refine ⟨21188399118251487248621113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113004795297341265325979269 21188399118251487248621113)
    ·
      refine ⟨15891299338688615436465835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21188399118251487248621113 15891299338688615436465835)
      ·
        refine ⟨23836949008032923154698753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15891299338688615436465835 23836949008032923154698753)
        ·
          refine ⟨17877711756024692366024065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23836949008032923154698753 17877711756024692366024065)
          ·
            refine ⟨13408283817018519274518049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17877711756024692366024065 13408283817018519274518049)
            ·
              refine ⟨10056212862763889455888537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13408283817018519274518049 10056212862763889455888537)
              ·
                refine ⟨7542159647072917091916403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056212862763889455888537 7542159647072917091916403)
                ·
                  refine ⟨11313239470609375637874605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7542159647072917091916403 11313239470609375637874605)
                  ·
                    refine ⟨4242464801478515864202977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11313239470609375637874605 4242464801478515864202977)
                    ·
                      refine ⟨3181848601108886898152233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242464801478515864202977 3181848601108886898152233)
                      ·
                        rfl

theorem cell23_6196628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6196628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196628 prefixEnd_6196628 := by exact prefixLift 6196628
  have htrace : WordTrace (prefixWord ++ tailWord_6196628) baseStart_6196628 baseEnd_6196628 := by
    simpa [prefixWord, tailWord_6196628, baseEnd_6196628] using wordTrace_append hprefix tailTrace_6196628
  have hstable : (prefixWord ++ tailWord_6196628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196628).length < 2 ^ (prefixWord ++ tailWord_6196628).sum := by decide
  have hdescent : baseEnd_6196628 < baseStart_6196628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196748 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_6196748 : Nat := 118140960795 + 6196748 * 2 ^ 59
def prefixEnd_6196748 : Nat := 4983230072969 + 3 ^ 40 * 6196748 * 2
def baseEnd_6196748 : Nat := 3181910218787426428651681

theorem tailTrace_6196748 : CollatzResearch.WordTrace tailWord_6196748 prefixEnd_6196748 3181910218787426428651681 := by
  unfold tailWord_6196748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113006983677123895573163449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150675978236165194097551265 113006983677123895573163449)
  ·
    refine ⟨84755237757842921679872587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113006983677123895573163449 84755237757842921679872587)
    ·
      refine ⟨127132856636764382519808881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84755237757842921679872587 127132856636764382519808881)
      ·
        refine ⟨95349642477573286889856661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127132856636764382519808881 95349642477573286889856661)
        ·
          refine ⟨4469514491136247822962031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95349642477573286889856661 4469514491136247822962031)
          ·
            refine ⟨6704271736704371734443047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469514491136247822962031 6704271736704371734443047)
            ·
              refine ⟨10056407605056557601664571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704271736704371734443047 10056407605056557601664571)
              ·
                refine ⟨15084611407584836402496857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10056407605056557601664571 15084611407584836402496857)
                ·
                  refine ⟨11313458555688627301872643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15084611407584836402496857 11313458555688627301872643)
                  ·
                    refine ⟨16970187833532940952808965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11313458555688627301872643 16970187833532940952808965)
                    ·
                      refine ⟨3181910218787426428651681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16970187833532940952808965 3181910218787426428651681)
                      ·
                        rfl

theorem cell23_6196748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_6196748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196748 prefixEnd_6196748 := by exact prefixLift 6196748
  have htrace : WordTrace (prefixWord ++ tailWord_6196748) baseStart_6196748 baseEnd_6196748 := by
    simpa [prefixWord, tailWord_6196748, baseEnd_6196748] using wordTrace_append hprefix tailTrace_6196748
  have hstable : (prefixWord ++ tailWord_6196748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196748).length < 2 ^ (prefixWord ++ tailWord_6196748).sum := by decide
  have hdescent : baseEnd_6196748 < baseStart_6196748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196771 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 6]
def baseStart_6196771 : Nat := 118140960795 + 6196771 * 2 ^ 59
def prefixEnd_6196771 : Nat := 4983230072969 + 3 ^ 40 * 6196771 * 2
def baseEnd_6196771 : Nat := 353546892093608870962675

theorem tailTrace_6196771 : CollatzResearch.WordTrace tailWord_6196771 prefixEnd_6196771 353546892093608870962675 := by
  unfold tailWord_6196771
  simp only [CollatzResearch.WordTrace]
  refine ⟨226014806233164466074414167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150676537488776310716276111 226014806233164466074414167)
  ·
    refine ⟨339022209349746699111621251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226014806233164466074414167 339022209349746699111621251)
    ·
      refine ⟨508533314024620048667431877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339022209349746699111621251 508533314024620048667431877)
      ·
        refine ⟨95349996379616259125143477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 508533314024620048667431877 95349996379616259125143477)
        ·
          refine ⟨8939062160589024292982201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95349996379616259125143477 8939062160589024292982201)
          ·
            refine ⟨6704296620441768219736651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8939062160589024292982201 6704296620441768219736651)
            ·
              refine ⟨10056444930662652329604977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704296620441768219736651 10056444930662652329604977)
              ·
                refine ⟨7542333697996989247203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056444930662652329604977 7542333697996989247203733)
                ·
                  refine ⟨353546892093608870962675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7542333697996989247203733 353546892093608870962675)
                  ·
                    rfl

theorem cell23_6196771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 6].length) (baseStart_6196771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196771 prefixEnd_6196771 := by exact prefixLift 6196771
  have htrace : WordTrace (prefixWord ++ tailWord_6196771) baseStart_6196771 baseEnd_6196771 := by
    simpa [prefixWord, tailWord_6196771, baseEnd_6196771] using wordTrace_append hprefix tailTrace_6196771
  have hstable : (prefixWord ++ tailWord_6196771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196771).length < 2 ^ (prefixWord ++ tailWord_6196771).sum := by decide
  have hdescent : baseEnd_6196771 < baseStart_6196771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196801 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6196801 : Nat := 118140960795 + 6196801 * 2 ^ 59
def prefixEnd_6196801 : Nat := 4983230072969 + 3 ^ 40 * 6196801 * 2
def baseEnd_6196801 : Nat := 1060645811087371573762979

theorem tailTrace_6196801 : CollatzResearch.WordTrace tailWord_6196801 prefixEnd_6196801 1060645811087371573762979 := by
  unfold tailWord_6196801
  simp only [CollatzResearch.WordTrace]
  refine ⟨226015900423055781198006257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150677266948703854132004171 226015900423055781198006257)
  ·
    refine ⟨169511925317291835898504693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226015900423055781198006257 169511925317291835898504693)
    ·
      refine ⟨15891742998496109615484815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169511925317291835898504693 15891742998496109615484815)
      ·
        refine ⟨23837614497744164423227223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15891742998496109615484815 23837614497744164423227223)
        ·
          refine ⟨35756421746616246634840835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23837614497744164423227223 35756421746616246634840835)
          ·
            refine ⟨53634632619924369952261253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35756421746616246634840835 53634632619924369952261253)
            ·
              refine ⟨10056493616235819366048985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53634632619924369952261253 10056493616235819366048985)
              ·
                refine ⟨7542370212176864524536739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056493616235819366048985 7542370212176864524536739)
                ·
                  refine ⟨11313555318265296786805109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7542370212176864524536739 11313555318265296786805109)
                  ·
                    refine ⟨1060645811087371573762979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11313555318265296786805109 1060645811087371573762979)
                    ·
                      rfl

theorem cell23_6196801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6196801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196801 prefixEnd_6196801 := by exact prefixLift 6196801
  have htrace : WordTrace (prefixWord ++ tailWord_6196801) baseStart_6196801 baseEnd_6196801 := by
    simpa [prefixWord, tailWord_6196801, baseEnd_6196801] using wordTrace_append hprefix tailTrace_6196801
  have hstable : (prefixWord ++ tailWord_6196801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196801).length < 2 ^ (prefixWord ++ tailWord_6196801).sum := by decide
  have hdescent : baseEnd_6196801 < baseStart_6196801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196824 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_6196824 : Nat := 118140960795 + 6196824 * 2 ^ 59
def prefixEnd_6196824 : Nat := 4983230072969 + 3 ^ 40 * 6196824 * 2
def baseEnd_6196824 : Nat := 3181949243317168131301331

theorem tailTrace_6196824 : CollatzResearch.WordTrace tailWord_6196824 prefixEnd_6196824 3181949243317168131301331 := by
  unfold tailWord_6196824
  simp only [CollatzResearch.WordTrace]
  refine ⟨113008369650986228063046763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150677826201314970750729017 113008369650986228063046763)
  ·
    refine ⟨169512554476479342094570145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113008369650986228063046763 169512554476479342094570145)
    ·
      refine ⟨127134415857359506570927609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169512554476479342094570145 127134415857359506570927609)
      ·
        refine ⟨95350811893019629928195707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127134415857359506570927609 95350811893019629928195707)
        ·
          refine ⟨143026217839529444892293561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95350811893019629928195707 143026217839529444892293561)
          ·
            refine ⟨107269663379647083669220171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143026217839529444892293561 107269663379647083669220171)
            ·
              refine ⟨160904495069470625503830257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107269663379647083669220171 160904495069470625503830257)
              ·
                refine ⟨120678371302102969127872693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160904495069470625503830257 120678371302102969127872693)
                ·
                  refine ⟨11313597309572153355738065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120678371302102969127872693 11313597309572153355738065)
                  ·
                    refine ⟨8485197982179115016803549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11313597309572153355738065 8485197982179115016803549)
                    ·
                      refine ⟨3181949243317168131301331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8485197982179115016803549 3181949243317168131301331)
                      ·
                        rfl

theorem cell23_6196824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_6196824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196824 prefixEnd_6196824 := by exact prefixLift 6196824
  have htrace : WordTrace (prefixWord ++ tailWord_6196824) baseStart_6196824 baseEnd_6196824 := by
    simpa [prefixWord, tailWord_6196824, baseEnd_6196824] using wordTrace_append hprefix tailTrace_6196824
  have hstable : (prefixWord ++ tailWord_6196824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196824).length < 2 ^ (prefixWord ++ tailWord_6196824).sum := by decide
  have hdescent : baseEnd_6196824 < baseStart_6196824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_6196847 : Nat := 118140960795 + 6196847 * 2 ^ 59
def prefixEnd_6196847 : Nat := 4983230072969 + 3 ^ 40 * 6196847 * 2
def baseEnd_6196847 : Nat := 3181961053372221541313725

theorem tailTrace_6196847 : CollatzResearch.WordTrace tailWord_6196847 prefixEnd_6196847 3181961053372221541313725 := by
  unfold tailWord_6196847
  simp only [CollatzResearch.WordTrace]
  refine ⟨226017578180889131054180795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150678385453926087369453863 226017578180889131054180795)
  ·
    refine ⟨339026367271333696581271193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226017578180889131054180795 339026367271333696581271193)
    ·
      refine ⟨254269775453500272435953395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339026367271333696581271193 254269775453500272435953395)
      ·
        refine ⟨381404663180250408653930093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254269775453500272435953395 381404663180250408653930093)
        ·
          refine ⟨143026748692593903245223785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381404663180250408653930093 143026748692593903245223785)
          ·
            refine ⟨107270061519445427433917839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143026748692593903245223785 107270061519445427433917839)
            ·
              refine ⟨160905092279168141150876759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107270061519445427433917839 160905092279168141150876759)
              ·
                refine ⟨241357638418752211726315139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160905092279168141150876759 241357638418752211726315139)
                ·
                  refine ⟨362036457628128317589472709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241357638418752211726315139 362036457628128317589472709)
                  ·
                    refine ⟨67881835805274059548026133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362036457628128317589472709 67881835805274059548026133)
                    ·
                      refine ⟨3181961053372221541313725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67881835805274059548026133 3181961053372221541313725)
                      ·
                        rfl

theorem cell23_6196847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_6196847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196847 prefixEnd_6196847 := by exact prefixLift 6196847
  have htrace : WordTrace (prefixWord ++ tailWord_6196847) baseStart_6196847 baseEnd_6196847 := by
    simpa [prefixWord, tailWord_6196847, baseEnd_6196847] using wordTrace_append hprefix tailTrace_6196847
  have hstable : (prefixWord ++ tailWord_6196847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196847).length < 2 ^ (prefixWord ++ tailWord_6196847).sum := by decide
  have hdescent : baseEnd_6196847 < baseStart_6196847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196848 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_6196848 : Nat := 118140960795 + 6196848 * 2 ^ 59
def prefixEnd_6196848 : Nat := 4983230072969 + 3 ^ 40 * 6196848 * 2
def baseEnd_6196848 : Nat := 1060653855617625345800407

theorem tailTrace_6196848 : CollatzResearch.WordTrace tailWord_6196848 prefixEnd_6196848 1060653855617625345800407 := by
  unfold tailWord_6196848
  simp only [CollatzResearch.WordTrace]
  refine ⟨113008807326942754112483599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150678409769257005483311465 113008807326942754112483599)
  ·
    refine ⟨169513210990414131168725399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113008807326942754112483599 169513210990414131168725399)
    ·
      refine ⟨254269816485621196753088099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169513210990414131168725399 254269816485621196753088099)
      ·
        refine ⟨381404724728431795129632149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254269816485621196753088099 381404724728431795129632149)
        ·
          refine ⟨17878346471645240396701507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 381404724728431795129632149 17878346471645240396701507)
          ·
            refine ⟨26817519707467860595052261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17878346471645240396701507 26817519707467860595052261)
            ·
              refine ⟨5028284945150223861572299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26817519707467860595052261 5028284945150223861572299)
              ·
                refine ⟨7542427417725335792358449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028284945150223861572299 7542427417725335792358449)
                ·
                  refine ⟨5656820563294001844268837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542427417725335792358449 5656820563294001844268837)
                  ·
                    refine ⟨1060653855617625345800407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656820563294001844268837 1060653855617625345800407)
                    ·
                      rfl

theorem cell23_6196848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_6196848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196848 prefixEnd_6196848 := by exact prefixLift 6196848
  have htrace : WordTrace (prefixWord ++ tailWord_6196848) baseStart_6196848 baseEnd_6196848 := by
    simpa [prefixWord, tailWord_6196848, baseEnd_6196848] using wordTrace_append hprefix tailTrace_6196848
  have hstable : (prefixWord ++ tailWord_6196848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196848).length < 2 ^ (prefixWord ++ tailWord_6196848).sum := by decide
  have hdescent : baseEnd_6196848 < baseStart_6196848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196871 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_6196871 : Nat := 118140960795 + 6196871 * 2 ^ 59
def prefixEnd_6196871 : Nat := 4983230072969 + 3 ^ 40 * 6196871 * 2
def baseEnd_6196871 : Nat := 3181973376907929447413615

theorem tailTrace_6196871 : CollatzResearch.WordTrace tailWord_6196871 prefixEnd_6196871 3181973376907929447413615 := by
  unfold tailWord_6196871
  simp only [CollatzResearch.WordTrace]
  refine ⟨226018453532802183153054467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150678969021868122102036311 226018453532802183153054467)
  ·
    refine ⟨339027680299203274729581701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226018453532802183153054467 339027680299203274729581701)
    ·
      refine ⟨63567690056100614011796569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339027680299203274729581701 63567690056100614011796569)
      ·
        refine ⟨47675767542075460508847427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63567690056100614011796569 47675767542075460508847427)
        ·
          refine ⟨71513651313113190763271141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47675767542075460508847427 71513651313113190763271141)
          ·
            refine ⟨13408809621208723268113339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71513651313113190763271141 13408809621208723268113339)
            ·
              refine ⟨20113214431813084902170009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13408809621208723268113339 20113214431813084902170009)
              ·
                refine ⟨15084910823859813676627507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20113214431813084902170009 15084910823859813676627507)
                ·
                  refine ⟨22627366235789720514941261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15084910823859813676627507 22627366235789720514941261)
                  ·
                    refine ⟨8485262338421145193102973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22627366235789720514941261 8485262338421145193102973)
                    ·
                      refine ⟨3181973376907929447413615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8485262338421145193102973 3181973376907929447413615)
                      ·
                        rfl

theorem cell23_6196871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_6196871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196871 prefixEnd_6196871 := by exact prefixLift 6196871
  have htrace : WordTrace (prefixWord ++ tailWord_6196871) baseStart_6196871 baseEnd_6196871 := by
    simpa [prefixWord, tailWord_6196871, baseEnd_6196871] using wordTrace_append hprefix tailTrace_6196871
  have hstable : (prefixWord ++ tailWord_6196871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196871).length < 2 ^ (prefixWord ++ tailWord_6196871).sum := by decide
  have hdescent : baseEnd_6196871 < baseStart_6196871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196888 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6196888 : Nat := 118140960795 + 6196888 * 2 ^ 59
def prefixEnd_6196888 : Nat := 4983230072969 + 3 ^ 40 * 6196888 * 2
def baseEnd_6196888 : Nat := 3181982106079055880901037

theorem tailTrace_6196888 : CollatzResearch.WordTrace tailWord_6196888 prefixEnd_6196888 3181982106079055880901037 := by
  unfold tailWord_6196888
  simp only [CollatzResearch.WordTrace]
  refine ⟨113009536786870297528211659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150679382382493730037615545 113009536786870297528211659)
  ·
    refine ⟨169514305180305446292317489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113009536786870297528211659 169514305180305446292317489)
    ·
      refine ⟨127135728885229084719238117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169514305180305446292317489 127135728885229084719238117)
      ·
        refine ⟨23837949165980453384857147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127135728885229084719238117 23837949165980453384857147)
        ·
          refine ⟨35756923748970680077285721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23837949165980453384857147 35756923748970680077285721)
          ·
            refine ⟨26817692811728010057964291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35756923748970680077285721 26817692811728010057964291)
            ·
              refine ⟨40226539217592015086946437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26817692811728010057964291 40226539217592015086946437)
              ·
                refine ⟨7542476103298502828802457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40226539217592015086946437 7542476103298502828802457)
                ·
                  refine ⟨5656857077473877121601843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542476103298502828802457 5656857077473877121601843)
                  ·
                    refine ⟨8485285616210815682402765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5656857077473877121601843 8485285616210815682402765)
                    ·
                      refine ⟨3181982106079055880901037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8485285616210815682402765 3181982106079055880901037)
                      ·
                        rfl

theorem cell23_6196888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6196888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196888 prefixEnd_6196888 := by exact prefixLift 6196888
  have htrace : WordTrace (prefixWord ++ tailWord_6196888) baseStart_6196888 baseEnd_6196888 := by
    simpa [prefixWord, tailWord_6196888, baseEnd_6196888] using wordTrace_append hprefix tailTrace_6196888
  have hstable : (prefixWord ++ tailWord_6196888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196888).length < 2 ^ (prefixWord ++ tailWord_6196888).sum := by decide
  have hdescent : baseEnd_6196888 < baseStart_6196888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196914 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6196914 : Nat := 118140960795 + 6196914 * 2 ^ 59
def prefixEnd_6196914 : Nat := 4983230072969 + 3 ^ 40 * 6196914 * 2
def baseEnd_6196914 : Nat := 3181995456576072779175917

theorem tailTrace_6196914 : CollatzResearch.WordTrace tailWord_6196914 prefixEnd_6196914 3181995456576072779175917 := by
  unfold tailWord_6196914
  simp only [CollatzResearch.WordTrace]
  refine ⟨56505005467911600374217449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150680014581097600997913197 56505005467911600374217449)
  ·
    refine ⟨42378754100933700280663087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56505005467911600374217449 42378754100933700280663087)
    ·
      refine ⟨63568131151400550420994631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42378754100933700280663087 63568131151400550420994631)
      ·
        refine ⟨95352196727100825631491947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63568131151400550420994631 95352196727100825631491947)
        ·
          refine ⟨143028295090651238447237921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95352196727100825631491947 143028295090651238447237921)
          ·
            refine ⟨107271221317988428835428441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143028295090651238447237921 107271221317988428835428441)
            ·
              refine ⟨80453415988491321626571331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107271221317988428835428441 80453415988491321626571331)
              ·
                refine ⟨120680123982736982439856997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80453415988491321626571331 120680123982736982439856997)
                ·
                  refine ⟨22627523246763184207473187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120680123982736982439856997 22627523246763184207473187)
                  ·
                    refine ⟨33941284870144776311209781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22627523246763184207473187 33941284870144776311209781)
                    ·
                      refine ⟨3181995456576072779175917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33941284870144776311209781 3181995456576072779175917)
                      ·
                        rfl

theorem cell23_6196914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6196914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196914 prefixEnd_6196914 := by exact prefixLift 6196914
  have htrace : WordTrace (prefixWord ++ tailWord_6196914) baseStart_6196914 baseEnd_6196914 := by
    simpa [prefixWord, tailWord_6196914, baseEnd_6196914] using wordTrace_append hprefix tailTrace_6196914
  have hstable : (prefixWord ++ tailWord_6196914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196914).length < 2 ^ (prefixWord ++ tailWord_6196914).sum := by decide
  have hdescent : baseEnd_6196914 < baseStart_6196914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196928 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2]
def baseStart_6196928 : Nat := 118140960795 + 6196928 * 2 ^ 59
def prefixEnd_6196928 : Nat := 4983230072969 + 3 ^ 40 * 6196928 * 2
def baseEnd_6196928 : Nat := 3182002645305235724400853

theorem tailTrace_6196928 : CollatzResearch.WordTrace tailWord_6196928 prefixEnd_6196928 3182002645305235724400853 := by
  unfold tailWord_6196928
  simp only [CollatzResearch.WordTrace]
  refine ⟨113010266246797840943939719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150680354995730454591919625 113010266246797840943939719)
  ·
    refine ⟨169515399370196761415909579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113010266246797840943939719 169515399370196761415909579)
    ·
      refine ⟨254273099055295142123864369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169515399370196761415909579 254273099055295142123864369)
      ·
        refine ⟨190704824291471356592898277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254273099055295142123864369 190704824291471356592898277)
        ·
          refine ⟨35757154554650879361168427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190704824291471356592898277 35757154554650879361168427)
          ·
            refine ⟨53635731831976319041752641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35757154554650879361168427 53635731831976319041752641)
            ·
              refine ⟨40226798873982239281314481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53635731831976319041752641 40226798873982239281314481)
              ·
                refine ⟨30170099155486679460985861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40226798873982239281314481 30170099155486679460985861)
                ·
                  refine ⟨5656893591653752398934849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30170099155486679460985861 5656893591653752398934849)
                  ·
                    refine ⟨4242670193740314299201137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5656893591653752398934849 4242670193740314299201137)
                    ·
                      refine ⟨3182002645305235724400853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242670193740314299201137 3182002645305235724400853)
                      ·
                        rfl

theorem cell23_6196928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_6196928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196928 prefixEnd_6196928 := by exact prefixLift 6196928
  have htrace : WordTrace (prefixWord ++ tailWord_6196928) baseStart_6196928 baseEnd_6196928 := by
    simpa [prefixWord, tailWord_6196928, baseEnd_6196928] using wordTrace_append hprefix tailTrace_6196928
  have hstable : (prefixWord ++ tailWord_6196928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196928).length < 2 ^ (prefixWord ++ tailWord_6196928).sum := by decide
  have hdescent : baseEnd_6196928 < baseStart_6196928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196945 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_6196945 : Nat := 118140960795 + 6196945 * 2 ^ 59
def prefixEnd_6196945 : Nat := 4983230072969 + 3 ^ 40 * 6196945 * 2
def baseEnd_6196945 : Nat := 3182011374476362157888275

theorem tailTrace_6196945 : CollatzResearch.WordTrace tailWord_6196945 prefixEnd_6196945 3182011374476362157888275 := by
  unfold tailWord_6196945
  simp only [CollatzResearch.WordTrace]
  refine ⟨226021152534534093791248289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150680768356356062527498859 226021152534534093791248289)
  ·
    refine ⟨169515864400900570343436217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226021152534534093791248289 169515864400900570343436217)
    ·
      refine ⟨127136898300675427757577163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169515864400900570343436217 127136898300675427757577163)
      ·
        refine ⟨190705347451013141636365745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127136898300675427757577163 190705347451013141636365745)
        ·
          refine ⟨143029010588259856227274309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190705347451013141636365745 143029010588259856227274309)
          ·
            refine ⟨26817939485298723042613933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143029010588259856227274309 26817939485298723042613933)
            ·
              refine ⟨10056727306987021140980225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26817939485298723042613933 10056727306987021140980225)
              ·
                refine ⟨7542545480240265855735169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056727306987021140980225 7542545480240265855735169)
                ·
                  refine ⟨5656909110180199391801377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542545480240265855735169 5656909110180199391801377)
                  ·
                    refine ⟨4242681832635149543851033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5656909110180199391801377 4242681832635149543851033)
                    ·
                      refine ⟨3182011374476362157888275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242681832635149543851033 3182011374476362157888275)
                      ·
                        rfl

theorem cell23_6196945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_6196945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196945 prefixEnd_6196945 := by exact prefixLift 6196945
  have htrace : WordTrace (prefixWord ++ tailWord_6196945) baseStart_6196945 baseEnd_6196945 := by
    simpa [prefixWord, tailWord_6196945, baseEnd_6196945] using wordTrace_append hprefix tailTrace_6196945
  have hstable : (prefixWord ++ tailWord_6196945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196945).length < 2 ^ (prefixWord ++ tailWord_6196945).sum := by decide
  have hdescent : baseEnd_6196945 < baseStart_6196945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196951 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 5]
def baseStart_6196951 : Nat := 118140960795 + 6196951 * 2 ^ 59
def prefixEnd_6196951 : Nat := 4983230072969 + 3 ^ 40 * 6196951 * 2
def baseEnd_6196951 : Nat := 353557161706698792712583

theorem tailTrace_6196951 : CollatzResearch.WordTrace tailWord_6196951 prefixEnd_6196951 353557161706698792712583 := by
  unfold tailWord_6196951
  simp only [CollatzResearch.WordTrace]
  refine ⟨226021371372512356815966707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150680914248341571210644471 226021371372512356815966707)
  ·
    refine ⟨339032057058768535223950061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226021371372512356815966707 339032057058768535223950061)
    ·
      refine ⟨127137021397038200708981273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339032057058768535223950061 127137021397038200708981273)
      ·
        refine ⟨95352766047778650531735955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127137021397038200708981273 95352766047778650531735955)
        ·
          refine ⟨143029149071667975797603933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95352766047778650531735955 143029149071667975797603933)
          ·
            refine ⟨53635930901875490924101475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143029149071667975797603933 53635930901875490924101475)
            ·
              refine ⟨80453896352813236386152213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53635930901875490924101475 80453896352813236386152213)
              ·
                refine ⟨3771276391538120455600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80453896352813236386152213 3771276391538120455600885)
                ·
                  refine ⟨353557161706698792712583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771276391538120455600885 353557161706698792712583)
                  ·
                    rfl

theorem cell23_6196951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 5].length) (baseStart_6196951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196951 prefixEnd_6196951 := by exact prefixLift 6196951
  have htrace : WordTrace (prefixWord ++ tailWord_6196951) baseStart_6196951 baseEnd_6196951 := by
    simpa [prefixWord, tailWord_6196951, baseEnd_6196951] using wordTrace_append hprefix tailTrace_6196951
  have hstable : (prefixWord ++ tailWord_6196951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196951).length < 2 ^ (prefixWord ++ tailWord_6196951).sum := by decide
  have hdescent : baseEnd_6196951 < baseStart_6196951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196964 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_6196964 : Nat := 118140960795 + 6196964 * 2 ^ 59
def prefixEnd_6196964 : Nat := 4983230072969 + 3 ^ 40 * 6196964 * 2
def baseEnd_6196964 : Nat := 1060673710202932527850229

theorem tailTrace_6196964 : CollatzResearch.WordTrace tailWord_6196964 prefixEnd_6196964 1060673710202932527850229 := by
  unfold tailWord_6196964
  simp only [CollatzResearch.WordTrace]
  refine ⟨113010922760732630018094973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150681230347643506690793297 113010922760732630018094973)
  ·
    refine ⟨42379096035274736256785615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113010922760732630018094973 42379096035274736256785615)
    ·
      refine ⟨63568644052912104385178423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42379096035274736256785615 63568644052912104385178423)
      ·
        refine ⟨95352966079368156577767635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63568644052912104385178423 95352966079368156577767635)
        ·
          refine ⟨143029449119052234866651453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95352966079368156577767635 143029449119052234866651453)
          ·
            refine ⟨53636043419644588074994295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143029449119052234866651453 53636043419644588074994295)
            ·
              refine ⟨80454065129466882112491443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53636043419644588074994295 80454065129466882112491443)
              ·
                refine ⟨120681097694200323168737165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80454065129466882112491443 120681097694200323168737165)
                ·
                  refine ⟨45255411635325121188276437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120681097694200323168737165 45255411635325121188276437)
                  ·
                    refine ⟨1060673710202932527850229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45255411635325121188276437 1060673710202932527850229)
                    ·
                      rfl

theorem cell23_6196964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_6196964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196964 prefixEnd_6196964 := by exact prefixLift 6196964
  have htrace : WordTrace (prefixWord ++ tailWord_6196964) baseStart_6196964 baseEnd_6196964 := by
    simpa [prefixWord, tailWord_6196964, baseEnd_6196964] using wordTrace_append hprefix tailTrace_6196964
  have hstable : (prefixWord ++ tailWord_6196964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196964).length < 2 ^ (prefixWord ++ tailWord_6196964).sum := by decide
  have hdescent : baseEnd_6196964 < baseStart_6196964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6196971 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 5, 2]
def baseStart_6196971 : Nat := 118140960795 + 6196971 * 2 ^ 59
def prefixEnd_6196971 : Nat := 4983230072969 + 3 ^ 40 * 6196971 * 2
def baseEnd_6196971 : Nat := 3182024724973379056163155

theorem tailTrace_6196971 : CollatzResearch.WordTrace tailWord_6196971 prefixEnd_6196971 3182024724973379056163155 := by
  unfold tailWord_6196971
  simp only [CollatzResearch.WordTrace]
  refine ⟨226022100832439900231694767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150681400554959933487796511 226022100832439900231694767)
  ·
    refine ⟨339033151248659850347542151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226022100832439900231694767 339033151248659850347542151)
    ·
      refine ⟨508549726872989775521313227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339033151248659850347542151 508549726872989775521313227)
      ·
        refine ⟨762824590309484663281969841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508549726872989775521313227 762824590309484663281969841)
        ·
          refine ⟨572118442732113497461477381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762824590309484663281969841 572118442732113497461477381)
          ·
            refine ⟨107272208012271280774027009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572118442732113497461477381 107272208012271280774027009)
            ·
              refine ⟨80454156009203460580520257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107272208012271280774027009 80454156009203460580520257)
              ·
                refine ⟨60340617006902595435390193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80454156009203460580520257 60340617006902595435390193)
                ·
                  refine ⟨45255462755176946576542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60340617006902595435390193 45255462755176946576542645)
                  ·
                    refine ⟨4242699633297838741550873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45255462755176946576542645 4242699633297838741550873)
                    ·
                      refine ⟨3182024724973379056163155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242699633297838741550873 3182024724973379056163155)
                      ·
                        rfl

theorem cell23_6196971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5, 2].length) (baseStart_6196971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6196971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6196971 prefixEnd_6196971 := by exact prefixLift 6196971
  have htrace : WordTrace (prefixWord ++ tailWord_6196971) baseStart_6196971 baseEnd_6196971 := by
    simpa [prefixWord, tailWord_6196971, baseEnd_6196971] using wordTrace_append hprefix tailTrace_6196971
  have hstable : (prefixWord ++ tailWord_6196971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6196971).length < 2 ^ (prefixWord ++ tailWord_6196971).sum := by decide
  have hdescent : baseEnd_6196971 < baseStart_6196971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6196971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197011 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 3, 4]
def baseStart_6197011 : Nat := 118140960795 + 6197011 * 2 ^ 59
def prefixEnd_6197011 : Nat := 4983230072969 + 3 ^ 40 * 6197011 * 2
def baseEnd_6197011 : Nat := 1060681754733186299887657

theorem tailTrace_6197011 : CollatzResearch.WordTrace tailWord_6197011 prefixEnd_6197011 1060681754733186299887657 := by
  unfold tailWord_6197011
  simp only [CollatzResearch.WordTrace]
  refine ⟨226023559752294987063150887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150682373168196658042100591 226023559752294987063150887)
  ·
    refine ⟨339035339628442480594726331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226023559752294987063150887 339035339628442480594726331)
    ·
      refine ⟨508553009442663720892089497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339035339628442480594726331 508553009442663720892089497)
      ·
        refine ⟨381414757081997790669067123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508553009442663720892089497 381414757081997790669067123)
        ·
          refine ⟨572122135622996686003600685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381414757081997790669067123 572122135622996686003600685)
          ·
            refine ⟨214545800858623757251350257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572122135622996686003600685 214545800858623757251350257)
            ·
              refine ⟨160909350643967817938512693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214545800858623757251350257 160909350643967817938512693)
              ·
                refine ⟨15085251622871982931735565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160909350643967817938512693 15085251622871982931735565)
                ·
                  refine ⟨5656969358576993599400837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15085251622871982931735565 5656969358576993599400837)
                  ·
                    refine ⟨1060681754733186299887657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656969358576993599400837 1060681754733186299887657)
                    ·
                      rfl

theorem cell23_6197011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 4].length) (baseStart_6197011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197011 prefixEnd_6197011 := by exact prefixLift 6197011
  have htrace : WordTrace (prefixWord ++ tailWord_6197011) baseStart_6197011 baseEnd_6197011 := by
    simpa [prefixWord, tailWord_6197011, baseEnd_6197011] using wordTrace_append hprefix tailTrace_6197011
  have hstable : (prefixWord ++ tailWord_6197011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197011).length < 2 ^ (prefixWord ++ tailWord_6197011).sum := by decide
  have hdescent : baseEnd_6197011 < baseStart_6197011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197148 : List Nat := [2, 2, 3, 3, 1, 2, 1, 9]
def baseStart_6197148 : Nat := 118140960795 + 6197148 * 2 ^ 59
def prefixEnd_6197148 : Nat := 4983230072969 + 3 ^ 40 * 6197148 * 2
def baseEnd_6197148 : Nat := 117856133742563883838883

theorem tailTrace_6197148 : CollatzResearch.WordTrace tailWord_6197148 prefixEnd_6197148 117856133742563883838883 := by
  unfold tailWord_6197148
  simp only [CollatzResearch.WordTrace]
  refine ⟨113014278276399329730444049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150685704368532439640592065 113014278276399329730444049)
  ·
    refine ⟨84760708707299497297833037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113014278276399329730444049 84760708707299497297833037)
    ·
      refine ⟨31785265765237311486687389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84760708707299497297833037 31785265765237311486687389)
      ·
        refine ⟨11919474661963991807507771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31785265765237311486687389 11919474661963991807507771)
        ·
          refine ⟨17879211992945987711261657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11919474661963991807507771 17879211992945987711261657)
          ·
            refine ⟨13409408994709490783446243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17879211992945987711261657 13409408994709490783446243)
            ·
              refine ⟨20114113492064236175169365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13409408994709490783446243 20114113492064236175169365)
              ·
                refine ⟨117856133742563883838883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20114113492064236175169365 117856133742563883838883)
                ·
                  rfl

theorem cell23_6197148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 9].length) (baseStart_6197148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197148 prefixEnd_6197148 := by exact prefixLift 6197148
  have htrace : WordTrace (prefixWord ++ tailWord_6197148) baseStart_6197148 baseEnd_6197148 := by
    simpa [prefixWord, tailWord_6197148, baseEnd_6197148] using wordTrace_append hprefix tailTrace_6197148
  have hstable : (prefixWord ++ tailWord_6197148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197148).length < 2 ^ (prefixWord ++ tailWord_6197148).sum := by decide
  have hdescent : baseEnd_6197148 < baseStart_6197148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197171 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_6197171 : Nat := 118140960795 + 6197171 * 2 ^ 59
def prefixEnd_6197171 : Nat := 4983230072969 + 3 ^ 40 * 6197171 * 2
def baseEnd_6197171 : Nat := 3182127421104278273662235

theorem tailTrace_6197171 : CollatzResearch.WordTrace tailWord_6197171 prefixEnd_6197171 3182127421104278273662235 := by
  unfold tailWord_6197171
  simp only [CollatzResearch.WordTrace]
  refine ⟨226029395431715334388975367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150686263621143556259316911 226029395431715334388975367)
  ·
    refine ⟨339044093147573001583463051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226029395431715334388975367 339044093147573001583463051)
    ·
      refine ⟨508566139721359502375194577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339044093147573001583463051 508566139721359502375194577)
      ·
        refine ⟨381424604791019626781395933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508566139721359502375194577 381424604791019626781395933)
        ·
          refine ⟨143034226796632360043023475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381424604791019626781395933 143034226796632360043023475)
          ·
            refine ⟨214551340194948540064535213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143034226796632360043023475 214551340194948540064535213)
            ·
              refine ⟨80456752573105702524200705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214551340194948540064535213 80456752573105702524200705)
              ·
                refine ⟨60342564429829276893150529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80456752573105702524200705 60342564429829276893150529)
                ·
                  refine ⟨45256923322371957669862897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60342564429829276893150529 45256923322371957669862897)
                  ·
                    refine ⟨33942692491778968252397173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45256923322371957669862897 33942692491778968252397173)
                    ·
                      refine ⟨3182127421104278273662235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33942692491778968252397173 3182127421104278273662235)
                      ·
                        rfl

theorem cell23_6197171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_6197171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197171 prefixEnd_6197171 := by exact prefixLift 6197171
  have htrace : WordTrace (prefixWord ++ tailWord_6197171) baseStart_6197171 baseEnd_6197171 := by
    simpa [prefixWord, tailWord_6197171, baseEnd_6197171] using wordTrace_append hprefix tailTrace_6197171
  have hstable : (prefixWord ++ tailWord_6197171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197171).length < 2 ^ (prefixWord ++ tailWord_6197171).sum := by decide
  have hdescent : baseEnd_6197171 < baseStart_6197171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197175 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_6197175 : Nat := 118140960795 + 6197175 * 2 ^ 59
def prefixEnd_6197175 : Nat := 4983230072969 + 3 ^ 40 * 6197175 * 2
def baseEnd_6197175 : Nat := 3182129475026896258012217

theorem tailTrace_6197175 : CollatzResearch.WordTrace tailWord_6197175 prefixEnd_6197175 3182129475026896258012217 := by
  unfold tailWord_6197175
  simp only [CollatzResearch.WordTrace]
  refine ⟨226029541323700843072120979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150686360882467228714747319 226029541323700843072120979)
  ·
    refine ⟨339044311985551264608181469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226029541323700843072120979 339044311985551264608181469)
    ·
      refine ⟨127141616994581724228068051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339044311985551264608181469 127141616994581724228068051)
      ·
        refine ⟨190712425491872586342102077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127141616994581724228068051 190712425491872586342102077)
        ·
          refine ⟨71517159559452219878288279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190712425491872586342102077 71517159559452219878288279)
          ·
            refine ⟨107275739339178329817432419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71517159559452219878288279 107275739339178329817432419)
            ·
              refine ⟨160913609008767494726148629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107275739339178329817432419 160913609008767494726148629)
              ·
                refine ⟨7542825422285976315288217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160913609008767494726148629 7542825422285976315288217)
                ·
                  refine ⟨5657119066714482236466163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542825422285976315288217 5657119066714482236466163)
                  ·
                    refine ⟨8485678600071723354699245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657119066714482236466163 8485678600071723354699245)
                    ·
                      refine ⟨3182129475026896258012217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8485678600071723354699245 3182129475026896258012217)
                      ·
                        rfl

theorem cell23_6197175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_6197175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197175 prefixEnd_6197175 := by exact prefixLift 6197175
  have htrace : WordTrace (prefixWord ++ tailWord_6197175) baseStart_6197175 baseEnd_6197175 := by
    simpa [prefixWord, tailWord_6197175, baseEnd_6197175] using wordTrace_append hprefix tailTrace_6197175
  have hstable : (prefixWord ++ tailWord_6197175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197175).length < 2 ^ (prefixWord ++ tailWord_6197175).sum := by decide
  have hdescent : baseEnd_6197175 < baseStart_6197175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197191 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 8]
def baseStart_6197191 : Nat := 118140960795 + 6197191 * 2 ^ 59
def prefixEnd_6197191 : Nat := 4983230072969 + 3 ^ 40 * 6197191 * 2
def baseEnd_6197191 : Nat := 1060712563572456065137381

theorem tailTrace_6197191 : CollatzResearch.WordTrace tailWord_6197191 prefixEnd_6197191 1060712563572456065137381 := by
  unfold tailWord_6197191
  simp only [CollatzResearch.WordTrace]
  refine ⟨226030124891642877804703427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150686749927761918536468951 226030124891642877804703427)
  ·
    refine ⟨339045187337464316707055141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226030124891642877804703427 339045187337464316707055141)
    ·
      refine ⟨63570972625774559382572839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339045187337464316707055141 63570972625774559382572839)
      ·
        refine ⟨95356458938661839073859259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63570972625774559382572839 95356458938661839073859259)
        ·
          refine ⟨143034688407992758610788889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95356458938661839073859259 143034688407992758610788889)
          ·
            refine ⟨107276016305994568958091667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143034688407992758610788889 107276016305994568958091667)
            ·
              refine ⟨160914024458991853437137501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107276016305994568958091667 160914024458991853437137501)
              ·
                refine ⟨60342759172121945038926563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160914024458991853437137501 60342759172121945038926563)
                ·
                  refine ⟨90514138758182917558389845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60342759172121945038926563 90514138758182917558389845)
                  ·
                    refine ⟨1060712563572456065137381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90514138758182917558389845 1060712563572456065137381)
                    ·
                      rfl

theorem cell23_6197191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_6197191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197191 prefixEnd_6197191 := by exact prefixLift 6197191
  have htrace : WordTrace (prefixWord ++ tailWord_6197191) baseStart_6197191 baseEnd_6197191 := by
    simpa [prefixWord, tailWord_6197191, baseEnd_6197191] using wordTrace_append hprefix tailTrace_6197191
  have hstable : (prefixWord ++ tailWord_6197191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197191).length < 2 ^ (prefixWord ++ tailWord_6197191).sum := by decide
  have hdescent : baseEnd_6197191 < baseStart_6197191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197192 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_6197192 : Nat := 118140960795 + 6197192 * 2 ^ 59
def prefixEnd_6197192 : Nat := 4983230072969 + 3 ^ 40 * 6197192 * 2
def baseEnd_6197192 : Nat := 3182138204198022691499639

theorem tailTrace_6197192 : CollatzResearch.WordTrace tailWord_6197192 prefixEnd_6197192 3182138204198022691499639 := by
  unfold tailWord_6197192
  simp only [CollatzResearch.WordTrace]
  refine ⟨113015080682319627487744915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150686774243092836650326553 113015080682319627487744915)
  ·
    refine ⟨169522621023479441231617373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113015080682319627487744915 169522621023479441231617373)
    ·
      refine ⟨63570982883804790461856515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169522621023479441231617373 63570982883804790461856515)
      ·
        refine ⟨95356474325707185692784773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63570982883804790461856515 95356474325707185692784773)
        ·
          refine ⟨17879338936070097317397145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95356474325707185692784773 17879338936070097317397145)
          ·
            refine ⟨13409504202052572988047859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17879338936070097317397145 13409504202052572988047859)
            ·
              refine ⟨20114256303078859482071789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13409504202052572988047859 20114256303078859482071789)
              ·
                refine ⟨7542846113654572305776921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20114256303078859482071789 7542846113654572305776921)
                ·
                  refine ⟨5657134585240929229332691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542846113654572305776921 5657134585240929229332691)
                  ·
                    refine ⟨8485701877861393843999037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657134585240929229332691 8485701877861393843999037)
                    ·
                      refine ⟨3182138204198022691499639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8485701877861393843999037 3182138204198022691499639)
                      ·
                        rfl

theorem cell23_6197192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_6197192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197192 prefixEnd_6197192 := by exact prefixLift 6197192
  have htrace : WordTrace (prefixWord ++ tailWord_6197192) baseStart_6197192 baseEnd_6197192 := by
    simpa [prefixWord, tailWord_6197192, baseEnd_6197192] using wordTrace_append hprefix tailTrace_6197192
  have hstable : (prefixWord ++ tailWord_6197192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197192).length < 2 ^ (prefixWord ++ tailWord_6197192).sum := by decide
  have hdescent : baseEnd_6197192 < baseStart_6197192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197215 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 4, 2]
def baseStart_6197215 : Nat := 118140960795 + 6197215 * 2 ^ 59
def prefixEnd_6197215 : Nat := 4983230072969 + 3 ^ 40 * 6197215 * 2
def baseEnd_6197215 : Nat := 3182150014253076101512033

theorem tailTrace_6197215 : CollatzResearch.WordTrace tailWord_6197215 prefixEnd_6197215 3182150014253076101512033 := by
  unfold tailWord_6197215
  simp only [CollatzResearch.WordTrace]
  refine ⟨226031000243555929903577099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150687333495703953269051399 226031000243555929903577099)
  ·
    refine ⟨339046500365333894855365649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226031000243555929903577099 339046500365333894855365649)
    ·
      refine ⟨254284875274000421141524237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339046500365333894855365649 254284875274000421141524237)
      ·
        refine ⟨95356828227750157928071589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254284875274000421141524237 95356828227750157928071589)
        ·
          refine ⟨17879405292703154611513423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95356828227750157928071589 17879405292703154611513423)
          ·
            refine ⟨26819107939054731917270135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17879405292703154611513423 26819107939054731917270135)
            ·
              refine ⟨40228661908582097875905203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26819107939054731917270135 40228661908582097875905203)
              ·
                refine ⟨60342992862873146813857805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40228661908582097875905203 60342992862873146813857805)
                ·
                  refine ⟨22628622323577430055196677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60342992862873146813857805 22628622323577430055196677)
                  ·
                    refine ⟨4242866685670768135349377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22628622323577430055196677 4242866685670768135349377)
                    ·
                      refine ⟨3182150014253076101512033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242866685670768135349377 3182150014253076101512033)
                      ·
                        rfl

theorem cell23_6197215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_6197215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197215 prefixEnd_6197215 := by exact prefixLift 6197215
  have htrace : WordTrace (prefixWord ++ tailWord_6197215) baseStart_6197215 baseEnd_6197215 := by
    simpa [prefixWord, tailWord_6197215, baseEnd_6197215] using wordTrace_append hprefix tailTrace_6197215
  have hstable : (prefixWord ++ tailWord_6197215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197215).length < 2 ^ (prefixWord ++ tailWord_6197215).sum := by decide
  have hdescent : baseEnd_6197215 < baseStart_6197215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197219 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6197219 : Nat := 118140960795 + 6197219 * 2 ^ 59
def prefixEnd_6197219 : Nat := 4983230072969 + 3 ^ 40 * 6197219 * 2
def baseEnd_6197219 : Nat := 3182152068175694085862015

theorem tailTrace_6197219 : CollatzResearch.WordTrace tailWord_6197219 prefixEnd_6197219 3182152068175694085862015 := by
  unfold tailWord_6197219
  simp only [CollatzResearch.WordTrace]
  refine ⟨226031146135541438586722711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150687430757027625724481807 226031146135541438586722711)
  ·
    refine ⟨339046719203312157880084067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226031146135541438586722711 339046719203312157880084067)
    ·
      refine ⟨508570078804968236820126101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339046719203312157880084067 508570078804968236820126101)
      ·
        refine ⟨23839222443982886100943411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 508570078804968236820126101 23839222443982886100943411)
        ·
          refine ⟨35758833665974329151415117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23839222443982886100943411 35758833665974329151415117)
          ·
            refine ⟨13409562624740373431780669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35758833665974329151415117 13409562624740373431780669)
            ·
              refine ⟨5028585984277640036917751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13409562624740373431780669 5028585984277640036917751)
              ·
                refine ⟨7542878976416460055376627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028585984277640036917751 7542878976416460055376627)
                ·
                  refine ⟨11314318464624690083064941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7542878976416460055376627 11314318464624690083064941)
                  ·
                    refine ⟨4242869424234258781149353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11314318464624690083064941 4242869424234258781149353)
                    ·
                      refine ⟨3182152068175694085862015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242869424234258781149353 3182152068175694085862015)
                      ·
                        rfl

theorem cell23_6197219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6197219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197219 prefixEnd_6197219 := by exact prefixLift 6197219
  have htrace : WordTrace (prefixWord ++ tailWord_6197219) baseStart_6197219 baseEnd_6197219 := by
    simpa [prefixWord, tailWord_6197219, baseEnd_6197219] using wordTrace_append hprefix tailTrace_6197219
  have hstable : (prefixWord ++ tailWord_6197219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197219).length < 2 ^ (prefixWord ++ tailWord_6197219).sum := by decide
  have hdescent : baseEnd_6197219 < baseStart_6197219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197232 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2]
def baseStart_6197232 : Nat := 118140960795 + 6197232 * 2 ^ 59
def prefixEnd_6197232 : Nat := 4983230072969 + 3 ^ 40 * 6197232 * 2
def baseEnd_6197232 : Nat := 3182158743424202534999455

theorem tailTrace_6197232 : CollatzResearch.WordTrace tailWord_6197232 prefixEnd_6197232 3182158743424202534999455 := by
  unfold tailWord_6197232
  simp only [CollatzResearch.WordTrace]
  refine ⟨113015810142247170903472975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150687746856329561204630633 113015810142247170903472975)
  ·
    refine ⟨169523715213370756355209463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113015810142247170903472975 169523715213370756355209463)
    ·
      refine ⟨254285572820056134532814195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169523715213370756355209463 254285572820056134532814195)
      ·
        refine ⟨381428359230084201799221293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254285572820056134532814195 381428359230084201799221293)
        ·
          refine ⟨143035634711281575674707985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381428359230084201799221293 143035634711281575674707985)
          ·
            refine ⟨107276726033461181756030989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143035634711281575674707985 107276726033461181756030989)
            ·
              refine ⟨40228772262547943158511621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107276726033461181756030989 40228772262547943158511621)
              ·
                refine ⟨7542894799227739342220929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40228772262547943158511621 7542894799227739342220929)
                ·
                  refine ⟨5657171099420804506665697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542894799227739342220929 5657171099420804506665697)
                  ·
                    refine ⟨4242878324565603379999273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657171099420804506665697 4242878324565603379999273)
                    ·
                      refine ⟨3182158743424202534999455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4242878324565603379999273 3182158743424202534999455)
                      ·
                        rfl

theorem cell23_6197232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 2, 2].length) (baseStart_6197232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197232 prefixEnd_6197232 := by exact prefixLift 6197232
  have htrace : WordTrace (prefixWord ++ tailWord_6197232) baseStart_6197232 baseEnd_6197232 := by
    simpa [prefixWord, tailWord_6197232, baseEnd_6197232] using wordTrace_append hprefix tailTrace_6197232
  have hstable : (prefixWord ++ tailWord_6197232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197232).length < 2 ^ (prefixWord ++ tailWord_6197232).sum := by decide
  have hdescent : baseEnd_6197232 < baseStart_6197232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197348 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_6197348 : Nat := 118140960795 + 6197348 * 2 ^ 59
def prefixEnd_6197348 : Nat := 4983230072969 + 3 ^ 40 * 6197348 * 2
def baseEnd_6197348 : Nat := 3182218307180124081148921

theorem tailTrace_6197348 : CollatzResearch.WordTrace tailWord_6197348 prefixEnd_6197348 3182218307180124081148921 := by
  unfold tailWord_6197348
  simp only [CollatzResearch.WordTrace]
  refine ⟨113017925576037046809084349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150690567434716062412112465 113017925576037046809084349)
  ·
    refine ⟨42381722091013892553406631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113017925576037046809084349 42381722091013892553406631)
    ·
      refine ⟨63572583136520838830109947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42381722091013892553406631 63572583136520838830109947)
      ·
        refine ⟨95358874704781258245164921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63572583136520838830109947 95358874704781258245164921)
        ·
          refine ⟨71519156028585943683873691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95358874704781258245164921 71519156028585943683873691)
          ·
            refine ⟨107278734042878915525810537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71519156028585943683873691 107278734042878915525810537)
            ·
              refine ⟨80459050532159186644357903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107278734042878915525810537 80459050532159186644357903)
              ·
                refine ⟨120688575798238779966536855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80459050532159186644357903 120688575798238779966536855)
                ·
                  refine ⟨181032863697358169949805283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120688575798238779966536855 181032863697358169949805283)
                  ·
                    refine ⟨271549295546037254924707925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181032863697358169949805283 271549295546037254924707925)
                    ·
                      refine ⟨3182218307180124081148921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271549295546037254924707925 3182218307180124081148921)
                      ·
                        rfl

theorem cell23_6197348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_6197348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197348 prefixEnd_6197348 := by exact prefixLift 6197348
  have htrace : WordTrace (prefixWord ++ tailWord_6197348) baseStart_6197348 baseEnd_6197348 := by
    simpa [prefixWord, tailWord_6197348, baseEnd_6197348] using wordTrace_append hprefix tailTrace_6197348
  have hstable : (prefixWord ++ tailWord_6197348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197348).length < 2 ^ (prefixWord ++ tailWord_6197348).sum := by decide
  have hdescent : baseEnd_6197348 < baseStart_6197348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197362 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_6197362 : Nat := 118140960795 + 6197362 * 2 ^ 59
def prefixEnd_6197362 : Nat := 4983230072969 + 3 ^ 40 * 6197362 * 2
def baseEnd_6197362 : Nat := 353580610656587447374873

theorem tailTrace_6197362 : CollatzResearch.WordTrace tailWord_6197362 prefixEnd_6197362 353580610656587447374873 := by
  unfold tailWord_6197362
  simp only [CollatzResearch.WordTrace]
  refine ⟨56509090443505843502294585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150690907849348916006118893 56509090443505843502294585)
  ·
    refine ⟨42381817832629382626720939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56509090443505843502294585 42381817832629382626720939)
    ·
      refine ⟨63572726748944073940081409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42381817832629382626720939 63572726748944073940081409)
      ·
        refine ⟨47679545061708055455061057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63572726748944073940081409 47679545061708055455061057)
        ·
          refine ⟨35759658796281041591295793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47679545061708055455061057 35759658796281041591295793)
          ·
            refine ⟨26819744097210781193471845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35759658796281041591295793 26819744097210781193471845)
            ·
              refine ⟨5028702018227021473775971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26819744097210781193471845 5028702018227021473775971)
              ·
                refine ⟨7543053027340532210663957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028702018227021473775971 7543053027340532210663957)
                ·
                  refine ⟨353580610656587447374873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7543053027340532210663957 353580610656587447374873)
                  ·
                    rfl

theorem cell23_6197362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_6197362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197362 prefixEnd_6197362 := by exact prefixLift 6197362
  have htrace : WordTrace (prefixWord ++ tailWord_6197362) baseStart_6197362 baseEnd_6197362 := by
    simpa [prefixWord, tailWord_6197362, baseEnd_6197362] using wordTrace_append hprefix tailTrace_6197362
  have hstable : (prefixWord ++ tailWord_6197362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197362).length < 2 ^ (prefixWord ++ tailWord_6197362).sum := by decide
  have hdescent : baseEnd_6197362 < baseStart_6197362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197392 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_6197392 : Nat := 118140960795 + 6197392 * 2 ^ 59
def prefixEnd_6197392 : Nat := 4983230072969 + 3 ^ 40 * 6197392 * 2
def baseEnd_6197392 : Nat := 1060746966776307302999573

theorem tailTrace_6197392 : CollatzResearch.WordTrace tailWord_6197392 prefixEnd_6197392 1060746966776307302999573 := by
  unfold tailWord_6197392
  simp only [CollatzResearch.WordTrace]
  refine ⟨113018727981957344566385215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150691637309276459421846953 113018727981957344566385215)
  ·
    refine ⟨169528091972936016849577823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113018727981957344566385215 169528091972936016849577823)
    ·
      refine ⟨254292137959404025274366735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169528091972936016849577823 254292137959404025274366735)
      ·
        refine ⟨381438206939106037911550103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254292137959404025274366735 381438206939106037911550103)
        ·
          refine ⟨572157310408659056867325155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381438206939106037911550103 572157310408659056867325155)
          ·
            refine ⟨858235965612988585300987733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572157310408659056867325155 858235965612988585300987733)
            ·
              refine ⟨5028726361013604991997975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 858235965612988585300987733 5028726361013604991997975)
              ·
                refine ⟨7543089541520407487996963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028726361013604991997975 7543089541520407487996963)
                ·
                  refine ⟨11314634312280611231995445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543089541520407487996963 11314634312280611231995445)
                  ·
                    refine ⟨1060746966776307302999573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11314634312280611231995445 1060746966776307302999573)
                    ·
                      rfl

theorem cell23_6197392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_6197392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197392 prefixEnd_6197392 := by exact prefixLift 6197392
  have htrace : WordTrace (prefixWord ++ tailWord_6197392) baseStart_6197392 baseEnd_6197392 := by
    simpa [prefixWord, tailWord_6197392, baseEnd_6197392] using wordTrace_append hprefix tailTrace_6197392
  have hstable : (prefixWord ++ tailWord_6197392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197392).length < 2 ^ (prefixWord ++ tailWord_6197392).sum := by decide
  have hdescent : baseEnd_6197392 < baseStart_6197392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197432 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_6197432 : Nat := 118140960795 + 6197432 * 2 ^ 59
def prefixEnd_6197432 : Nat := 4983230072969 + 3 ^ 40 * 6197432 * 2
def baseEnd_6197432 : Nat := 3182261439555101752498535

theorem tailTrace_6197432 : CollatzResearch.WordTrace tailWord_6197432 prefixEnd_6197432 3182261439555101752498535 := by
  unfold tailWord_6197432
  simp only [CollatzResearch.WordTrace]
  refine ⟨113019457441884887982113275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150692609922513183976151033 113019457441884887982113275)
  ·
    refine ⟨169529186162827331973169913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113019457441884887982113275 169529186162827331973169913)
    ·
      refine ⟨127146889622120498979877435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169529186162827331973169913 127146889622120498979877435)
      ·
        refine ⟨190720334433180748469816153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127146889622120498979877435 190720334433180748469816153)
        ·
          refine ⟨143040250824885561352362115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190720334433180748469816153 143040250824885561352362115)
          ·
            refine ⟨214560376237328342028543173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143040250824885561352362115 214560376237328342028543173)
            ·
              refine ⟨40230070544499064130351845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214560376237328342028543173 40230070544499064130351845)
              ·
                refine ⟨7543138227093574524440971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40230070544499064130351845 7543138227093574524440971)
                ·
                  refine ⟨11314707340640361786661457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543138227093574524440971 11314707340640361786661457)
                  ·
                    refine ⟨8486030505480271339996093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11314707340640361786661457 8486030505480271339996093)
                    ·
                      refine ⟨3182261439555101752498535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486030505480271339996093 3182261439555101752498535)
                      ·
                        rfl

theorem cell23_6197432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_6197432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197432 prefixEnd_6197432 := by exact prefixLift 6197432
  have htrace : WordTrace (prefixWord ++ tailWord_6197432) baseStart_6197432 baseEnd_6197432 := by
    simpa [prefixWord, tailWord_6197432, baseEnd_6197432] using wordTrace_append hprefix tailTrace_6197432
  have hstable : (prefixWord ++ tailWord_6197432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197432).length < 2 ^ (prefixWord ++ tailWord_6197432).sum := by decide
  have hdescent : baseEnd_6197432 < baseStart_6197432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197435 : List Nat := [1, 1, 1, 1, 1, 2, 9, 7]
def baseStart_6197435 : Nat := 118140960795 + 6197435 * 2 ^ 59
def prefixEnd_6197435 : Nat := 4983230072969 + 3 ^ 40 * 6197435 * 2
def baseEnd_6197435 : Nat := 117861591851743157065223

theorem tailTrace_6197435 : CollatzResearch.WordTrace tailWord_6197435 prefixEnd_6197435 117861591851743157065223 := by
  unfold tailWord_6197435
  simp only [CollatzResearch.WordTrace]
  refine ⟨226039024302758907476585759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150692682868505938317723839 226039024302758907476585759)
  ·
    refine ⟨339058536454138361214878639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226039024302758907476585759 339058536454138361214878639)
    ·
      refine ⟨508587804681207541822317959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339058536454138361214878639 508587804681207541822317959)
      ·
        refine ⟨762881707021811312733476939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508587804681207541822317959 762881707021811312733476939)
        ·
          refine ⟨1144322560532716969100215409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762881707021811312733476939 1144322560532716969100215409)
          ·
            refine ⟨858241920399537726825161557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144322560532716969100215409 858241920399537726825161557)
            ·
              refine ⟨5028761252341041368116181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 858241920399537726825161557 5028761252341041368116181)
              ·
                refine ⟨117861591851743157065223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5028761252341041368116181 117861591851743157065223)
                ·
                  rfl

theorem cell23_6197435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 7].length) (baseStart_6197435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197435 prefixEnd_6197435 := by exact prefixLift 6197435
  have htrace : WordTrace (prefixWord ++ tailWord_6197435) baseStart_6197435 baseEnd_6197435 := by
    simpa [prefixWord, tailWord_6197435, baseEnd_6197435] using wordTrace_append hprefix tailTrace_6197435
  have hstable : (prefixWord ++ tailWord_6197435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197435).length < 2 ^ (prefixWord ++ tailWord_6197435).sum := by decide
  have hdescent : baseEnd_6197435 < baseStart_6197435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197452 : List Nat := [2, 2, 1, 6, 1, 1, 10]
def baseStart_6197452 : Nat := 118140960795 + 6197452 * 2 ^ 59
def prefixEnd_6197452 : Nat := 4983230072969 + 3 ^ 40 * 6197452 * 2
def baseEnd_6197452 : Nat := 39287305051459156472203

theorem tailTrace_6197452 : CollatzResearch.WordTrace tailWord_6197452 prefixEnd_6197452 39287305051459156472203 := by
  unfold tailWord_6197452
  simp only [CollatzResearch.WordTrace]
  refine ⟨113019822171848659689977305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150693096229131546253303073 113019822171848659689977305)
  ·
    refine ⟨84764866628886494767482979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113019822171848659689977305 84764866628886494767482979)
    ·
      refine ⟨127147299943329742151224469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84764866628886494767482979 127147299943329742151224469)
      ·
        refine ⟨5960029684843581663338647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127147299943329742151224469 5960029684843581663338647)
        ·
          refine ⟨8940044527265372495007971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960029684843581663338647 8940044527265372495007971)
          ·
            refine ⟨13410066790898058742511957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940044527265372495007971 13410066790898058742511957)
            ·
              refine ⟨39287305051459156472203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13410066790898058742511957 39287305051459156472203)
              ·
                rfl

theorem cell23_6197452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 10].length) (baseStart_6197452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197452 prefixEnd_6197452 := by exact prefixLift 6197452
  have htrace : WordTrace (prefixWord ++ tailWord_6197452) baseStart_6197452 baseEnd_6197452 := by
    simpa [prefixWord, tailWord_6197452, baseEnd_6197452] using wordTrace_append hprefix tailTrace_6197452
  have hstable : (prefixWord ++ tailWord_6197452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197452).length < 2 ^ (prefixWord ++ tailWord_6197452).sum := by decide
  have hdescent : baseEnd_6197452 < baseStart_6197452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197479 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6197479 : Nat := 118140960795 + 6197479 * 2 ^ 59
def prefixEnd_6197479 : Nat := 4983230072969 + 3 ^ 40 * 6197479 * 2
def baseEnd_6197479 : Nat := 3182285573145863068610819

theorem tailTrace_6197479 : CollatzResearch.WordTrace tailWord_6197479 prefixEnd_6197479 3182285573145863068610819 := by
  unfold tailWord_6197479
  simp only [CollatzResearch.WordTrace]
  refine ⟨226040629114599502991187491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150693752743066335327458327 226040629114599502991187491)
  ·
    refine ⟨339060943671899254486781237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226040629114599502991187491 339060943671899254486781237)
    ·
      refine ⟨31786963469240555108135741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339060943671899254486781237 31786963469240555108135741)
      ·
        refine ⟨11920111300965208165550903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31786963469240555108135741 11920111300965208165550903)
        ·
          refine ⟨17880166951447812248326355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11920111300965208165550903 17880166951447812248326355)
          ·
            refine ⟨26820250427171718372489533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17880166951447812248326355 26820250427171718372489533)
            ·
              refine ⟨10057593910189394389683575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26820250427171718372489533 10057593910189394389683575)
              ·
                refine ⟨15086390865284091584525363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10057593910189394389683575 15086390865284091584525363)
                ·
                  refine ⟨22629586297926137376788045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15086390865284091584525363 22629586297926137376788045)
                  ·
                    refine ⟨8486094861722301516295517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22629586297926137376788045 8486094861722301516295517)
                    ·
                      refine ⟨3182285573145863068610819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486094861722301516295517 3182285573145863068610819)
                      ·
                        rfl

theorem cell23_6197479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6197479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197479 prefixEnd_6197479 := by exact prefixLift 6197479
  have htrace : WordTrace (prefixWord ++ tailWord_6197479) baseStart_6197479 baseEnd_6197479 := by
    simpa [prefixWord, tailWord_6197479, baseEnd_6197479] using wordTrace_append hprefix tailTrace_6197479
  have hstable : (prefixWord ++ tailWord_6197479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197479).length < 2 ^ (prefixWord ++ tailWord_6197479).sum := by decide
  have hdescent : baseEnd_6197479 < baseStart_6197479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197489 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_6197489 : Nat := 118140960795 + 6197489 * 2 ^ 59
def prefixEnd_6197489 : Nat := 4983230072969 + 3 ^ 40 * 6197489 * 2
def baseEnd_6197489 : Nat := 3182290707952408029485773

theorem tailTrace_6197489 : CollatzResearch.WordTrace tailWord_6197489 prefixEnd_6197489 3182290707952408029485773 := by
  unfold tailWord_6197489
  simp only [CollatzResearch.WordTrace]
  refine ⟨226040993844563274699051521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150693995896375516466034347 226040993844563274699051521)
  ·
    refine ⟨169530745383422456024288641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226040993844563274699051521 169530745383422456024288641)
    ·
      refine ⟨127148059037566842018216481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169530745383422456024288641 127148059037566842018216481)
      ·
        refine ⟨95361044278175131513662361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127148059037566842018216481 95361044278175131513662361)
        ·
          refine ⟨71520783208631348635246771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95361044278175131513662361 71520783208631348635246771)
          ·
            refine ⟨107281174812947022952870157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71520783208631348635246771 107281174812947022952870157)
            ·
              refine ⟨40230440554855133607326309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107281174812947022952870157 40230440554855133607326309)
              ·
                refine ⟨7543207604035337551373683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40230440554855133607326309 7543207604035337551373683)
                ·
                  refine ⟨11314811406053006327060525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543207604035337551373683 11314811406053006327060525)
                  ·
                    refine ⟨4243054277269877372647697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11314811406053006327060525 4243054277269877372647697)
                    ·
                      refine ⟨3182290707952408029485773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243054277269877372647697 3182290707952408029485773)
                      ·
                        rfl

theorem cell23_6197489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_6197489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197489 prefixEnd_6197489 := by exact prefixLift 6197489
  have htrace : WordTrace (prefixWord ++ tailWord_6197489) baseStart_6197489 baseEnd_6197489 := by
    simpa [prefixWord, tailWord_6197489, baseEnd_6197489] using wordTrace_append hprefix tailTrace_6197489
  have hstable : (prefixWord ++ tailWord_6197489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197489).length < 2 ^ (prefixWord ++ tailWord_6197489).sum := by decide
  have hdescent : baseEnd_6197489 < baseStart_6197489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197530 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_6197530 : Nat := 118140960795 + 6197530 * 2 ^ 59
def prefixEnd_6197530 : Nat := 4983230072969 + 3 ^ 40 * 6197530 * 2
def baseEnd_6197530 : Nat := 3182311760659242369073085

theorem tailTrace_6197530 : CollatzResearch.WordTrace tailWord_6197530 prefixEnd_6197530 3182311760659242369073085 := by
  unfold tailWord_6197530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56510622309353684675323511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150694992824943159134196029 56510622309353684675323511)
  ·
    refine ⟨84765933464030527012985267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56510622309353684675323511 84765933464030527012985267)
    ·
      refine ⟨127148900196045790519477901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84765933464030527012985267 127148900196045790519477901)
      ·
        refine ⟨47680837573517171444804213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127148900196045790519477901 47680837573517171444804213)
        ·
          refine ⟨4470078522517234822950395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47680837573517171444804213 4470078522517234822950395)
          ·
            refine ⟨6705117783775852234425593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470078522517234822950395 6705117783775852234425593)
            ·
              refine ⟨5028838337831889175819195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705117783775852234425593 5028838337831889175819195)
              ·
                refine ⟨7543257506747833763728793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028838337831889175819195 7543257506747833763728793)
                ·
                  refine ⟨5657443130060875322796595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543257506747833763728793 5657443130060875322796595)
                  ·
                    refine ⟨8486164695091312984194893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657443130060875322796595 8486164695091312984194893)
                    ·
                      refine ⟨3182311760659242369073085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486164695091312984194893 3182311760659242369073085)
                      ·
                        rfl

theorem cell23_6197530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_6197530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197530 prefixEnd_6197530 := by exact prefixLift 6197530
  have htrace : WordTrace (prefixWord ++ tailWord_6197530) baseStart_6197530 baseEnd_6197530 := by
    simpa [prefixWord, tailWord_6197530, baseEnd_6197530] using wordTrace_append hprefix tailTrace_6197530
  have hstable : (prefixWord ++ tailWord_6197530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197530).length < 2 ^ (prefixWord ++ tailWord_6197530).sum := by decide
  have hdescent : baseEnd_6197530 < baseStart_6197530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197636 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_6197636 : Nat := 118140960795 + 6197636 * 2 ^ 59
def prefixEnd_6197636 : Nat := 4983230072969 + 3 ^ 40 * 6197636 * 2
def baseEnd_6197636 : Nat := 1060788729869539651449199

theorem tailTrace_6197636 : CollatzResearch.WordTrace tailWord_6197636 prefixEnd_6197636 1060788729869539651449199 := by
  unfold tailWord_6197636
  simp only [CollatzResearch.WordTrace]
  refine ⟨113023177687515359402326381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150697570250020479203101841 113023177687515359402326381)
  ·
    refine ⟨42383691632818259775872393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113023177687515359402326381 42383691632818259775872393)
    ·
      refine ⟨31787768724613694831904295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42383691632818259775872393 31787768724613694831904295)
      ·
        refine ⟨47681653086920542247856443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31787768724613694831904295 47681653086920542247856443)
        ·
          refine ⟨71522479630380813371784665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47681653086920542247856443 71522479630380813371784665)
          ·
            refine ⟨53641859722785610028838499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71522479630380813371784665 53641859722785610028838499)
            ·
              refine ⟨80462789584178415043257749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53641859722785610028838499 80462789584178415043257749)
              ·
                refine ⟨3771693261758363205152707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80462789584178415043257749 3771693261758363205152707)
                ·
                  refine ⟨5657539892637544807729061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771693261758363205152707 5657539892637544807729061)
                  ·
                    refine ⟨1060788729869539651449199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5657539892637544807729061 1060788729869539651449199)
                    ·
                      rfl

theorem cell23_6197636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_6197636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197636 prefixEnd_6197636 := by exact prefixLift 6197636
  have htrace : WordTrace (prefixWord ++ tailWord_6197636) baseStart_6197636 baseEnd_6197636 := by
    simpa [prefixWord, tailWord_6197636, baseEnd_6197636] using wordTrace_append hprefix tailTrace_6197636
  have hstable : (prefixWord ++ tailWord_6197636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197636).length < 2 ^ (prefixWord ++ tailWord_6197636).sum := by decide
  have hdescent : baseEnd_6197636 < baseStart_6197636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197669 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_6197669 : Nat := 118140960795 + 6197669 * 2 ^ 59
def prefixEnd_6197669 : Nat := 4983230072969 + 3 ^ 40 * 6197669 * 2
def baseEnd_6197669 : Nat := 3182383134470217325234945

theorem tailTrace_6197669 : CollatzResearch.WordTrace tailWord_6197669 prefixEnd_6197669 3182383134470217325234945 := by
  unfold tailWord_6197669
  simp only [CollatzResearch.WordTrace]
  refine ⟨226047558983911165440604061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150698372655940776960402707 226047558983911165440604061)
  ·
    refine ⟨84767834618966687040226523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226047558983911165440604061 84767834618966687040226523)
    ·
      refine ⟨127151751928450030560339785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84767834618966687040226523 127151751928450030560339785)
      ·
        refine ⟨95363813946337522920254839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127151751928450030560339785 95363813946337522920254839)
        ·
          refine ⟨143045720919506284380382259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95363813946337522920254839 143045720919506284380382259)
          ·
            refine ⟨214568581379259426570573389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143045720919506284380382259 214568581379259426570573389)
            ·
              refine ⟨80463218017222284963965021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214568581379259426570573389 80463218017222284963965021)
              ·
                refine ⟨30173706756458356861486883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80463218017222284963965021 30173706756458356861486883)
                ·
                  refine ⟨45260560134687535292230325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30173706756458356861486883 45260560134687535292230325)
                  ·
                    refine ⟨4243177512626956433646593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45260560134687535292230325 4243177512626956433646593)
                    ·
                      refine ⟨3182383134470217325234945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243177512626956433646593 3182383134470217325234945)
                      ·
                        rfl

theorem cell23_6197669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_6197669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197669 prefixEnd_6197669 := by exact prefixLift 6197669
  have htrace : WordTrace (prefixWord ++ tailWord_6197669) baseStart_6197669 baseEnd_6197669 := by
    simpa [prefixWord, tailWord_6197669, baseEnd_6197669] using wordTrace_append hprefix tailTrace_6197669
  have hstable : (prefixWord ++ tailWord_6197669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197669).length < 2 ^ (prefixWord ++ tailWord_6197669).sum := by decide
  have hdescent : baseEnd_6197669 < baseStart_6197669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197693 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_6197693 : Nat := 118140960795 + 6197693 * 2 ^ 59
def prefixEnd_6197693 : Nat := 4983230072969 + 3 ^ 40 * 6197693 * 2
def baseEnd_6197693 : Nat := 3182395458005925231334835

theorem tailTrace_6197693 : CollatzResearch.WordTrace tailWord_6197693 prefixEnd_6197693 3182395458005925231334835 := by
  unfold tailWord_6197693
  simp only [CollatzResearch.WordTrace]
  refine ⟨226048434335824217539477733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150698956223882811692985155 226048434335824217539477733)
  ·
    refine ⟨42384081437967040788652075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226048434335824217539477733 42384081437967040788652075)
    ·
      refine ⟨63576122156950561182978113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42384081437967040788652075 63576122156950561182978113)
      ·
        refine ⟨47682091617712920887233585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63576122156950561182978113 47682091617712920887233585)
        ·
          refine ⟨35761568713284690665425189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47682091617712920887233585 35761568713284690665425189)
          ·
            refine ⟨6705294133740879499767223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35761568713284690665425189 6705294133740879499767223)
            ·
              refine ⟨10057941200611319249650835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705294133740879499767223 10057941200611319249650835)
              ·
                refine ⟨15086911800916978874476253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10057941200611319249650835 15086911800916978874476253)
                ·
                  refine ⟨5657591925343867077928595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15086911800916978874476253 5657591925343867077928595)
                  ·
                    refine ⟨8486387888015800616892893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657591925343867077928595 8486387888015800616892893)
                    ·
                      refine ⟨3182395458005925231334835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486387888015800616892893 3182395458005925231334835)
                      ·
                        rfl

theorem cell23_6197693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_6197693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197693 prefixEnd_6197693 := by exact prefixLift 6197693
  have htrace : WordTrace (prefixWord ++ tailWord_6197693) baseStart_6197693 baseEnd_6197693 := by
    simpa [prefixWord, tailWord_6197693, baseEnd_6197693] using wordTrace_append hprefix tailTrace_6197693
  have hstable : (prefixWord ++ tailWord_6197693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197693).length < 2 ^ (prefixWord ++ tailWord_6197693).sum := by decide
  have hdescent : baseEnd_6197693 < baseStart_6197693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197700 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 6]
def baseStart_6197700 : Nat := 118140960795 + 6197700 * 2 ^ 59
def prefixEnd_6197700 : Nat := 4983230072969 + 3 ^ 40 * 6197700 * 2
def baseEnd_6197700 : Nat := 353599894707834078216367

theorem tailTrace_6197700 : CollatzResearch.WordTrace tailWord_6197700 prefixEnd_6197700 353599894707834078216367 := by
  unfold tailWord_6197700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113024344823399428867491277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150699126431199238489988369 113024344823399428867491277)
  ·
    refine ⟨42384129308774785825309229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113024344823399428867491277 42384129308774785825309229)
    ·
      refine ⟨15894048490790544684490961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42384129308774785825309229 15894048490790544684490961)
      ·
        refine ⟨11920536368092908513368221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15894048490790544684490961 11920536368092908513368221)
        ·
          refine ⟨4470201138034840692513083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11920536368092908513368221 4470201138034840692513083)
          ·
            refine ⟨6705301707052261038769625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470201138034840692513083 6705301707052261038769625)
            ·
              refine ⟨5028976280289195779077219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705301707052261038769625 5028976280289195779077219)
              ·
                refine ⟨7543464420433793668615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028976280289195779077219 7543464420433793668615829)
                ·
                  refine ⟨353599894707834078216367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7543464420433793668615829 353599894707834078216367)
                  ·
                    rfl

theorem cell23_6197700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_6197700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197700 prefixEnd_6197700 := by exact prefixLift 6197700
  have htrace : WordTrace (prefixWord ++ tailWord_6197700) baseStart_6197700 baseEnd_6197700 := by
    simpa [prefixWord, tailWord_6197700, baseEnd_6197700] using wordTrace_append hprefix tailTrace_6197700
  have hstable : (prefixWord ++ tailWord_6197700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197700).length < 2 ^ (prefixWord ++ tailWord_6197700).sum := by decide
  have hdescent : baseEnd_6197700 < baseStart_6197700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197716 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6197716 : Nat := 118140960795 + 6197716 * 2 ^ 59
def prefixEnd_6197716 : Nat := 4983230072969 + 3 ^ 40 * 6197716 * 2
def baseEnd_6197716 : Nat := 3182407268060978641347229

theorem tailTrace_6197716 : CollatzResearch.WordTrace tailWord_6197716 prefixEnd_6197716 3182407268060978641347229 := by
  unfold tailWord_6197716
  simp only [CollatzResearch.WordTrace]
  refine ⟨113024636607370446233782501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150699515476493928311710001 113024636607370446233782501)
  ·
    refine ⟨21192119363881958668834219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113024636607370446233782501 21192119363881958668834219)
    ·
      refine ⟨31788179045822938003251329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21192119363881958668834219 31788179045822938003251329)
      ·
        refine ⟨23841134284367203502438497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31788179045822938003251329 23841134284367203502438497)
        ·
          refine ⟨17880850713275402626828873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23841134284367203502438497 17880850713275402626828873)
          ·
            refine ⟨13410638034956551970121655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17880850713275402626828873 13410638034956551970121655)
            ·
              refine ⟨20115957052434827955182483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13410638034956551970121655 20115957052434827955182483)
              ·
                refine ⟨30173935578652241932773725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20115957052434827955182483 30173935578652241932773725)
                ·
                  refine ⟨11315225841994590724790147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30173935578652241932773725 11315225841994590724790147)
                  ·
                    refine ⟨16972838762991886087185221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11315225841994590724790147 16972838762991886087185221)
                    ·
                      refine ⟨3182407268060978641347229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16972838762991886087185221 3182407268060978641347229)
                      ·
                        rfl

theorem cell23_6197716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6197716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197716 prefixEnd_6197716 := by exact prefixLift 6197716
  have htrace : WordTrace (prefixWord ++ tailWord_6197716) baseStart_6197716 baseEnd_6197716 := by
    simpa [prefixWord, tailWord_6197716, baseEnd_6197716] using wordTrace_append hprefix tailTrace_6197716
  have hstable : (prefixWord ++ tailWord_6197716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197716).length < 2 ^ (prefixWord ++ tailWord_6197716).sum := by decide
  have hdescent : baseEnd_6197716 < baseStart_6197716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197722 : List Nat := [3, 1, 1, 2, 3, 1, 1, 11]
def baseStart_6197722 : Nat := 118140960795 + 6197722 * 2 ^ 59
def prefixEnd_6197722 : Nat := 4983230072969 + 3 ^ 40 * 6197722 * 2
def baseEnd_6197722 : Nat := 117867049960922430291563

theorem tailTrace_6197722 : CollatzResearch.WordTrace tailWord_6197722 prefixEnd_6197722 117867049960922430291563 := by
  unfold tailWord_6197722
  simp only [CollatzResearch.WordTrace]
  refine ⟨56512373013179788873070855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150699661368479436994855613 56512373013179788873070855)
  ·
    refine ⟨84768559519769683309606283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56512373013179788873070855 84768559519769683309606283)
    ·
      refine ⟨127152839279654524964409425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84768559519769683309606283 127152839279654524964409425)
      ·
        refine ⟨95364629459740893723307069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127152839279654524964409425 95364629459740893723307069)
        ·
          refine ⟨35761736047402835146240151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95364629459740893723307069 35761736047402835146240151)
          ·
            refine ⟨53642604071104252719360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35761736047402835146240151 53642604071104252719360227)
            ·
              refine ⟨80463906106656379079040341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53642604071104252719360227 80463906106656379079040341)
              ·
                refine ⟨117867049960922430291563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80463906106656379079040341 117867049960922430291563)
                ·
                  rfl

theorem cell23_6197722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_6197722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197722 prefixEnd_6197722 := by exact prefixLift 6197722
  have htrace : WordTrace (prefixWord ++ tailWord_6197722) baseStart_6197722 baseEnd_6197722 := by
    simpa [prefixWord, tailWord_6197722, baseEnd_6197722] using wordTrace_append hprefix tailTrace_6197722
  have hstable : (prefixWord ++ tailWord_6197722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197722).length < 2 ^ (prefixWord ++ tailWord_6197722).sum := by decide
  have hdescent : baseEnd_6197722 < baseStart_6197722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197729 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6197729 : Nat := 118140960795 + 6197729 * 2 ^ 59
def prefixEnd_6197729 : Nat := 4983230072969 + 3 ^ 40 * 6197729 * 2
def baseEnd_6197729 : Nat := 3182413943309487090484669

theorem tailTrace_6197729 : CollatzResearch.WordTrace tailWord_6197729 prefixEnd_6197729 3182413943309487090484669 := by
  unfold tailWord_6197729
  simp only [CollatzResearch.WordTrace]
  refine ⟨226049747363693795687788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150699831575795863791858827 226049747363693795687788241)
  ·
    refine ⟨169537310522770346765841181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226049747363693795687788241 169537310522770346765841181)
    ·
      refine ⟨63576491446038880037190443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169537310522770346765841181 63576491446038880037190443)
      ·
        refine ⟨95364737169058320055785665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63576491446038880037190443 95364737169058320055785665)
        ·
          refine ⟨71523552876793740041839249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95364737169058320055785665 71523552876793740041839249)
          ·
            refine ⟨53642664657595305031379437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71523552876793740041839249 53642664657595305031379437)
            ·
              refine ⟨20115999246598239386767289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53642664657595305031379437 20115999246598239386767289)
              ·
                refine ⟨15086999434948679540075467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20115999246598239386767289 15086999434948679540075467)
                ·
                  refine ⟨22630499152423019310113201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15086999434948679540075467 22630499152423019310113201)
                  ·
                    refine ⟨16972874364317264482584901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22630499152423019310113201 16972874364317264482584901)
                    ·
                      refine ⟨3182413943309487090484669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16972874364317264482584901 3182413943309487090484669)
                      ·
                        rfl

theorem cell23_6197729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6197729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197729 prefixEnd_6197729 := by exact prefixLift 6197729
  have htrace : WordTrace (prefixWord ++ tailWord_6197729) baseStart_6197729 baseEnd_6197729 := by
    simpa [prefixWord, tailWord_6197729, baseEnd_6197729] using wordTrace_append hprefix tailTrace_6197729
  have hstable : (prefixWord ++ tailWord_6197729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197729).length < 2 ^ (prefixWord ++ tailWord_6197729).sum := by decide
  have hdescent : baseEnd_6197729 < baseStart_6197729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197736 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6197736 : Nat := 118140960795 + 6197736 * 2 ^ 59
def prefixEnd_6197736 : Nat := 4983230072969 + 3 ^ 40 * 6197736 * 2
def baseEnd_6197736 : Nat := 3182417537674068563097137

theorem tailTrace_6197736 : CollatzResearch.WordTrace tailWord_6197736 prefixEnd_6197736 3182417537674068563097137 := by
  unfold tailWord_6197736
  simp only [CollatzResearch.WordTrace]
  refine ⟨113025001337334217941646531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150700001783112290588862041 113025001337334217941646531)
  ·
    refine ⟨169537502006001326912469797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113025001337334217941646531 169537502006001326912469797)
    ·
      refine ⟨31788281626125248796088087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169537502006001326912469797 31788281626125248796088087)
      ·
        refine ⟨47682422439187873194132131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31788281626125248796088087 47682422439187873194132131)
        ·
          refine ⟨71523633658781809791198197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47682422439187873194132131 71523633658781809791198197)
          ·
            refine ⟨6705340655510794667924831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71523633658781809791198197 6705340655510794667924831)
            ·
              refine ⟨10058010983266192001887247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705340655510794667924831 10058010983266192001887247)
              ·
                refine ⟨15087016474899288002830871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10058010983266192001887247 15087016474899288002830871)
                ·
                  refine ⟨22630524712348932004246307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15087016474899288002830871 22630524712348932004246307)
                  ·
                    refine ⟨33945787068523398006369461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22630524712348932004246307 33945787068523398006369461)
                    ·
                      refine ⟨3182417537674068563097137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33945787068523398006369461 3182417537674068563097137)
                      ·
                        rfl

theorem cell23_6197736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6197736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197736 prefixEnd_6197736 := by exact prefixLift 6197736
  have htrace : WordTrace (prefixWord ++ tailWord_6197736) baseStart_6197736 baseEnd_6197736 := by
    simpa [prefixWord, tailWord_6197736, baseEnd_6197736] using wordTrace_append hprefix tailTrace_6197736
  have hstable : (prefixWord ++ tailWord_6197736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197736).length < 2 ^ (prefixWord ++ tailWord_6197736).sum := by decide
  have hdescent : baseEnd_6197736 < baseStart_6197736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197752 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_6197752 : Nat := 118140960795 + 6197752 * 2 ^ 59
def prefixEnd_6197752 : Nat := 4983230072969 + 3 ^ 40 * 6197752 * 2
def baseEnd_6197752 : Nat := 1060808584454846833499021

theorem tailTrace_6197752 : CollatzResearch.WordTrace tailWord_6197752 prefixEnd_6197752 1060808584454846833499021 := by
  unfold tailWord_6197752
  simp only [CollatzResearch.WordTrace]
  refine ⟨113025293121305235307937755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150700390828406980410583673 113025293121305235307937755)
  ·
    refine ⟨169537939681957852961906633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113025293121305235307937755 169537939681957852961906633)
    ·
      refine ⟨127153454761468389721429975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169537939681957852961906633 127153454761468389721429975)
      ·
        refine ⟨190730182142202584582144963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127153454761468389721429975 190730182142202584582144963)
        ·
          refine ⟨286095273213303876873217445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190730182142202584582144963 286095273213303876873217445)
          ·
            refine ⟨53642863727494476913728271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286095273213303876873217445 53642863727494476913728271)
            ·
              refine ⟨80464295591241715370592407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53642863727494476913728271 80464295591241715370592407)
              ·
                refine ⟨120696443386862573055888611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80464295591241715370592407 120696443386862573055888611)
                ·
                  refine ⟨181044665080293859583832917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120696443386862573055888611 181044665080293859583832917)
                  ·
                    refine ⟨1060808584454846833499021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181044665080293859583832917 1060808584454846833499021)
                    ·
                      rfl

theorem cell23_6197752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_6197752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197752 prefixEnd_6197752 := by exact prefixLift 6197752
  have htrace : WordTrace (prefixWord ++ tailWord_6197752) baseStart_6197752 baseEnd_6197752 := by
    simpa [prefixWord, tailWord_6197752, baseEnd_6197752] using wordTrace_append hprefix tailTrace_6197752
  have hstable : (prefixWord ++ tailWord_6197752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197752).length < 2 ^ (prefixWord ++ tailWord_6197752).sum := by decide
  have hdescent : baseEnd_6197752 < baseStart_6197752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197793 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6197793 : Nat := 118140960795 + 6197793 * 2 ^ 59
def prefixEnd_6197793 : Nat := 4983230072969 + 3 ^ 40 * 6197793 * 2
def baseEnd_6197793 : Nat := 3182446806071374840084375

theorem tailTrace_6197793 : CollatzResearch.WordTrace tailWord_6197793 prefixEnd_6197793 3182446806071374840084375 := by
  unfold tailWord_6197793
  simp only [CollatzResearch.WordTrace]
  refine ⟨226052081635461934618118033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150701387756974623078745355 226052081635461934618118033)
  ·
    refine ⟨169539061226596450963588525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226052081635461934618118033 169539061226596450963588525)
    ·
      refine ⟨63577147959973669111345697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169539061226596450963588525 63577147959973669111345697)
      ·
        refine ⟨47682860969980251833509273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63577147959973669111345697 47682860969980251833509273)
        ·
          refine ⟨35762145727485188875131955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47682860969980251833509273 35762145727485188875131955)
          ·
            refine ⟨53643218591227783312697933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35762145727485188875131955 53643218591227783312697933)
            ·
              refine ⟨20116206971710418742261725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53643218591227783312697933 20116206971710418742261725)
              ·
                refine ⟨7543577614391407028348147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20116206971710418742261725 7543577614391407028348147)
                ·
                  refine ⟨11315366421587110542522221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543577614391407028348147 11315366421587110542522221)
                  ·
                    refine ⟨4243262408095166453445833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11315366421587110542522221 4243262408095166453445833)
                    ·
                      refine ⟨3182446806071374840084375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243262408095166453445833 3182446806071374840084375)
                      ·
                        rfl

theorem cell23_6197793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6197793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197793 prefixEnd_6197793 := by exact prefixLift 6197793
  have htrace : WordTrace (prefixWord ++ tailWord_6197793) baseStart_6197793 baseEnd_6197793 := by
    simpa [prefixWord, tailWord_6197793, baseEnd_6197793] using wordTrace_append hprefix tailTrace_6197793
  have hstable : (prefixWord ++ tailWord_6197793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197793).length < 2 ^ (prefixWord ++ tailWord_6197793).sum := by decide
  have hdescent : baseEnd_6197793 < baseStart_6197793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197800 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6197800 : Nat := 118140960795 + 6197800 * 2 ^ 59
def prefixEnd_6197800 : Nat := 4983230072969 + 3 ^ 40 * 6197800 * 2
def baseEnd_6197800 : Nat := 3182450400435956312696843

theorem tailTrace_6197800 : CollatzResearch.WordTrace tailWord_6197800 prefixEnd_6197800 3182450400435956312696843 := by
  unfold tailWord_6197800
  simp only [CollatzResearch.WordTrace]
  refine ⟨113026168473218287406811427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150701557964291049875748569 113026168473218287406811427)
  ·
    refine ⟨169539252709827431110217141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113026168473218287406811427 169539252709827431110217141)
    ·
      refine ⟨15894304941546321666582857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169539252709827431110217141 15894304941546321666582857)
      ·
        refine ⟨11920728706159741249937143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15894304941546321666582857 11920728706159741249937143)
        ·
          refine ⟨17881093059239611874905715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11920728706159741249937143 17881093059239611874905715)
          ·
            refine ⟨26821639588859417812358573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17881093059239611874905715 26821639588859417812358573)
            ·
              refine ⟨10058114845822281679634465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26821639588859417812358573 10058114845822281679634465)
              ·
                refine ⟨7543586134366711259725849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10058114845822281679634465 7543586134366711259725849)
                ·
                  refine ⟨5657689600775033444794387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543586134366711259725849 5657689600775033444794387)
                  ·
                    refine ⟨8486534401162550167191581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657689600775033444794387 8486534401162550167191581)
                    ·
                      refine ⟨3182450400435956312696843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486534401162550167191581 3182450400435956312696843)
                      ·
                        rfl

theorem cell23_6197800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6197800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197800 prefixEnd_6197800 := by exact prefixLift 6197800
  have htrace : WordTrace (prefixWord ++ tailWord_6197800) baseStart_6197800 baseEnd_6197800 := by
    simpa [prefixWord, tailWord_6197800, baseEnd_6197800] using wordTrace_append hprefix tailTrace_6197800
  have hstable : (prefixWord ++ tailWord_6197800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197800).length < 2 ^ (prefixWord ++ tailWord_6197800).sum := by decide
  have hdescent : baseEnd_6197800 < baseStart_6197800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197809 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_6197809 : Nat := 118140960795 + 6197809 * 2 ^ 59
def prefixEnd_6197809 : Nat := 4983230072969 + 3 ^ 40 * 6197809 * 2
def baseEnd_6197809 : Nat := 3182455021761846777484301

theorem tailTrace_6197809 : CollatzResearch.WordTrace tailWord_6197809 prefixEnd_6197809 3182455021761846777484301 := by
  unfold tailWord_6197809
  simp only [CollatzResearch.WordTrace]
  refine ⟨226052665203403969350700481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150701776802269312900466987 226052665203403969350700481)
  ·
    refine ⟨169539498902552977013025361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226052665203403969350700481 169539498902552977013025361)
    ·
      refine ⟨127154624176914732759769021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169539498902552977013025361 127154624176914732759769021)
      ·
        refine ⟨47682984066343024784913383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127154624176914732759769021 47682984066343024784913383)
        ·
          refine ⟨71524476099514537177370075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47682984066343024784913383 71524476099514537177370075)
          ·
            refine ⟨107286714149271805766055113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71524476099514537177370075 107286714149271805766055113)
            ·
              refine ⟨80465035611953854324541335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107286714149271805766055113 80465035611953854324541335)
              ·
                refine ⟨120697553417930781486812003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80465035611953854324541335 120697553417930781486812003)
                ·
                  refine ⟨181046330126896172230218005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120697553417930781486812003 181046330126896172230218005)
                  ·
                    refine ⟨8486546724698258073291469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181046330126896172230218005 8486546724698258073291469)
                    ·
                      refine ⟨3182455021761846777484301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486546724698258073291469 3182455021761846777484301)
                      ·
                        rfl

theorem cell23_6197809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_6197809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197809 prefixEnd_6197809 := by exact prefixLift 6197809
  have htrace : WordTrace (prefixWord ++ tailWord_6197809) baseStart_6197809 baseEnd_6197809 := by
    simpa [prefixWord, tailWord_6197809, baseEnd_6197809] using wordTrace_append hprefix tailTrace_6197809
  have hstable : (prefixWord ++ tailWord_6197809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197809).length < 2 ^ (prefixWord ++ tailWord_6197809).sum := by decide
  have hdescent : baseEnd_6197809 < baseStart_6197809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197829 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 7]
def baseStart_6197829 : Nat := 118140960795 + 6197829 * 2 ^ 59
def prefixEnd_6197829 : Nat := 4983230072969 + 3 ^ 40 * 6197829 * 2
def baseEnd_6197829 : Nat := 353607254597215188803801

theorem tailTrace_6197829 : CollatzResearch.WordTrace tailWord_6197829 prefixEnd_6197829 353607254597215188803801 := by
  unfold tailWord_6197829
  simp only [CollatzResearch.WordTrace]
  refine ⟨226053394663331512766428541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150702263108887675177619027 226053394663331512766428541)
  ·
    refine ⟨84770022998749317287410703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226053394663331512766428541 84770022998749317287410703)
    ·
      refine ⟨127155034498123975931116055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84770022998749317287410703 127155034498123975931116055)
      ·
        refine ⟨190732551747185963896674083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127155034498123975931116055 190732551747185963896674083)
        ·
          refine ⟨286098827620778945845011125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190732551747185963896674083 286098827620778945845011125)
          ·
            refine ⟨26821765089448026172969793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286098827620778945845011125 26821765089448026172969793)
            ·
              refine ⟨20116323817086019629727345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26821765089448026172969793 20116323817086019629727345)
              ·
                refine ⟨15087242862814514722295509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20116323817086019629727345 15087242862814514722295509)
                ·
                  refine ⟨353607254597215188803801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15087242862814514722295509 353607254597215188803801)
                  ·
                    rfl

theorem cell23_6197829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_6197829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197829 prefixEnd_6197829 := by exact prefixLift 6197829
  have htrace : WordTrace (prefixWord ++ tailWord_6197829) baseStart_6197829 baseEnd_6197829 := by
    simpa [prefixWord, tailWord_6197829, baseEnd_6197829] using wordTrace_append hprefix tailTrace_6197829
  have hstable : (prefixWord ++ tailWord_6197829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197829).length < 2 ^ (prefixWord ++ tailWord_6197829).sum := by decide
  have hdescent : baseEnd_6197829 < baseStart_6197829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197839 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_6197839 : Nat := 118140960795 + 6197839 * 2 ^ 59
def prefixEnd_6197839 : Nat := 4983230072969 + 3 ^ 40 * 6197839 * 2
def baseEnd_6197839 : Nat := 3182470426181481660109163

theorem tailTrace_6197839 : CollatzResearch.WordTrace tailWord_6197839 prefixEnd_6197839 3182470426181481660109163 := by
  unfold tailWord_6197839
  simp only [CollatzResearch.WordTrace]
  refine ⟨226053759393295284474292571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150702506262196856316195047 226053759393295284474292571)
  ·
    refine ⟨339080639089942926711438857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226053759393295284474292571 339080639089942926711438857)
    ·
      refine ⟨254310479317457195033579143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339080639089942926711438857 254310479317457195033579143)
      ·
        refine ⟨381465718976185792550368715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254310479317457195033579143 381465718976185792550368715)
        ·
          refine ⟨572198578464278688825553073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381465718976185792550368715 572198578464278688825553073)
          ·
            refine ⟨429148933848209016619164805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572198578464278688825553073 429148933848209016619164805)
            ·
              refine ⟨80465425096539190616093401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 429148933848209016619164805 80465425096539190616093401)
              ·
                refine ⟨60349068822404392962070051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80465425096539190616093401 60349068822404392962070051)
                ·
                  refine ⟨90523603233606589443105077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60349068822404392962070051 90523603233606589443105077)
                  ·
                    refine ⟨8486587803150617760291101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90523603233606589443105077 8486587803150617760291101)
                    ·
                      refine ⟨3182470426181481660109163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486587803150617760291101 3182470426181481660109163)
                      ·
                        rfl

theorem cell23_6197839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_6197839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197839 prefixEnd_6197839 := by exact prefixLift 6197839
  have htrace : WordTrace (prefixWord ++ tailWord_6197839) baseStart_6197839 baseEnd_6197839 := by
    simpa [prefixWord, tailWord_6197839, baseEnd_6197839] using wordTrace_append hprefix tailTrace_6197839
  have hstable : (prefixWord ++ tailWord_6197839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197839).length < 2 ^ (prefixWord ++ tailWord_6197839).sum := by decide
  have hdescent : baseEnd_6197839 < baseStart_6197839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197874 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6197874 : Nat := 118140960795 + 6197874 * 2 ^ 59
def prefixEnd_6197874 : Nat := 4983230072969 + 3 ^ 40 * 6197874 * 2
def baseEnd_6197874 : Nat := 3182488398004389023171503

theorem tailTrace_6197874 : CollatzResearch.WordTrace tailWord_6197874 prefixEnd_6197874 3182488398004389023171503 := by
  unfold tailWord_6197874
  simp only [CollatzResearch.WordTrace]
  refine ⟨56513758987042121362954169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150703357298778990301211117 56513758987042121362954169)
  ·
    refine ⟨42385319240281591022215627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56513758987042121362954169 42385319240281591022215627)
    ·
      refine ⟨63577978860422386533323441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42385319240281591022215627 63577978860422386533323441)
      ·
        refine ⟨47683484145316789899992581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63577978860422386533323441 47683484145316789899992581)
        ·
          refine ⟨8940653277246898106248609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47683484145316789899992581 8940653277246898106248609)
          ·
            refine ⟨6705489957935173579686457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8940653277246898106248609 6705489957935173579686457)
            ·
              refine ⟨5029117468451380184764843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705489957935173579686457 5029117468451380184764843)
              ·
                refine ⟨7543676202677070277147265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029117468451380184764843 7543676202677070277147265)
                ·
                  refine ⟨5657757152007802707860449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543676202677070277147265 5657757152007802707860449)
                  ·
                    refine ⟨4243317864005852030895337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5657757152007802707860449 4243317864005852030895337)
                    ·
                      refine ⟨3182488398004389023171503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243317864005852030895337 3182488398004389023171503)
                      ·
                        rfl

theorem cell23_6197874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6197874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197874 prefixEnd_6197874 := by exact prefixLift 6197874
  have htrace : WordTrace (prefixWord ++ tailWord_6197874) baseStart_6197874 baseEnd_6197874 := by
    simpa [prefixWord, tailWord_6197874, baseEnd_6197874] using wordTrace_append hprefix tailTrace_6197874
  have hstable : (prefixWord ++ tailWord_6197874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197874).length < 2 ^ (prefixWord ++ tailWord_6197874).sum := by decide
  have hdescent : baseEnd_6197874 < baseStart_6197874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197879 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_6197879 : Nat := 118140960795 + 6197879 * 2 ^ 59
def prefixEnd_6197879 : Nat := 4983230072969 + 3 ^ 40 * 6197879 * 2
def baseEnd_6197879 : Nat := 3182490965407661503608979

theorem tailTrace_6197879 : CollatzResearch.WordTrace tailWord_6197879 prefixEnd_6197879 3182490965407661503608979 := by
  unfold tailWord_6197879
  simp only [CollatzResearch.WordTrace]
  refine ⟨226055218313150371305748691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150703478875433580870499127 226055218313150371305748691)
  ·
    refine ⟨339082827469725556958623037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226055218313150371305748691 339082827469725556958623037)
    ·
      refine ⟨127156060301147083859483639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339082827469725556958623037 127156060301147083859483639)
      ·
        refine ⟨190734090451720625789225459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127156060301147083859483639 190734090451720625789225459)
        ·
          refine ⟨286101135677580938683838189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190734090451720625789225459 286101135677580938683838189)
          ·
            refine ⟨107287925879092852006439321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286101135677580938683838189 107287925879092852006439321)
            ·
              refine ⟨80465944409319639004829491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107287925879092852006439321 80465944409319639004829491)
              ·
                refine ⟨120698916613979458507244237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80465944409319639004829491 120698916613979458507244237)
                ·
                  refine ⟨45262093730242296940216589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120698916613979458507244237 45262093730242296940216589)
                  ·
                    refine ⟨16973285148840861352581221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45262093730242296940216589 16973285148840861352581221)
                    ·
                      refine ⟨3182490965407661503608979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16973285148840861352581221 3182490965407661503608979)
                      ·
                        rfl

theorem cell23_6197879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_6197879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197879 prefixEnd_6197879 := by exact prefixLift 6197879
  have htrace : WordTrace (prefixWord ++ tailWord_6197879) baseStart_6197879 baseEnd_6197879 := by
    simpa [prefixWord, tailWord_6197879, baseEnd_6197879] using wordTrace_append hprefix tailTrace_6197879
  have hstable : (prefixWord ++ tailWord_6197879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197879).length < 2 ^ (prefixWord ++ tailWord_6197879).sum := by decide
  have hdescent : baseEnd_6197879 < baseStart_6197879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197914 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_6197914 : Nat := 118140960795 + 6197914 * 2 ^ 59
def prefixEnd_6197914 : Nat := 4983230072969 + 3 ^ 40 * 6197914 * 2
def baseEnd_6197914 : Nat := 353612104136729874074591

theorem tailTrace_6197914 : CollatzResearch.WordTrace tailWord_6197914 prefixEnd_6197914 353612104136729874074591 := by
  unfold tailWord_6197914
  simp only [CollatzResearch.WordTrace]
  refine ⟨56514123717005893070818199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150704329912015714855515197 56514123717005893070818199)
  ·
    refine ⟨84771185575508839606227299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56514123717005893070818199 84771185575508839606227299)
    ·
      refine ⟨127156778363263259409340949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84771185575508839606227299 127156778363263259409340949)
      ·
        refine ⟨5960473985777965284812857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127156778363263259409340949 5960473985777965284812857)
        ·
          refine ⟨4470355489333473963609643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960473985777965284812857 4470355489333473963609643)
          ·
            refine ⟨6705533234000210945414465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470355489333473963609643 6705533234000210945414465)
            ·
              refine ⟨5029149925500158209060849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705533234000210945414465 5029149925500158209060849)
              ·
                refine ⟨3771862444125118656795637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029149925500158209060849 3771862444125118656795637)
                ·
                  refine ⟨353612104136729874074591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3771862444125118656795637 353612104136729874074591)
                  ·
                    rfl

theorem cell23_6197914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_6197914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197914 prefixEnd_6197914 := by exact prefixLift 6197914
  have htrace : WordTrace (prefixWord ++ tailWord_6197914) baseStart_6197914 baseEnd_6197914 := by
    simpa [prefixWord, tailWord_6197914, baseEnd_6197914] using wordTrace_append hprefix tailTrace_6197914
  have hstable : (prefixWord ++ tailWord_6197914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197914).length < 2 ^ (prefixWord ++ tailWord_6197914).sum := by decide
  have hdescent : baseEnd_6197914 < baseStart_6197914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6197970 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_6197970 : Nat := 118140960795 + 6197970 * 2 ^ 59
def prefixEnd_6197970 : Nat := 4983230072969 + 3 ^ 40 * 6197970 * 2
def baseEnd_6197970 : Nat := 353615299127468960841229

theorem tailTrace_6197970 : CollatzResearch.WordTrace tailWord_6197970 prefixEnd_6197970 353615299127468960841229 := by
  unfold tailWord_6197970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56514634338955173461827841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150705691570547129231540909 56514634338955173461827841)
  ·
    refine ⟨42385975754216380096370881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56514634338955173461827841 42385975754216380096370881)
    ·
      refine ⟨31789481815662285072278161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42385975754216380096370881 31789481815662285072278161)
      ·
        refine ⟨23842111361746713804208621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31789481815662285072278161 23842111361746713804208621)
        ·
          refine ⟨8940791760655017676578233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23842111361746713804208621 8940791760655017676578233)
          ·
            refine ⟨6705593820491263257433675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8940791760655017676578233 6705593820491263257433675)
            ·
              refine ⟨10058390730736894886150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705593820491263257433675 10058390730736894886150513)
              ·
                refine ⟨7543793048052671164612885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10058390730736894886150513 7543793048052671164612885)
                ·
                  refine ⟨353615299127468960841229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7543793048052671164612885 353615299127468960841229)
                  ·
                    rfl

theorem cell23_6197970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_6197970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6197970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6197970 prefixEnd_6197970 := by exact prefixLift 6197970
  have htrace : WordTrace (prefixWord ++ tailWord_6197970) baseStart_6197970 baseEnd_6197970 := by
    simpa [prefixWord, tailWord_6197970, baseEnd_6197970] using wordTrace_append hprefix tailTrace_6197970
  have hstable : (prefixWord ++ tailWord_6197970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6197970).length < 2 ^ (prefixWord ++ tailWord_6197970).sum := by decide
  have hdescent : baseEnd_6197970 < baseStart_6197970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6197970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198014 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_6198014 : Nat := 118140960795 + 6198014 * 2 ^ 59
def prefixEnd_6198014 : Nat := 4983230072969 + 3 ^ 40 * 6198014 * 2
def baseEnd_6198014 : Nat := 3182560285296018475420859

theorem tailTrace_6198014 : CollatzResearch.WordTrace tailWord_6198014 prefixEnd_6198014 3182560285296018475420859 := by
  unfold tailWord_6198014
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257517770957661170239137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150706761445107526241275397 28257517770957661170239137)
  ·
    refine ⟨21193138328218245877679353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28257517770957661170239137 21193138328218245877679353)
    ·
      refine ⟨15894853746163684408259515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21193138328218245877679353 15894853746163684408259515)
      ·
        refine ⟨23842280619245526612389273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894853746163684408259515 23842280619245526612389273)
        ·
          refine ⟨17881710464434144959291955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23842280619245526612389273 17881710464434144959291955)
          ·
            refine ⟨26822565696651217438937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17881710464434144959291955 26822565696651217438937933)
            ·
              refine ⟨10058462136244206539601725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26822565696651217438937933 10058462136244206539601725)
              ·
                refine ⟨3771923301091577452350647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10058462136244206539601725 3771923301091577452350647)
                ·
                  refine ⟨5657884951637366178525971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771923301091577452350647 5657884951637366178525971)
                  ·
                    refine ⟨8486827427456049267788957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5657884951637366178525971 8486827427456049267788957)
                    ·
                      refine ⟨3182560285296018475420859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486827427456049267788957 3182560285296018475420859)
                      ·
                        rfl

theorem cell23_6198014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_6198014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198014 prefixEnd_6198014 := by exact prefixLift 6198014
  have htrace : WordTrace (prefixWord ++ tailWord_6198014) baseStart_6198014 baseEnd_6198014 := by
    simpa [prefixWord, tailWord_6198014, baseEnd_6198014] using wordTrace_append hprefix tailTrace_6198014
  have hstable : (prefixWord ++ tailWord_6198014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198014).length < 2 ^ (prefixWord ++ tailWord_6198014).sum := by decide
  have hdescent : baseEnd_6198014 < baseStart_6198014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198023 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6198023 : Nat := 118140960795 + 6198023 * 2 ^ 59
def prefixEnd_6198023 : Nat := 4983230072969 + 3 ^ 40 * 6198023 * 2
def baseEnd_6198023 : Nat := 3182564906621908940208317

theorem tailTrace_6198023 : CollatzResearch.WordTrace tailWord_6198023 prefixEnd_6198023 3182564906621908940208317 := by
  unfold tailWord_6198023
  simp only [CollatzResearch.WordTrace]
  refine ⟨226060470424628683898990723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150706980283085789265993815 226060470424628683898990723)
  ·
    refine ⟨339090705636943025848486085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226060470424628683898990723 339090705636943025848486085)
    ·
      refine ⟨63579507306926817346591141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339090705636943025848486085 63579507306926817346591141)
      ·
        refine ⟨11921157620048778252485839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63579507306926817346591141 11921157620048778252485839)
        ·
          refine ⟨17881736430073167378728759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921157620048778252485839 17881736430073167378728759)
          ·
            refine ⟨26822604645109751068093139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17881736430073167378728759 26822604645109751068093139)
            ·
              refine ⟨40233906967664626602139709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26822604645109751068093139 40233906967664626602139709)
              ·
                refine ⟨15087715112874234975802391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40233906967664626602139709 15087715112874234975802391)
                ·
                  refine ⟨22631572669311352463703587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15087715112874234975802391 22631572669311352463703587)
                  ·
                    refine ⟨33947359003967028695555381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22631572669311352463703587 33947359003967028695555381)
                    ·
                      refine ⟨3182564906621908940208317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33947359003967028695555381 3182564906621908940208317)
                      ·
                        rfl

theorem cell23_6198023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6198023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198023 prefixEnd_6198023 := by exact prefixLift 6198023
  have htrace : WordTrace (prefixWord ++ tailWord_6198023) baseStart_6198023 baseEnd_6198023 := by
    simpa [prefixWord, tailWord_6198023, baseEnd_6198023] using wordTrace_append hprefix tailTrace_6198023
  have hstable : (prefixWord ++ tailWord_6198023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198023).length < 2 ^ (prefixWord ++ tailWord_6198023).sum := by decide
  have hdescent : baseEnd_6198023 < baseStart_6198023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198047 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 2, 4]
def baseStart_6198047 : Nat := 118140960795 + 6198047 * 2 ^ 59
def prefixEnd_6198047 : Nat := 4983230072969 + 3 ^ 40 * 6198047 * 2
def baseEnd_6198047 : Nat := 1060859076719205615436069

theorem tailTrace_6198047 : CollatzResearch.WordTrace tailWord_6198047 prefixEnd_6198047 1060859076719205615436069 := by
  unfold tailWord_6198047
  simp only [CollatzResearch.WordTrace]
  refine ⟨226061345776541735997864395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150707563851027823998576263 226061345776541735997864395)
  ·
    refine ⟨339092018664812603996796593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226061345776541735997864395 339092018664812603996796593)
    ·
      refine ⟨254319013998609452997597445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339092018664812603996796593 254319013998609452997597445)
      ·
        refine ⟨47684815124739272437049521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254319013998609452997597445 47684815124739272437049521)
        ·
          refine ⟨35763611343554454327787141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47684815124739272437049521 35763611343554454327787141)
          ·
            refine ⟨6705677126916460186460089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35763611343554454327787141 6705677126916460186460089)
            ·
              refine ⟨5029257845187345139845067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705677126916460186460089 5029257845187345139845067)
              ·
                refine ⟨7543886767781017709767601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029257845187345139845067 7543886767781017709767601)
                ·
                  refine ⟨5657915075835763282325701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7543886767781017709767601 5657915075835763282325701)
                  ·
                    refine ⟨1060859076719205615436069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5657915075835763282325701 1060859076719205615436069)
                    ·
                      rfl

theorem cell23_6198047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_6198047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198047 prefixEnd_6198047 := by exact prefixLift 6198047
  have htrace : WordTrace (prefixWord ++ tailWord_6198047) baseStart_6198047 baseEnd_6198047 := by
    simpa [prefixWord, tailWord_6198047, baseEnd_6198047] using wordTrace_append hprefix tailTrace_6198047
  have hstable : (prefixWord ++ tailWord_6198047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198047).length < 2 ^ (prefixWord ++ tailWord_6198047).sum := by decide
  have hdescent : baseEnd_6198047 < baseStart_6198047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198053 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_6198053 : Nat := 118140960795 + 6198053 * 2 ^ 59
def prefixEnd_6198053 : Nat := 4983230072969 + 3 ^ 40 * 6198053 * 2
def baseEnd_6198053 : Nat := 3182580311041543822833179

theorem tailTrace_6198053 : CollatzResearch.WordTrace tailWord_6198053 prefixEnd_6198053 3182580311041543822833179 := by
  unfold tailWord_6198053
  simp only [CollatzResearch.WordTrace]
  refine ⟨226061564614519999022582813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150707709743013332681721875 226061564614519999022582813)
  ·
    refine ⟨84773086730444999633468555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226061564614519999022582813 84773086730444999633468555)
    ·
      refine ⟨127159630095667499450202833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84773086730444999633468555 127159630095667499450202833)
      ·
        refine ⟨95369722571750624587652125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127159630095667499450202833 95369722571750624587652125)
        ·
          refine ⟨35763645964406484220369547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95369722571750624587652125 35763645964406484220369547)
          ·
            refine ⟨53645468946609726330554321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35763645964406484220369547 53645468946609726330554321)
            ·
              refine ⟨40234101709957294747915741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53645468946609726330554321 40234101709957294747915741)
              ·
                refine ⟨15087788141233985530468403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40234101709957294747915741 15087788141233985530468403)
                ·
                  refine ⟨22631682211850978295702605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15087788141233985530468403 22631682211850978295702605)
                  ·
                    refine ⟨8486880829444116860888477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22631682211850978295702605 8486880829444116860888477)
                    ·
                      refine ⟨3182580311041543822833179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8486880829444116860888477 3182580311041543822833179)
                      ·
                        rfl

theorem cell23_6198053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_6198053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198053 prefixEnd_6198053 := by exact prefixLift 6198053
  have htrace : WordTrace (prefixWord ++ tailWord_6198053) baseStart_6198053 baseEnd_6198053 := by
    simpa [prefixWord, tailWord_6198053, baseEnd_6198053] using wordTrace_append hprefix tailTrace_6198053
  have hstable : (prefixWord ++ tailWord_6198053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198053).length < 2 ^ (prefixWord ++ tailWord_6198053).sum := by decide
  have hdescent : baseEnd_6198053 < baseStart_6198053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198080 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2]
def baseStart_6198080 : Nat := 118140960795 + 6198080 * 2 ^ 59
def prefixEnd_6198080 : Nat := 4983230072969 + 3 ^ 40 * 6198080 * 2
def baseEnd_6198080 : Nat := 3182594175019215217195555

theorem tailTrace_6198080 : CollatzResearch.WordTrace tailWord_6198080 prefixEnd_6198080 3182594175019215217195555 := by
  unfold tailWord_6198080
  simp only [CollatzResearch.WordTrace]
  refine ⟨113031274692711091316907847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150708366256948121755877129 113031274692711091316907847)
  ·
    refine ⟨169546912039066636975361771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113031274692711091316907847 169546912039066636975361771)
    ·
      refine ⟨254320368058599955463042657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169546912039066636975361771 254320368058599955463042657)
      ·
        refine ⟨190740276043949966597281993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254320368058599955463042657 190740276043949966597281993)
        ·
          refine ⟨143055207032962474947961495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190740276043949966597281993 143055207032962474947961495)
          ·
            refine ⟨214582810549443712421942243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143055207032962474947961495 214582810549443712421942243)
            ·
              refine ⟨321874215824165568632913365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214582810549443712421942243 321874215824165568632913365)
              ·
                refine ⟨7543926933378880514833907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 321874215824165568632913365 7543926933378880514833907)
                ·
                  refine ⟨11315890400068320772250861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543926933378880514833907 11315890400068320772250861)
                  ·
                    refine ⟨4243458900025620289594073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11315890400068320772250861 4243458900025620289594073)
                    ·
                      refine ⟨3182594175019215217195555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243458900025620289594073 3182594175019215217195555)
                      ·
                        rfl

theorem cell23_6198080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_6198080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198080 prefixEnd_6198080 := by exact prefixLift 6198080
  have htrace : WordTrace (prefixWord ++ tailWord_6198080) baseStart_6198080 baseEnd_6198080 := by
    simpa [prefixWord, tailWord_6198080, baseEnd_6198080] using wordTrace_append hprefix tailTrace_6198080
  have hstable : (prefixWord ++ tailWord_6198080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198080).length < 2 ^ (prefixWord ++ tailWord_6198080).sum := by decide
  have hdescent : baseEnd_6198080 < baseStart_6198080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198096 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_6198096 : Nat := 118140960795 + 6198096 * 2 ^ 59
def prefixEnd_6198096 : Nat := 4983230072969 + 3 ^ 40 * 6198096 * 2
def baseEnd_6198096 : Nat := 3182602390709687154595481

theorem tailTrace_6198096 : CollatzResearch.WordTrace tailWord_6198096 prefixEnd_6198096 3182602390709687154595481 := by
  unfold tailWord_6198096
  simp only [CollatzResearch.WordTrace]
  refine ⟨113031566476682108683199071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150708755302242811577598761 113031566476682108683199071)
  ·
    refine ⟨169547349715023163024798607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113031566476682108683199071 169547349715023163024798607)
    ·
      refine ⟨254321024572534744537197911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169547349715023163024798607 254321024572534744537197911)
      ·
        refine ⟨381481536858802116805796867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254321024572534744537197911 381481536858802116805796867)
        ·
          refine ⟨572222305288203175208695301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381481536858802116805796867 572222305288203175208695301)
          ·
            refine ⟨107291682241538095351630369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572222305288203175208695301 107291682241538095351630369)
            ·
              refine ⟨80468761681153571513722777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107291682241538095351630369 80468761681153571513722777)
              ·
                refine ⟨60351571260865178635292083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80468761681153571513722777 60351571260865178635292083)
                ·
                  refine ⟨90527356891297767952938125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60351571260865178635292083 90527356891297767952938125)
                  ·
                    refine ⟨33947758834236662982351797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90527356891297767952938125 33947758834236662982351797)
                    ·
                      refine ⟨3182602390709687154595481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33947758834236662982351797 3182602390709687154595481)
                      ·
                        rfl

theorem cell23_6198096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_6198096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198096 prefixEnd_6198096 := by exact prefixLift 6198096
  have htrace : WordTrace (prefixWord ++ tailWord_6198096) baseStart_6198096 baseEnd_6198096 := by
    simpa [prefixWord, tailWord_6198096, baseEnd_6198096] using wordTrace_append hprefix tailTrace_6198096
  have hstable : (prefixWord ++ tailWord_6198096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198096).length < 2 ^ (prefixWord ++ tailWord_6198096).sum := by decide
  have hdescent : baseEnd_6198096 < baseStart_6198096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198103 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 6]
def baseStart_6198103 : Nat := 118140960795 + 6198103 * 2 ^ 59
def prefixEnd_6198103 : Nat := 4983230072969 + 3 ^ 40 * 6198103 * 2
def baseEnd_6198103 : Nat := 1060868661691422875735983

theorem tailTrace_6198103 : CollatzResearch.WordTrace tailWord_6198103 prefixEnd_6198103 1060868661691422875735983 := by
  unfold tailWord_6198103
  simp only [CollatzResearch.WordTrace]
  refine ⟨226063388264338857561902963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150708925509559238374601975 226063388264338857561902963)
  ·
    refine ⟨339095082396508286342854445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226063388264338857561902963 339095082396508286342854445)
    ·
      refine ⟨127160655898690607378570417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339095082396508286342854445 127160655898690607378570417)
      ·
        refine ⟨95370491924017955533927813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127160655898690607378570417 95370491924017955533927813)
        ·
          refine ⟨17881967235753366662611465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95370491924017955533927813 17881967235753366662611465)
          ·
            refine ⟨13411475426815024996958599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17881967235753366662611465 13411475426815024996958599)
            ·
              refine ⟨20117213140222537495437899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411475426815024996958599 20117213140222537495437899)
              ·
                refine ⟨30175819710333806243156849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20117213140222537495437899 30175819710333806243156849)
                ·
                  refine ⟨22631864782750354682367637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30175819710333806243156849 22631864782750354682367637)
                  ·
                    refine ⟨1060868661691422875735983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22631864782750354682367637 1060868661691422875735983)
                    ·
                      rfl

theorem cell23_6198103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_6198103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198103 prefixEnd_6198103 := by exact prefixLift 6198103
  have htrace : WordTrace (prefixWord ++ tailWord_6198103) baseStart_6198103 baseEnd_6198103 := by
    simpa [prefixWord, tailWord_6198103, baseEnd_6198103] using wordTrace_append hprefix tailTrace_6198103
  have hstable : (prefixWord ++ tailWord_6198103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198103).length < 2 ^ (prefixWord ++ tailWord_6198103).sum := by decide
  have hdescent : baseEnd_6198103 < baseStart_6198103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198143 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_6198143 : Nat := 118140960795 + 6198143 * 2 ^ 59
def prefixEnd_6198143 : Nat := 4983230072969 + 3 ^ 40 * 6198143 * 2
def baseEnd_6198143 : Nat := 3182626524300448470707765

theorem tailTrace_6198143 : CollatzResearch.WordTrace tailWord_6198143 prefixEnd_6198143 3182626524300448470707765 := by
  unfold tailWord_6198143
  simp only [CollatzResearch.WordTrace]
  refine ⟨226064847184193944393359083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150709898122795962928906055 226064847184193944393359083)
  ·
    refine ⟨339097270776290916590038625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226064847184193944393359083 339097270776290916590038625)
    ·
      refine ⟨254322953082218187442528969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339097270776290916590038625 254322953082218187442528969)
      ·
        refine ⟨190742214811663640581896727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254322953082218187442528969 190742214811663640581896727)
        ·
          refine ⟨286113322217495460872845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190742214811663640581896727 286113322217495460872845091)
          ·
            refine ⟨429169983326243191309267637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286113322217495460872845091 429169983326243191309267637)
            ·
              refine ⟨40234685936835299185243841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 429169983326243191309267637 40234685936835299185243841)
              ·
                refine ⟨30176014452626474388932881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40234685936835299185243841 30176014452626474388932881)
                ·
                  refine ⟨22632010839469855791699661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30176014452626474388932881 22632010839469855791699661)
                  ·
                    refine ⟨8487004064801195921887373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22632010839469855791699661 8487004064801195921887373)
                    ·
                      refine ⟨3182626524300448470707765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487004064801195921887373 3182626524300448470707765)
                      ·
                        rfl

theorem cell23_6198143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_6198143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198143 prefixEnd_6198143 := by exact prefixLift 6198143
  have htrace : WordTrace (prefixWord ++ tailWord_6198143) baseStart_6198143 baseEnd_6198143 := by
    simpa [prefixWord, tailWord_6198143, baseEnd_6198143] using wordTrace_append hprefix tailTrace_6198143
  have hstable : (prefixWord ++ tailWord_6198143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198143).length < 2 ^ (prefixWord ++ tailWord_6198143).sum := by decide
  have hdescent : baseEnd_6198143 < baseStart_6198143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198200 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_6198200 : Nat := 118140960795 + 6198200 * 2 ^ 59
def prefixEnd_6198200 : Nat := 4983230072969 + 3 ^ 40 * 6198200 * 2
def baseEnd_6198200 : Nat := 3182655792697754747695003

theorem tailTrace_6198200 : CollatzResearch.WordTrace tailWord_6198200 prefixEnd_6198200 3182655792697754747695003 := by
  unfold tailWord_6198200
  simp only [CollatzResearch.WordTrace]
  refine ⟨113033463072493721564092027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150711284096658295418789369 113033463072493721564092027)
  ·
    refine ⟨169550194608740582346138041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113033463072493721564092027 169550194608740582346138041)
    ·
      refine ⟨127162645956555436759603531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169550194608740582346138041 127162645956555436759603531)
      ·
        refine ⟨190743968934833155139405297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127162645956555436759603531 190743968934833155139405297)
        ·
          refine ⟨143057976701124866354553973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190743968934833155139405297 143057976701124866354553973)
          ·
            refine ⟨13411685315730456220739435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143057976701124866354553973 13411685315730456220739435)
            ·
              refine ⟨20117527973595684331109153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411685315730456220739435 20117527973595684331109153)
              ·
                refine ⟨15088145980196763248331865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20117527973595684331109153 15088145980196763248331865)
                ·
                  refine ⟨11316109485147572436248899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15088145980196763248331865 11316109485147572436248899)
                  ·
                    refine ⟨16974164227721358654373349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11316109485147572436248899 16974164227721358654373349)
                    ·
                      refine ⟨3182655792697754747695003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16974164227721358654373349 3182655792697754747695003)
                      ·
                        rfl

theorem cell23_6198200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_6198200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198200 prefixEnd_6198200 := by exact prefixLift 6198200
  have htrace : WordTrace (prefixWord ++ tailWord_6198200) baseStart_6198200 baseEnd_6198200 := by
    simpa [prefixWord, tailWord_6198200, baseEnd_6198200] using wordTrace_append hprefix tailTrace_6198200
  have hstable : (prefixWord ++ tailWord_6198200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198200).length < 2 ^ (prefixWord ++ tailWord_6198200).sum := by decide
  have hdescent : baseEnd_6198200 < baseStart_6198200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198220 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6198220 : Nat := 118140960795 + 6198220 * 2 ^ 59
def prefixEnd_6198220 : Nat := 4983230072969 + 3 ^ 40 * 6198220 * 2
def baseEnd_6198220 : Nat := 3182666062310844669444911

theorem tailTrace_6198220 : CollatzResearch.WordTrace tailWord_6198220 prefixEnd_6198220 3182666062310844669444911 := by
  unfold tailWord_6198220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113033827802457493271956057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150711770403276657695941409 113033827802457493271956057)
  ·
    refine ⟨84775370851843119953967043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113033827802457493271956057 84775370851843119953967043)
    ·
      refine ⟨127163056277764679930950565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84775370851843119953967043 127163056277764679930950565)
      ·
        refine ⟨23843073052080877487053231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127163056277764679930950565 23843073052080877487053231)
        ·
          refine ⟨35764609578121316230579847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23843073052080877487053231 35764609578121316230579847)
          ·
            refine ⟨53646914367181974345869771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35764609578121316230579847 53646914367181974345869771)
            ·
              refine ⟨80470371550772961518804657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53646914367181974345869771 80470371550772961518804657)
              ·
                refine ⟨60352778663079721139103493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80470371550772961518804657 60352778663079721139103493)
                ·
                  refine ⟨11316145999327447713581905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60352778663079721139103493 11316145999327447713581905)
                  ·
                    refine ⟨8487109499495585785186429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11316145999327447713581905 8487109499495585785186429)
                    ·
                      refine ⟨3182666062310844669444911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487109499495585785186429 3182666062310844669444911)
                      ·
                        rfl

theorem cell23_6198220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6198220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198220 prefixEnd_6198220 := by exact prefixLift 6198220
  have htrace : WordTrace (prefixWord ++ tailWord_6198220) baseStart_6198220 baseEnd_6198220 := by
    simpa [prefixWord, tailWord_6198220, baseEnd_6198220] using wordTrace_append hprefix tailTrace_6198220
  have hstable : (prefixWord ++ tailWord_6198220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198220).length < 2 ^ (prefixWord ++ tailWord_6198220).sum := by decide
  have hdescent : baseEnd_6198220 < baseStart_6198220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198237 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_6198237 : Nat := 118140960795 + 6198237 * 2 ^ 59
def prefixEnd_6198237 : Nat := 4983230072969 + 3 ^ 40 * 6198237 * 2
def baseEnd_6198237 : Nat := 3182674791481971102932333

theorem tailTrace_6198237 : CollatzResearch.WordTrace tailWord_6198237 prefixEnd_6198237 3182674791481971102932333 := by
  unfold tailWord_6198237
  simp only [CollatzResearch.WordTrace]
  refine ⟨226068275645853398447280965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150712183763902265631520643 226068275645853398447280965)
  ·
    refine ⟨42387801683597512208865181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226068275645853398447280965 42387801683597512208865181)
    ·
      refine ⟨15895425631349067078324443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42387801683597512208865181 15895425631349067078324443)
      ·
        refine ⟨23843138447023600617486665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15895425631349067078324443 23843138447023600617486665)
        ·
          refine ⟨17882353835267700463114999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23843138447023600617486665 17882353835267700463114999)
          ·
            refine ⟨26823530752901550694672499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882353835267700463114999 26823530752901550694672499)
            ·
              refine ⟨40235296129352326042008749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26823530752901550694672499 40235296129352326042008749)
              ·
                refine ⟨15088236048507122265753281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40235296129352326042008749 15088236048507122265753281)
                ·
                  refine ⟨11316177036380341699314961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15088236048507122265753281 11316177036380341699314961)
                  ·
                    refine ⟨8487132777285256274486221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11316177036380341699314961 8487132777285256274486221)
                    ·
                      refine ⟨3182674791481971102932333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487132777285256274486221 3182674791481971102932333)
                      ·
                        rfl

theorem cell23_6198237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_6198237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198237 prefixEnd_6198237 := by exact prefixLift 6198237
  have htrace : WordTrace (prefixWord ++ tailWord_6198237) baseStart_6198237 baseEnd_6198237 := by
    simpa [prefixWord, tailWord_6198237, baseEnd_6198237] using wordTrace_append hprefix tailTrace_6198237
  have hstable : (prefixWord ++ tailWord_6198237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198237).length < 2 ^ (prefixWord ++ tailWord_6198237).sum := by decide
  have hdescent : baseEnd_6198237 < baseStart_6198237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198304 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_6198304 : Nat := 118140960795 + 6198304 * 2 ^ 59
def prefixEnd_6198304 : Nat := 4983230072969 + 3 ^ 40 * 6198304 * 2
def baseEnd_6198304 : Nat := 1060903064895274113598175

theorem tailTrace_6198304 : CollatzResearch.WordTrace tailWord_6198304 prefixEnd_6198304 1060903064895274113598175 := by
  unfold tailWord_6198304
  simp only [CollatzResearch.WordTrace]
  refine ⟨113035359668305334444984983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150713812891073779259979977 113035359668305334444984983)
  ·
    refine ⟨169553039502458001667477475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113035359668305334444984983 169553039502458001667477475)
    ·
      refine ⟨254329559253687002501216213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169553039502458001667477475 254329559253687002501216213)
      ·
        refine ⟨5960849045008289121122255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254329559253687002501216213 5960849045008289121122255)
        ·
          refine ⟨8941273567512433681683383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960849045008289121122255 8941273567512433681683383)
          ·
            refine ⟨13411910351268650522525075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941273567512433681683383 13411910351268650522525075)
            ·
              refine ⟨20117865526902975783787613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411910351268650522525075 20117865526902975783787613)
              ·
                refine ⟨7544199572588615918920355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20117865526902975783787613 7544199572588615918920355)
                ·
                  refine ⟨11316299358882923878380533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544199572588615918920355 11316299358882923878380533)
                  ·
                    refine ⟨1060903064895274113598175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11316299358882923878380533 1060903064895274113598175)
                    ·
                      rfl

theorem cell23_6198304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_6198304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198304 prefixEnd_6198304 := by exact prefixLift 6198304
  have htrace : WordTrace (prefixWord ++ tailWord_6198304) baseStart_6198304 baseEnd_6198304 := by
    simpa [prefixWord, tailWord_6198304, baseEnd_6198304] using wordTrace_append hprefix tailTrace_6198304
  have hstable : (prefixWord ++ tailWord_6198304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198304).length < 2 ^ (prefixWord ++ tailWord_6198304).sum := by decide
  have hdescent : baseEnd_6198304 < baseStart_6198304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198307 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 4]
def baseStart_6198307 : Nat := 118140960795 + 6198307 * 2 ^ 59
def prefixEnd_6198307 : Nat := 4983230072969 + 3 ^ 40 * 6198307 * 2
def baseEnd_6198307 : Nat := 3182710735127785829057011

theorem tailTrace_6198307 : CollatzResearch.WordTrace tailWord_6198307 prefixEnd_6198307 3182710735127785829057011 := by
  unfold tailWord_6198307
  simp only [CollatzResearch.WordTrace]
  refine ⟨226070828755599800402329175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150713885837066533601552783 226070828755599800402329175)
  ·
    refine ⟨339106243133399700603493763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226070828755599800402329175 339106243133399700603493763)
    ·
      refine ⟨508659364700099550905240645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339106243133399700603493763 508659364700099550905240645)
      ·
        refine ⟨95373630881268665794732621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 508659364700099550905240645 95373630881268665794732621)
        ·
          refine ⟨35765111580475749673024733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95373630881268665794732621 35765111580475749673024733)
          ·
            refine ⟨13411916842678406127384275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35765111580475749673024733 13411916842678406127384275)
            ·
              refine ⟨20117875264017609191076413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411916842678406127384275 20117875264017609191076413)
              ·
                refine ⟨7544203224006603446653655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20117875264017609191076413 7544203224006603446653655)
                ·
                  refine ⟨11316304836009905169980483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544203224006603446653655 11316304836009905169980483)
                  ·
                    refine ⟨16974457254014857754970725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11316304836009905169980483 16974457254014857754970725)
                    ·
                      refine ⟨3182710735127785829057011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16974457254014857754970725 3182710735127785829057011)
                      ·
                        rfl

theorem cell23_6198307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_6198307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198307 prefixEnd_6198307 := by exact prefixLift 6198307
  have htrace : WordTrace (prefixWord ++ tailWord_6198307) baseStart_6198307 baseEnd_6198307 := by
    simpa [prefixWord, tailWord_6198307, baseEnd_6198307] using wordTrace_append hprefix tailTrace_6198307
  have hstable : (prefixWord ++ tailWord_6198307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198307).length < 2 ^ (prefixWord ++ tailWord_6198307).sum := by decide
  have hdescent : baseEnd_6198307 < baseStart_6198307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_6198323 : Nat := 118140960795 + 6198323 * 2 ^ 59
def prefixEnd_6198323 : Nat := 4983230072969 + 3 ^ 40 * 6198323 * 2
def baseEnd_6198323 : Nat := 3182718950818257766456937

theorem tailTrace_6198323 : CollatzResearch.WordTrace tailWord_6198323 prefixEnd_6198323 3182718950818257766456937 := by
  unfold tailWord_6198323
  simp only [CollatzResearch.WordTrace]
  refine ⟨226071412323541835134911623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150714274882361223423274415 226071412323541835134911623)
  ·
    refine ⟨339107118485312752702367435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226071412323541835134911623 339107118485312752702367435)
    ·
      refine ⟨508660677727969129053551153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339107118485312752702367435 508660677727969129053551153)
      ·
        refine ⟨381495508295976846790163365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508660677727969129053551153 381495508295976846790163365)
        ·
          refine ⟨71530407805495658773155631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381495508295976846790163365 71530407805495658773155631)
          ·
            refine ⟨107295611708243488159733447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71530407805495658773155631 107295611708243488159733447)
            ·
              refine ⟨160943417562365232239600171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107295611708243488159733447 160943417562365232239600171)
              ·
                refine ⟨241415126343547848359400257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160943417562365232239600171 241415126343547848359400257)
                ·
                  refine ⟨181061344757660886269550193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241415126343547848359400257 181061344757660886269550193)
                  ·
                    refine ⟨135796008568245664702162645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181061344757660886269550193 135796008568245664702162645)
                    ·
                      refine ⟨3182718950818257766456937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135796008568245664702162645 3182718950818257766456937)
                      ·
                        rfl

theorem cell23_6198323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_6198323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198323 prefixEnd_6198323 := by exact prefixLift 6198323
  have htrace : WordTrace (prefixWord ++ tailWord_6198323) baseStart_6198323 baseEnd_6198323 := by
    simpa [prefixWord, tailWord_6198323, baseEnd_6198323] using wordTrace_append hprefix tailTrace_6198323
  have hstable : (prefixWord ++ tailWord_6198323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198323).length < 2 ^ (prefixWord ++ tailWord_6198323).sum := by decide
  have hdescent : baseEnd_6198323 < baseStart_6198323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198334 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_6198334 : Nat := 118140960795 + 6198334 * 2 ^ 59
def prefixEnd_6198334 : Nat := 4983230072969 + 3 ^ 40 * 6198334 * 2
def baseEnd_6198334 : Nat := 1060908199701819074473129

theorem tailTrace_6198334 : CollatzResearch.WordTrace tailWord_6198334 prefixEnd_6198334 1060908199701819074473129 := by
  unfold tailWord_6198334
  simp only [CollatzResearch.WordTrace]
  refine ⟨28258976690812748001695257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150714542351001322675708037 28258976690812748001695257)
  ·
    refine ⟨21194232518109561001271443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28258976690812748001695257 21194232518109561001271443)
    ·
      refine ⟨31791348777164341501907165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21194232518109561001271443 31791348777164341501907165)
      ·
        refine ⟨11921755791436628063215187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31791348777164341501907165 11921755791436628063215187)
        ·
          refine ⟨17882633687154942094822781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921755791436628063215187 17882633687154942094822781)
          ·
            refine ⟨6705987632683103285558543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17882633687154942094822781 6705987632683103285558543)
            ·
              refine ⟨10058981449024654928337815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6705987632683103285558543 10058981449024654928337815)
              ·
                refine ⟨15088472173536982392506723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10058981449024654928337815 15088472173536982392506723)
                ·
                  refine ⟨22632708260305473588760085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15088472173536982392506723 22632708260305473588760085)
                  ·
                    refine ⟨1060908199701819074473129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22632708260305473588760085 1060908199701819074473129)
                    ·
                      rfl

theorem cell23_6198334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_6198334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198334 prefixEnd_6198334 := by exact prefixLift 6198334
  have htrace : WordTrace (prefixWord ++ tailWord_6198334) baseStart_6198334 baseEnd_6198334 := by
    simpa [prefixWord, tailWord_6198334, baseEnd_6198334] using wordTrace_append hprefix tailTrace_6198334
  have hstable : (prefixWord ++ tailWord_6198334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198334).length < 2 ^ (prefixWord ++ tailWord_6198334).sum := by decide
  have hdescent : baseEnd_6198334 < baseStart_6198334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198337 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6198337 : Nat := 118140960795 + 6198337 * 2 ^ 59
def prefixEnd_6198337 : Nat := 4983230072969 + 3 ^ 40 * 6198337 * 2
def baseEnd_6198337 : Nat := 3182726139547420711681873

theorem tailTrace_6198337 : CollatzResearch.WordTrace tailWord_6198337 prefixEnd_6198337 3182726139547420711681873 := by
  unfold tailWord_6198337
  simp only [CollatzResearch.WordTrace]
  refine ⟨226071922945491115525921265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150714615296994077017280843 226071922945491115525921265)
  ·
    refine ⟨169553942209118336644440949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226071922945491115525921265 169553942209118336644440949)
    ·
      refine ⟨15895682082104844060416339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169553942209118336644440949 15895682082104844060416339)
      ·
        refine ⟨23843523123157266090624509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15895682082104844060416339 23843523123157266090624509)
        ·
          refine ⟨8941321171183974783984191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23843523123157266090624509 8941321171183974783984191)
          ·
            refine ⟨13411981756775962175976287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941321171183974783984191 13411981756775962175976287)
            ·
              refine ⟨20117972635163943263964431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411981756775962175976287 20117972635163943263964431)
              ·
                refine ⟨30176958952745914895946647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20117972635163943263964431 30176958952745914895946647)
                ·
                  refine ⟨45265438429118872343919971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30176958952745914895946647 45265438429118872343919971)
                  ·
                    refine ⟨67898157643678308515879957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45265438429118872343919971 67898157643678308515879957)
                    ·
                      refine ⟨3182726139547420711681873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67898157643678308515879957 3182726139547420711681873)
                      ·
                        rfl

theorem cell23_6198337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6198337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198337 prefixEnd_6198337 := by exact prefixLift 6198337
  have htrace : WordTrace (prefixWord ++ tailWord_6198337) baseStart_6198337 baseEnd_6198337 := by
    simpa [prefixWord, tailWord_6198337, baseEnd_6198337] using wordTrace_append hprefix tailTrace_6198337
  have hstable : (prefixWord ++ tailWord_6198337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198337).length < 2 ^ (prefixWord ++ tailWord_6198337).sum := by decide
  have hdescent : baseEnd_6198337 < baseStart_6198337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198357 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6198357 : Nat := 118140960795 + 6198357 * 2 ^ 59
def prefixEnd_6198357 : Nat := 4983230072969 + 3 ^ 40 * 6198357 * 2
def baseEnd_6198357 : Nat := 3182736409160510633431781

theorem tailTrace_6198357 : CollatzResearch.WordTrace tailWord_6198357 prefixEnd_6198357 3182736409160510633431781 := by
  unfold tailWord_6198357
  simp only [CollatzResearch.WordTrace]
  refine ⟨226072652405418658941649325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150715101603612439294432883 226072652405418658941649325)
  ·
    refine ⟨84777244652031997103118497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226072652405418658941649325 84777244652031997103118497)
    ·
      refine ⟨63582933489023997827338873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84777244652031997103118497 63582933489023997827338873)
      ·
        refine ⟨47687200116767998370504155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63582933489023997827338873 47687200116767998370504155)
        ·
          refine ⟨71530800175151997555756233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47687200116767998370504155 71530800175151997555756233)
          ·
            refine ⟨53648100131363998166817175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71530800175151997555756233 53648100131363998166817175)
            ·
              refine ⟨80472150197045997250225763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53648100131363998166817175 80472150197045997250225763)
              ·
                refine ⟨120708225295568995875338645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80472150197045997250225763 120708225295568995875338645)
                ·
                  refine ⟨5658198060729796681656499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120708225295568995875338645 5658198060729796681656499)
                  ·
                    refine ⟨8487297091094695022484749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5658198060729796681656499 8487297091094695022484749)
                    ·
                      refine ⟨3182736409160510633431781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487297091094695022484749 3182736409160510633431781)
                      ·
                        rfl

theorem cell23_6198357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6198357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198357 prefixEnd_6198357 := by exact prefixLift 6198357
  have htrace : WordTrace (prefixWord ++ tailWord_6198357) baseStart_6198357 baseEnd_6198357 := by
    simpa [prefixWord, tailWord_6198357, baseEnd_6198357] using wordTrace_append hprefix tailTrace_6198357
  have hstable : (prefixWord ++ tailWord_6198357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198357).length < 2 ^ (prefixWord ++ tailWord_6198357).sum := by decide
  have hdescent : baseEnd_6198357 < baseStart_6198357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198380 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_6198380 : Nat := 118140960795 + 6198380 * 2 ^ 59
def prefixEnd_6198380 : Nat := 4983230072969 + 3 ^ 40 * 6198380 * 2
def baseEnd_6198380 : Nat := 3182748219215564043444175

theorem tailTrace_6198380 : CollatzResearch.WordTrace tailWord_6198380 prefixEnd_6198380 3182748219215564043444175 := by
  unfold tailWord_6198380
  simp only [CollatzResearch.WordTrace]
  refine ⟨113036745642167666934868297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150715660856223555913157729 113036745642167666934868297)
  ·
    refine ⟨84777559231625750201151223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113036745642167666934868297 84777559231625750201151223)
    ·
      refine ⟨127166338847438625301726835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84777559231625750201151223 127166338847438625301726835)
      ·
        refine ⟨190749508271157937952590253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127166338847438625301726835 190749508271157937952590253)
        ·
          refine ⟨71531065601684226732221345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190749508271157937952590253 71531065601684226732221345)
          ·
            refine ⟨53648299201263170049166009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71531065601684226732221345 53648299201263170049166009)
            ·
              refine ⟨40236224400947377536874507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53648299201263170049166009 40236224400947377536874507)
              ·
                refine ⟨60354336601421066305311761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40236224400947377536874507 60354336601421066305311761)
                ·
                  refine ⟨45265752451065799728983821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60354336601421066305311761 45265752451065799728983821)
                  ·
                    refine ⟨16974657169149674898368933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45265752451065799728983821 16974657169149674898368933)
                    ·
                      refine ⟨3182748219215564043444175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16974657169149674898368933 3182748219215564043444175)
                      ·
                        rfl

theorem cell23_6198380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_6198380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198380 prefixEnd_6198380 := by exact prefixLift 6198380
  have htrace : WordTrace (prefixWord ++ tailWord_6198380) baseStart_6198380 baseEnd_6198380 := by
    simpa [prefixWord, tailWord_6198380, baseEnd_6198380] using wordTrace_append hprefix tailTrace_6198380
  have hstable : (prefixWord ++ tailWord_6198380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198380).length < 2 ^ (prefixWord ++ tailWord_6198380).sum := by decide
  have hdescent : baseEnd_6198380 < baseStart_6198380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198400 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_6198400 : Nat := 118140960795 + 6198400 * 2 ^ 59
def prefixEnd_6198400 : Nat := 4983230072969 + 3 ^ 40 * 6198400 * 2
def baseEnd_6198400 : Nat := 3182758488828653965194083

theorem tailTrace_6198400 : CollatzResearch.WordTrace tailWord_6198400 prefixEnd_6198400 3182758488828653965194083 := by
  unfold tailWord_6198400
  simp only [CollatzResearch.WordTrace]
  refine ⟨113037110372131438642732327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150716147162841918190309769 113037110372131438642732327)
  ·
    refine ⟨169555665558197157964098491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113037110372131438642732327 169555665558197157964098491)
    ·
      refine ⟨254333498337295736946147737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169555665558197157964098491 254333498337295736946147737)
      ·
        refine ⟨190750123752971802709610803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254333498337295736946147737 190750123752971802709610803)
        ·
          refine ⟨286125185629457704064416205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190750123752971802709610803 286125185629457704064416205)
          ·
            refine ⟨107296944611046639024156077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286125185629457704064416205 107296944611046639024156077)
            ·
              refine ⟨40236354229142489634058529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107296944611046639024156077 40236354229142489634058529)
              ·
                refine ⟨30177265671856867225543897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40236354229142489634058529 30177265671856867225543897)
                ·
                  refine ⟨22632949253892650419157923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30177265671856867225543897 22632949253892650419157923)
                  ·
                    refine ⟨33949423880838975628736885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22632949253892650419157923 33949423880838975628736885)
                    ·
                      refine ⟨3182758488828653965194083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33949423880838975628736885 3182758488828653965194083)
                      ·
                        rfl

theorem cell23_6198400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_6198400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198400 prefixEnd_6198400 := by exact prefixLift 6198400
  have htrace : WordTrace (prefixWord ++ tailWord_6198400) baseStart_6198400 baseEnd_6198400 := by
    simpa [prefixWord, tailWord_6198400, baseEnd_6198400] using wordTrace_append hprefix tailTrace_6198400
  have hstable : (prefixWord ++ tailWord_6198400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198400).length < 2 ^ (prefixWord ++ tailWord_6198400).sum := by decide
  have hdescent : baseEnd_6198400 < baseStart_6198400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198401 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_6198401 : Nat := 118140960795 + 6198401 * 2 ^ 59
def prefixEnd_6198401 : Nat := 4983230072969 + 3 ^ 40 * 6198401 * 2
def baseEnd_6198401 : Nat := 3182759002309308461281579

theorem tailTrace_6198401 : CollatzResearch.WordTrace tailWord_6198401 prefixEnd_6198401 3182759002309308461281579 := by
  unfold tailWord_6198401
  simp only [CollatzResearch.WordTrace]
  refine ⟨226074257217259254456251057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150716171478172836304167371 226074257217259254456251057)
  ·
    refine ⟨169555692912944440842188293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226074257217259254456251057 169555692912944440842188293)
    ·
      refine ⟨31791692421177082657910305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169555692912944440842188293 31791692421177082657910305)
      ·
        refine ⟨23843769315882811993432729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31791692421177082657910305 23843769315882811993432729)
        ·
          refine ⟨17882826986912108995074547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23843769315882811993432729 17882826986912108995074547)
          ·
            refine ⟨26824240480368163492611821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882826986912108995074547 26824240480368163492611821)
            ·
              refine ⟨10059090180138061309729433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26824240480368163492611821 10059090180138061309729433)
              ·
                refine ⟨7544317635103545982297075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10059090180138061309729433 7544317635103545982297075)
                ·
                  refine ⟨11316476452655318973445613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544317635103545982297075 11316476452655318973445613)
                  ·
                    refine ⟨4243678669745744615042105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11316476452655318973445613 4243678669745744615042105)
                    ·
                      refine ⟨3182759002309308461281579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243678669745744615042105 3182759002309308461281579)
                      ·
                        rfl

theorem cell23_6198401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_6198401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198401 prefixEnd_6198401 := by exact prefixLift 6198401
  have htrace : WordTrace (prefixWord ++ tailWord_6198401) baseStart_6198401 baseEnd_6198401 := by
    simpa [prefixWord, tailWord_6198401, baseEnd_6198401] using wordTrace_append hprefix tailTrace_6198401
  have hstable : (prefixWord ++ tailWord_6198401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198401).length < 2 ^ (prefixWord ++ tailWord_6198401).sum := by decide
  have hdescent : baseEnd_6198401 < baseStart_6198401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198414 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6198414 : Nat := 118140960795 + 6198414 * 2 ^ 59
def prefixEnd_6198414 : Nat := 4983230072969 + 3 ^ 40 * 6198414 * 2
def baseEnd_6198414 : Nat := 3182765677557816910419019

theorem tailTrace_6198414 : CollatzResearch.WordTrace tailWord_6198414 prefixEnd_6198414 3182765677557816910419019 := by
  unfold tailWord_6198414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28259341420776519709559287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150716487577474771784316197 28259341420776519709559287)
  ·
    refine ⟨42389012131164779564338931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28259341420776519709559287 42389012131164779564338931)
    ·
      refine ⟨63583518196747169346508397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42389012131164779564338931 63583518196747169346508397)
      ·
        refine ⟨23843819323780188504940649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63583518196747169346508397 23843819323780188504940649)
        ·
          refine ⟨17882864492835141378705487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23843819323780188504940649 17882864492835141378705487)
          ·
            refine ⟨26824296739252712068058231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17882864492835141378705487 26824296739252712068058231)
            ·
              refine ⟨40236445108879068102087347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26824296739252712068058231 40236445108879068102087347)
              ·
                refine ⟨60354667663318602153131021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40236445108879068102087347 60354667663318602153131021)
                ·
                  refine ⟨22633000373744475807424133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60354667663318602153131021 22633000373744475807424133)
                  ·
                    refine ⟨4243687570077089213892025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22633000373744475807424133 4243687570077089213892025)
                    ·
                      refine ⟨3182765677557816910419019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243687570077089213892025 3182765677557816910419019)
                      ·
                        rfl

theorem cell23_6198414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6198414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198414 prefixEnd_6198414 := by exact prefixLift 6198414
  have htrace : WordTrace (prefixWord ++ tailWord_6198414) baseStart_6198414 baseEnd_6198414 := by
    simpa [prefixWord, tailWord_6198414, baseEnd_6198414] using wordTrace_append hprefix tailTrace_6198414
  have hstable : (prefixWord ++ tailWord_6198414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198414).length < 2 ^ (prefixWord ++ tailWord_6198414).sum := by decide
  have hdescent : baseEnd_6198414 < baseStart_6198414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198418 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6198418 : Nat := 118140960795 + 6198418 * 2 ^ 59
def prefixEnd_6198418 : Nat := 4983230072969 + 3 ^ 40 * 6198418 * 2
def baseEnd_6198418 : Nat := 3182767731480434894769001

theorem tailTrace_6198418 : CollatzResearch.WordTrace tailWord_6198418 prefixEnd_6198418 3182767731480434894769001 := by
  unfold tailWord_6198418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56518719314549416589904977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150716584838798444239746605 56518719314549416589904977)
  ·
    refine ⟨42389039485912062442428733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56518719314549416589904977 42389039485912062442428733)
    ·
      refine ⟨15895889807217023415910775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42389039485912062442428733 15895889807217023415910775)
      ·
        refine ⟨23843834710825535123866163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15895889807217023415910775 23843834710825535123866163)
        ·
          refine ⟨35765752066238302685799245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23843834710825535123866163 35765752066238302685799245)
          ·
            refine ⟨13412157024839363507174717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35765752066238302685799245 13412157024839363507174717)
            ·
              refine ⟨5029558884314761315190519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13412157024839363507174717 5029558884314761315190519)
              ·
                refine ⟨7544338326472141972785779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029558884314761315190519 7544338326472141972785779)
                ·
                  refine ⟨11316507489708212959178669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544338326472141972785779 11316507489708212959178669)
                  ·
                    refine ⟨4243690308640579859692001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11316507489708212959178669 4243690308640579859692001)
                    ·
                      refine ⟨3182767731480434894769001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243690308640579859692001 3182767731480434894769001)
                      ·
                        rfl

theorem cell23_6198418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6198418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198418 prefixEnd_6198418 := by exact prefixLift 6198418
  have htrace : WordTrace (prefixWord ++ tailWord_6198418) baseStart_6198418 baseEnd_6198418 := by
    simpa [prefixWord, tailWord_6198418, baseEnd_6198418] using wordTrace_append hprefix tailTrace_6198418
  have hstable : (prefixWord ++ tailWord_6198418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198418).length < 2 ^ (prefixWord ++ tailWord_6198418).sum := by decide
  have hdescent : baseEnd_6198418 < baseStart_6198418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198487 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_6198487 : Nat := 118140960795 + 6198487 * 2 ^ 59
def prefixEnd_6198487 : Nat := 4983230072969 + 3 ^ 40 * 6198487 * 2
def baseEnd_6198487 : Nat := 3182803161645595124806183

theorem tailTrace_6198487 : CollatzResearch.WordTrace tailWord_6198487 prefixEnd_6198487 3182803161645595124806183 := by
  unfold tailWord_6198487
  simp only [CollatzResearch.WordTrace]
  refine ⟨226077393894947691143881715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150718262596631794095921143 226077393894947691143881715)
  ·
    refine ⟨339116090842421536715822573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226077393894947691143881715 339116090842421536715822573)
    ·
      refine ⟨127168534065908076268433465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339116090842421536715822573 127168534065908076268433465)
      ·
        refine ⟨95376400549431057201325099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127168534065908076268433465 95376400549431057201325099)
        ·
          refine ⟨143064600824146585801987649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95376400549431057201325099 143064600824146585801987649)
          ·
            refine ⟨107298450618109939351490737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143064600824146585801987649 107298450618109939351490737)
            ·
              refine ⟨80473837963582454513618053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107298450618109939351490737 80473837963582454513618053)
              ·
                refine ⟨15088844618171710221303385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80473837963582454513618053 15088844618171710221303385)
                ·
                  refine ⟨11316633463628782665977539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15088844618171710221303385 11316633463628782665977539)
                  ·
                    refine ⟨16974950195443173998966309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11316633463628782665977539 16974950195443173998966309)
                    ·
                      refine ⟨3182803161645595124806183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16974950195443173998966309 3182803161645595124806183)
                      ·
                        rfl

theorem cell23_6198487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_6198487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198487 prefixEnd_6198487 := by exact prefixLift 6198487
  have htrace : WordTrace (prefixWord ++ tailWord_6198487) baseStart_6198487 baseEnd_6198487 := by
    simpa [prefixWord, tailWord_6198487, baseEnd_6198487] using wordTrace_append hprefix tailTrace_6198487
  have hstable : (prefixWord ++ tailWord_6198487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198487).length < 2 ^ (prefixWord ++ tailWord_6198487).sum := by decide
  have hdescent : baseEnd_6198487 < baseStart_6198487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198504 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6198504 : Nat := 118140960795 + 6198504 * 2 ^ 59
def prefixEnd_6198504 : Nat := 4983230072969 + 3 ^ 40 * 6198504 * 2
def baseEnd_6198504 : Nat := 3182811890816721558293605

theorem tailTrace_6198504 : CollatzResearch.WordTrace tailWord_6198504 prefixEnd_6198504 3182811890816721558293605 := by
  unfold tailWord_6198504
  simp only [CollatzResearch.WordTrace]
  refine ⟨113039006967943051523625283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150718675957257402031500377 113039006967943051523625283)
  ·
    refine ⟨169558510451914577285437925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113039006967943051523625283 169558510451914577285437925)
    ·
      refine ⟨31792220709733983241019611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169558510451914577285437925 31792220709733983241019611)
      ·
        refine ⟨47688331064600974861529417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31792220709733983241019611 47688331064600974861529417)
        ·
          refine ⟨35766248298450731146147063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47688331064600974861529417 35766248298450731146147063)
          ·
            refine ⟨53649372447676096719220595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35766248298450731146147063 53649372447676096719220595)
            ·
              refine ⟨80474058671514145078830893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53649372447676096719220595 80474058671514145078830893)
              ·
                refine ⟨30177772001817804404561585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80474058671514145078830893 30177772001817804404561585)
                ·
                  refine ⟨22633329001363353303421189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30177772001817804404561585 22633329001363353303421189)
                  ·
                    refine ⟨4243749187755628744391473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22633329001363353303421189 4243749187755628744391473)
                    ·
                      refine ⟨3182811890816721558293605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243749187755628744391473 3182811890816721558293605)
                      ·
                        rfl

theorem cell23_6198504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6198504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198504 prefixEnd_6198504 := by exact prefixLift 6198504
  have htrace : WordTrace (prefixWord ++ tailWord_6198504) baseStart_6198504 baseEnd_6198504 := by
    simpa [prefixWord, tailWord_6198504, baseEnd_6198504] using wordTrace_append hprefix tailTrace_6198504
  have hstable : (prefixWord ++ tailWord_6198504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198504).length < 2 ^ (prefixWord ++ tailWord_6198504).sum := by decide
  have hdescent : baseEnd_6198504 < baseStart_6198504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198507 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3]
def baseStart_6198507 : Nat := 118140960795 + 6198507 * 2 ^ 59
def prefixEnd_6198507 : Nat := 4983230072969 + 3 ^ 40 * 6198507 * 2
def baseEnd_6198507 : Nat := 3182813431258685046556091

theorem tailTrace_6198507 : CollatzResearch.WordTrace tailWord_6198507 prefixEnd_6198507 3182813431258685046556091 := by
  unfold tailWord_6198507
  simp only [CollatzResearch.WordTrace]
  refine ⟨226078123354875234559609775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150718748903250156373073183 226078123354875234559609775)
  ·
    refine ⟨339117185032312851839414663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226078123354875234559609775 339117185032312851839414663)
    ·
      refine ⟨508675777548469277759121995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339117185032312851839414663 508675777548469277759121995)
      ·
        refine ⟨763013666322703916638682993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508675777548469277759121995 763013666322703916638682993)
        ·
          refine ⟨572260249742027937479012245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763013666322703916638682993 572260249742027937479012245)
          ·
            refine ⟨26824699206657559569328699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 572260249742027937479012245 26824699206657559569328699)
            ·
              refine ⟨40237048809986339353993049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26824699206657559569328699 40237048809986339353993049)
              ·
                refine ⟨30177786607489754515494787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40237048809986339353993049 30177786607489754515494787)
                ·
                  refine ⟨45266679911234631773242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30177786607489754515494787 45266679911234631773242181)
                  ·
                    refine ⟨8487502483356493457482909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45266679911234631773242181 8487502483356493457482909)
                    ·
                      refine ⟨3182813431258685046556091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8487502483356493457482909 3182813431258685046556091)
                      ·
                        rfl

theorem cell23_6198507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 3].length) (baseStart_6198507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198507 prefixEnd_6198507 := by exact prefixLift 6198507
  have htrace : WordTrace (prefixWord ++ tailWord_6198507) baseStart_6198507 baseEnd_6198507 := by
    simpa [prefixWord, tailWord_6198507, baseEnd_6198507] using wordTrace_append hprefix tailTrace_6198507
  have hstable : (prefixWord ++ tailWord_6198507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198507).length < 2 ^ (prefixWord ++ tailWord_6198507).sum := by decide
  have hdescent : baseEnd_6198507 < baseStart_6198507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198520 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_6198520 : Nat := 118140960795 + 6198520 * 2 ^ 59
def prefixEnd_6198520 : Nat := 4983230072969 + 3 ^ 40 * 6198520 * 2
def baseEnd_6198520 : Nat := 3182820106507193495693531

theorem tailTrace_6198520 : CollatzResearch.WordTrace tailWord_6198520 prefixEnd_6198520 3182820106507193495693531 := by
  unfold tailWord_6198520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113039298751914068889916507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150719065002552091853222009 113039298751914068889916507)
  ·
    refine ⟨169558948127871103334874761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113039298751914068889916507 169558948127871103334874761)
    ·
      refine ⟨127169211095903327501156071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169558948127871103334874761 127169211095903327501156071)
      ·
        refine ⟨190753816643854991251734107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127169211095903327501156071 190753816643854991251734107)
        ·
          refine ⟨286130724965782486877601161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190753816643854991251734107 286130724965782486877601161)
          ·
            refine ⟨214598043724336865158200871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286130724965782486877601161 214598043724336865158200871)
            ·
              refine ⟨321897065586505297737301307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214598043724336865158200871 321897065586505297737301307)
              ·
                refine ⟨482845598379757946605951961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321897065586505297737301307 482845598379757946605951961)
                ·
                  refine ⟨362134198784818459954463971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482845598379757946605951961 362134198784818459954463971)
                  ·
                    refine ⟨543201298177227689931695957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362134198784818459954463971 543201298177227689931695957)
                    ·
                      refine ⟨3182820106507193495693531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 543201298177227689931695957 3182820106507193495693531)
                      ·
                        rfl

theorem cell23_6198520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_6198520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198520 prefixEnd_6198520 := by exact prefixLift 6198520
  have htrace : WordTrace (prefixWord ++ tailWord_6198520) baseStart_6198520 baseEnd_6198520 := by
    simpa [prefixWord, tailWord_6198520, baseEnd_6198520] using wordTrace_append hprefix tailTrace_6198520
  have hstable : (prefixWord ++ tailWord_6198520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198520).length < 2 ^ (prefixWord ++ tailWord_6198520).sum := by decide
  have hdescent : baseEnd_6198520 < baseStart_6198520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198531 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 1, 4]
def baseStart_6198531 : Nat := 118140960795 + 6198531 * 2 ^ 59
def prefixEnd_6198531 : Nat := 4983230072969 + 3 ^ 40 * 6198531 * 2
def baseEnd_6198531 : Nat := 1060941918264797650885327

theorem tailTrace_6198531 : CollatzResearch.WordTrace tailWord_6198531 prefixEnd_6198531 1060941918264797650885327 := by
  unfold tailWord_6198531
  simp only [CollatzResearch.WordTrace]
  refine ⟨226078998706788286658483447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150719332471192191105655631 226078998706788286658483447)
  ·
    refine ⟨339118498060182429987725171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226078998706788286658483447 339118498060182429987725171)
    ·
      refine ⟨508677747090273644981587757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339118498060182429987725171 508677747090273644981587757)
      ·
        refine ⟨190754155158852616868095409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 508677747090273644981587757 190754155158852616868095409)
        ·
          refine ⟨143065616369139462651071557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190754155158852616868095409 143065616369139462651071557)
          ·
            refine ⟨26824803069213649247075917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143065616369139462651071557 26824803069213649247075917)
            ·
              refine ⟨10059301150955118467653469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26824803069213649247075917 10059301150955118467653469)
              ·
                refine ⟨3772237931608169425370051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10059301150955118467653469 3772237931608169425370051)
                ·
                  refine ⟨5658356897412254138055077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772237931608169425370051 5658356897412254138055077)
                  ·
                    refine ⟨1060941918264797650885327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5658356897412254138055077 1060941918264797650885327)
                    ·
                      rfl

theorem cell23_6198531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 4].length) (baseStart_6198531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198531 prefixEnd_6198531 := by exact prefixLift 6198531
  have htrace : WordTrace (prefixWord ++ tailWord_6198531) baseStart_6198531 baseEnd_6198531 := by
    simpa [prefixWord, tailWord_6198531, baseEnd_6198531] using wordTrace_append hprefix tailTrace_6198531
  have hstable : (prefixWord ++ tailWord_6198531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198531).length < 2 ^ (prefixWord ++ tailWord_6198531).sum := by decide
  have hdescent : baseEnd_6198531 < baseStart_6198531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198581 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_6198581 : Nat := 118140960795 + 6198581 * 2 ^ 59
def prefixEnd_6198581 : Nat := 4983230072969 + 3 ^ 40 * 6198581 * 2
def baseEnd_6198581 : Nat := 3182851428827117757030751

theorem tailTrace_6198581 : CollatzResearch.WordTrace tailWord_6198581 prefixEnd_6198581 3182851428827117757030751 := by
  unfold tailWord_6198581
  simp only [CollatzResearch.WordTrace]
  refine ⟨226080822356607145197803597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150720548237738096798535731 226080822356607145197803597)
  ·
    refine ⟨84780308383727679449176349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226080822356607145197803597 84780308383727679449176349)
    ·
      refine ⟨31792615643897879793441131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84780308383727679449176349 31792615643897879793441131)
      ·
        refine ⟨47688923465846819690161697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31792615643897879793441131 47688923465846819690161697)
        ·
          refine ⟨35766692599385114767621273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47688923465846819690161697 35766692599385114767621273)
          ·
            refine ⟨26825019449538836075715955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35766692599385114767621273 26825019449538836075715955)
            ·
              refine ⟨40237529174308254113573933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26825019449538836075715955 40237529174308254113573933)
              ·
                refine ⟨15089073440365595292590225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40237529174308254113573933 15089073440365595292590225)
                ·
                  refine ⟨11316805080274196469442669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15089073440365595292590225 11316805080274196469442669)
                  ·
                    refine ⟨4243801905102823676041001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11316805080274196469442669 4243801905102823676041001)
                    ·
                      refine ⟨3182851428827117757030751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243801905102823676041001 3182851428827117757030751)
                      ·
                        rfl

theorem cell23_6198581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_6198581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198581 prefixEnd_6198581 := by exact prefixLift 6198581
  have htrace : WordTrace (prefixWord ++ tailWord_6198581) baseStart_6198581 baseEnd_6198581 := by
    simpa [prefixWord, tailWord_6198581, baseEnd_6198581] using wordTrace_append hprefix tailTrace_6198581
  have hstable : (prefixWord ++ tailWord_6198581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198581).length < 2 ^ (prefixWord ++ tailWord_6198581).sum := by decide
  have hdescent : baseEnd_6198581 < baseStart_6198581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198591 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 1, 5]
def baseStart_6198591 : Nat := 118140960795 + 6198591 * 2 ^ 59
def prefixEnd_6198591 : Nat := 4983230072969 + 3 ^ 40 * 6198591 * 2
def baseEnd_6198591 : Nat := 1060952187877887572635235

theorem tailTrace_6198591 : CollatzResearch.WordTrace tailWord_6198591 prefixEnd_6198591 1060952187877887572635235 := by
  unfold tailWord_6198591
  simp only [CollatzResearch.WordTrace]
  refine ⟨226081187086570916905667627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150720791391047277937111751 226081187086570916905667627)
  ·
    refine ⟨339121780629856375358501441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226081187086570916905667627 339121780629856375358501441)
    ·
      refine ⟨254341335472392281518876081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339121780629856375358501441 254341335472392281518876081)
      ·
        refine ⟨190756001604294211139157061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254341335472392281518876081 190756001604294211139157061)
        ·
          refine ⟨35766750300805164588591949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190756001604294211139157061 35766750300805164588591949)
          ·
            refine ⟨13412531362801936720721981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35766750300805164588591949 13412531362801936720721981)
            ·
              refine ⟨5029699261050726270270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13412531362801936720721981 5029699261050726270270743)
              ·
                refine ⟨7544548891576089405406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029699261050726270270743 7544548891576089405406115)
                ·
                  refine ⟨11316823337364134108109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544548891576089405406115 11316823337364134108109173)
                  ·
                    refine ⟨1060952187877887572635235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11316823337364134108109173 1060952187877887572635235)
                    ·
                      rfl

theorem cell23_6198591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_6198591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198591 prefixEnd_6198591 := by exact prefixLift 6198591
  have htrace : WordTrace (prefixWord ++ tailWord_6198591) baseStart_6198591 baseEnd_6198591 := by
    simpa [prefixWord, tailWord_6198591, baseEnd_6198591] using wordTrace_append hprefix tailTrace_6198591
  have hstable : (prefixWord ++ tailWord_6198591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198591).length < 2 ^ (prefixWord ++ tailWord_6198591).sum := by decide
  have hdescent : baseEnd_6198591 < baseStart_6198591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198611 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 3, 2, 2]
def baseStart_6198611 : Nat := 118140960795 + 6198611 * 2 ^ 59
def prefixEnd_6198611 : Nat := 4983230072969 + 3 ^ 40 * 6198611 * 2
def baseEnd_6198611 : Nat := 3182866833246752639655613

theorem tailTrace_6198611 : CollatzResearch.WordTrace tailWord_6198611 prefixEnd_6198611 3182866833246752639655613 := by
  unfold tailWord_6198611
  simp only [CollatzResearch.WordTrace]
  refine ⟨226081916546498460321395687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150721277697665640214263791 226081916546498460321395687)
  ·
    refine ⟨339122874819747690482093531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226081916546498460321395687 339122874819747690482093531)
    ·
      refine ⟨508684312229621535723140297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339122874819747690482093531 508684312229621535723140297)
      ·
        refine ⟨381513234172216151792355223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508684312229621535723140297 381513234172216151792355223)
        ·
          refine ⟨572269851258324227688532835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381513234172216151792355223 572269851258324227688532835)
          ·
            refine ⟨858404776887486341532799253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572269851258324227688532835 858404776887486341532799253)
            ·
              refine ⟨40237723916600922259349965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 858404776887486341532799253 40237723916600922259349965)
              ·
                refine ⟨15089146468725345847256237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40237723916600922259349965 15089146468725345847256237)
                ·
                  refine ⟨5658429925772004692721089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15089146468725345847256237 5658429925772004692721089)
                  ·
                    refine ⟨4243822444329003519540817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5658429925772004692721089 4243822444329003519540817)
                    ·
                      refine ⟨3182866833246752639655613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4243822444329003519540817 3182866833246752639655613)
                      ·
                        rfl

theorem cell23_6198611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2, 2].length) (baseStart_6198611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198611 prefixEnd_6198611 := by exact prefixLift 6198611
  have htrace : WordTrace (prefixWord ++ tailWord_6198611) baseStart_6198611 baseEnd_6198611 := by
    simpa [prefixWord, tailWord_6198611, baseEnd_6198611] using wordTrace_append hprefix tailTrace_6198611
  have hstable : (prefixWord ++ tailWord_6198611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198611).length < 2 ^ (prefixWord ++ tailWord_6198611).sum := by decide
  have hdescent : baseEnd_6198611 < baseStart_6198611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198617 : List Nat := [1, 2, 1, 2, 2, 2, 5, 8]
def baseStart_6198617 : Nat := 118140960795 + 6198617 * 2 ^ 59
def prefixEnd_6198617 : Nat := 4983230072969 + 3 ^ 40 * 6198617 * 2
def baseEnd_6198617 : Nat := 117884070893728874673355

theorem tailTrace_6198617 : CollatzResearch.WordTrace tailWord_6198617 prefixEnd_6198617 117884070893728874673355 := by
  unfold tailWord_6198617
  simp only [CollatzResearch.WordTrace]
  refine ⟨226082135384476723346114105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150721423589651148897409403 226082135384476723346114105)
  ·
    refine ⟨169561601538357542509585579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226082135384476723346114105 169561601538357542509585579)
    ·
      refine ⟨254342402307536313764378369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169561601538357542509585579 254342402307536313764378369)
      ·
        refine ⟨190756801730652235323283777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254342402307536313764378369 190756801730652235323283777)
        ·
          refine ⟨143067601297989176492462833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190756801730652235323283777 143067601297989176492462833)
          ·
            refine ⟨107300700973491882369347125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143067601297989176492462833 107300700973491882369347125)
            ·
              refine ⟨10059440716264863972126293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107300700973491882369347125 10059440716264863972126293)
              ·
                refine ⟨117884070893728874673355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10059440716264863972126293 117884070893728874673355)
                ·
                  rfl

theorem cell23_6198617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 8].length) (baseStart_6198617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6198617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6198617 prefixEnd_6198617 := by exact prefixLift 6198617
  have htrace : WordTrace (prefixWord ++ tailWord_6198617) baseStart_6198617 baseEnd_6198617 := by
    simpa [prefixWord, tailWord_6198617, baseEnd_6198617] using wordTrace_append hprefix tailTrace_6198617
  have hstable : (prefixWord ++ tailWord_6198617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198617).length < 2 ^ (prefixWord ++ tailWord_6198617).sum := by decide
  have hdescent : baseEnd_6198617 < baseStart_6198617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
