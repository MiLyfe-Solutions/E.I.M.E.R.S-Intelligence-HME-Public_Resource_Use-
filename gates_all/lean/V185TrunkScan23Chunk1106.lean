import V185TrunkScan23Chunk1105

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6549558 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6549558 : Nat := 118140960795 + 6549558 * 2 ^ 59
def prefixEnd_6549558 : Nat := 4983230072969 + 3 ^ 40 * 6549558 * 2
def baseEnd_6549558 : Nat := 3363071328500191057904137

theorem tailTrace_6549558 : CollatzResearch.WordTrace tailWord_6549558 prefixEnd_6549558 3363071328500191057904137 := by
  unfold tailWord_6549558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930125325379838518573083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159254670137384944198112885 14930125325379838518573083)
  ·
    refine ⟨22395187988069757777859625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14930125325379838518573083 22395187988069757777859625)
    ·
      refine ⟨16796390991052318333394719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22395187988069757777859625 16796390991052318333394719)
      ·
        refine ⟨25194586486578477500092079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16796390991052318333394719 25194586486578477500092079)
        ·
          refine ⟨37791879729867716250138119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25194586486578477500092079 37791879729867716250138119)
          ·
            refine ⟨56687819594801574375207179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37791879729867716250138119 56687819594801574375207179)
            ·
              refine ⟨85031729392202361562810769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56687819594801574375207179 85031729392202361562810769)
              ·
                refine ⟨63773797044151771172108077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85031729392202361562810769 63773797044151771172108077)
                ·
                  refine ⟨23915173891556914189540529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63773797044151771172108077 23915173891556914189540529)
                  ·
                    refine ⟨17936380418667685642155397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23915173891556914189540529 17936380418667685642155397)
                    ·
                      refine ⟨3363071328500191057904137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17936380418667685642155397 3363071328500191057904137)
                      ·
                        rfl

theorem cell23_6549558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6549558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549558 prefixEnd_6549558 := by exact prefixLift 6549558
  have htrace : WordTrace (prefixWord ++ tailWord_6549558) baseStart_6549558 baseEnd_6549558 := by
    simpa [prefixWord, tailWord_6549558, baseEnd_6549558] using wordTrace_append hprefix tailTrace_6549558
  have hstable : (prefixWord ++ tailWord_6549558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549558).length < 2 ^ (prefixWord ++ tailWord_6549558).sum := by decide
  have hdescent : baseEnd_6549558 < baseStart_6549558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549578 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_6549578 : Nat := 118140960795 + 6549578 * 2 ^ 59
def prefixEnd_6549578 : Nat := 4983230072969 + 3 ^ 40 * 6549578 * 2
def baseEnd_6549578 : Nat := 3363081598113280979654045

theorem tailTrace_6549578 : CollatzResearch.WordTrace tailWord_6549578 prefixEnd_6549578 3363081598113280979654045 := by
  unfold tailWord_6549578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59720683666501239928224347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159255156444003306475264925 59720683666501239928224347)
  ·
    refine ⟨89581025499751859892336521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59720683666501239928224347 89581025499751859892336521)
    ·
      refine ⟨67185769124813894919252391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89581025499751859892336521 67185769124813894919252391)
      ·
        refine ⟨100778653687220842378878587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67185769124813894919252391 100778653687220842378878587)
        ·
          refine ⟨151167980530831263568317881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100778653687220842378878587 151167980530831263568317881)
          ·
            refine ⟨113375985398123447676238411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151167980530831263568317881 113375985398123447676238411)
            ·
              refine ⟨170063978097185171514357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113375985398123447676238411 170063978097185171514357617)
              ·
                refine ⟨127547983572888878635768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170063978097185171514357617 127547983572888878635768213)
                ·
                  refine ⟨5978811729979166186051635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127547983572888878635768213 5978811729979166186051635)
                  ·
                    refine ⟨8968217594968749279077453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978811729979166186051635 8968217594968749279077453)
                    ·
                      refine ⟨3363081598113280979654045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968217594968749279077453 3363081598113280979654045)
                      ·
                        rfl

theorem cell23_6549578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_6549578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549578 prefixEnd_6549578 := by exact prefixLift 6549578
  have htrace : WordTrace (prefixWord ++ tailWord_6549578) baseStart_6549578 baseEnd_6549578 := by
    simpa [prefixWord, tailWord_6549578, baseEnd_6549578] using wordTrace_append hprefix tailTrace_6549578
  have hstable : (prefixWord ++ tailWord_6549578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549578).length < 2 ^ (prefixWord ++ tailWord_6549578).sum := by decide
  have hdescent : baseEnd_6549578 < baseStart_6549578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549612 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_6549612 : Nat := 118140960795 + 6549612 * 2 ^ 59
def prefixEnd_6549612 : Nat := 4983230072969 + 3 ^ 40 * 6549612 * 2
def baseEnd_6549612 : Nat := 3363099056455533846628889

theorem tailTrace_6549612 : CollatzResearch.WordTrace tailWord_6549612 prefixEnd_6549612 3363099056455533846628889 := by
  unfold tailWord_6549612
  simp only [CollatzResearch.WordTrace]
  refine ⟨119441987373940891759817545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159255983165254522346423393 119441987373940891759817545)
  ·
    refine ⟨89581490530455668819863159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119441987373940891759817545 89581490530455668819863159)
    ·
      refine ⟨134372235795683503229794739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89581490530455668819863159 134372235795683503229794739)
      ·
        refine ⟨201558353693525254844692109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134372235795683503229794739 201558353693525254844692109)
        ·
          refine ⟨75584382635071970566759541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201558353693525254844692109 75584382635071970566759541)
          ·
            refine ⟨7086035872037997240633707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75584382635071970566759541 7086035872037997240633707)
            ·
              refine ⟨10629053808056995860950561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086035872037997240633707 10629053808056995860950561)
              ·
                refine ⟨7971790356042746895712921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10629053808056995860950561 7971790356042746895712921)
                ·
                  refine ⟨5978842767032060171784691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7971790356042746895712921 5978842767032060171784691)
                  ·
                    refine ⟨8968264150548090257677037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978842767032060171784691 8968264150548090257677037)
                    ·
                      refine ⟨3363099056455533846628889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968264150548090257677037 3363099056455533846628889)
                      ·
                        rfl

theorem cell23_6549612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_6549612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549612 prefixEnd_6549612 := by exact prefixLift 6549612
  have htrace : WordTrace (prefixWord ++ tailWord_6549612) baseStart_6549612 baseEnd_6549612 := by
    simpa [prefixWord, tailWord_6549612, baseEnd_6549612] using wordTrace_append hprefix tailTrace_6549612
  have hstable : (prefixWord ++ tailWord_6549612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549612).length < 2 ^ (prefixWord ++ tailWord_6549612).sum := by decide
  have hdescent : baseEnd_6549612 < baseStart_6549612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549635 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 4, 2]
def baseStart_6549635 : Nat := 118140960795 + 6549635 * 2 ^ 59
def prefixEnd_6549635 : Nat := 4983230072969 + 3 ^ 40 * 6549635 * 2
def baseEnd_6549635 : Nat := 3363110866510587256641283

theorem tailTrace_6549635 : CollatzResearch.WordTrace tailWord_6549635 prefixEnd_6549635 3363110866510587256641283 := by
  unfold tailWord_6549635
  simp only [CollatzResearch.WordTrace]
  refine ⟨238884813626798458447722359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159256542417865638965148239 238884813626798458447722359)
  ·
    refine ⟨358327220440197687671583539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238884813626798458447722359 358327220440197687671583539)
    ·
      refine ⟨537490830660296531507375309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358327220440197687671583539 537490830660296531507375309)
      ·
        refine ⟨201559061497611199315265741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537490830660296531507375309 201559061497611199315265741)
        ·
          refine ⟨75584648061604199743224653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201559061497611199315265741 75584648061604199743224653)
          ·
            refine ⟨28344243023101574903709245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75584648061604199743224653 28344243023101574903709245)
            ·
              refine ⟨10629091133663090588890967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28344243023101574903709245 10629091133663090588890967)
              ·
                refine ⟨15943636700494635883336451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629091133663090588890967 15943636700494635883336451)
                ·
                  refine ⟨23915455050741953825004677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15943636700494635883336451 23915455050741953825004677)
                  ·
                    refine ⟨4484147822014116342188377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23915455050741953825004677 4484147822014116342188377)
                    ·
                      refine ⟨3363110866510587256641283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484147822014116342188377 3363110866510587256641283)
                      ·
                        rfl

theorem cell23_6549635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_6549635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549635 prefixEnd_6549635 := by exact prefixLift 6549635
  have htrace : WordTrace (prefixWord ++ tailWord_6549635) baseStart_6549635 baseEnd_6549635 := by
    simpa [prefixWord, tailWord_6549635, baseEnd_6549635] using wordTrace_append hprefix tailTrace_6549635
  have hstable : (prefixWord ++ tailWord_6549635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549635).length < 2 ^ (prefixWord ++ tailWord_6549635).sum := by decide
  have hdescent : baseEnd_6549635 < baseStart_6549635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549641 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 7]
def baseStart_6549641 : Nat := 118140960795 + 6549641 * 2 ^ 59
def prefixEnd_6549641 : Nat := 4983230072969 + 3 ^ 40 * 6549641 * 2
def baseEnd_6549641 : Nat := 373679327488279359240695

theorem tailTrace_6549641 : CollatzResearch.WordTrace tailWord_6549641 prefixEnd_6549641 373679327488279359240695 := by
  unfold tailWord_6549641
  simp only [CollatzResearch.WordTrace]
  refine ⟨238885032464776721472440777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159256688309851147648293851 238885032464776721472440777)
  ·
    refine ⟨179163774348582541104330583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238885032464776721472440777 179163774348582541104330583)
    ·
      refine ⟨268745661522873811656495875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179163774348582541104330583 268745661522873811656495875)
      ·
        refine ⟨403118492284310717484743813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268745661522873811656495875 403118492284310717484743813)
        ·
          refine ⟨75584717303308259528389465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403118492284310717484743813 75584717303308259528389465)
          ·
            refine ⟨56688537977481194646292099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75584717303308259528389465 56688537977481194646292099)
            ·
              refine ⟨85032806966221791969438149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56688537977481194646292099 85032806966221791969438149)
              ·
                refine ⟨15943651306166585994269653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85032806966221791969438149 15943651306166585994269653)
                ·
                  refine ⟨373679327488279359240695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15943651306166585994269653 373679327488279359240695)
                  ·
                    rfl

theorem cell23_6549641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_6549641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549641 prefixEnd_6549641 := by exact prefixLift 6549641
  have htrace : WordTrace (prefixWord ++ tailWord_6549641) baseStart_6549641 baseEnd_6549641 := by
    simpa [prefixWord, tailWord_6549641, baseEnd_6549641] using wordTrace_append hprefix tailTrace_6549641
  have hstable : (prefixWord ++ tailWord_6549641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549641).length < 2 ^ (prefixWord ++ tailWord_6549641).sum := by decide
  have hdescent : baseEnd_6549641 < baseStart_6549641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549701 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_6549701 : Nat := 118140960795 + 6549701 * 2 ^ 59
def prefixEnd_6549701 : Nat := 4983230072969 + 3 ^ 40 * 6549701 * 2
def baseEnd_6549701 : Nat := 1121048252077927999471993

theorem tailTrace_6549701 : CollatzResearch.WordTrace tailWord_6549701 prefixEnd_6549701 1121048252077927999471993 := by
  unfold tailWord_6549701
  simp only [CollatzResearch.WordTrace]
  refine ⟨238887220844559351719624957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159258147229706234479749971 238887220844559351719624957)
  ·
    refine ⟨89582707816709756894859359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238887220844559351719624957 89582707816709756894859359)
    ·
      refine ⟨134374061725064635342289039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89582707816709756894859359 134374061725064635342289039)
      ·
        refine ⟨201561092587596953013433559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134374061725064635342289039 201561092587596953013433559)
        ·
          refine ⟨302341638881395429520150339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201561092587596953013433559 302341638881395429520150339)
          ·
            refine ⟨453512458322093144280225509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302341638881395429520150339 453512458322093144280225509)
            ·
              refine ⟨85033585935392464552542283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453512458322093144280225509 85033585935392464552542283)
              ·
                refine ⟨127550378903088696828813425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85033585935392464552542283 127550378903088696828813425)
                ·
                  refine ⟨95662784177316522621610069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127550378903088696828813425 95662784177316522621610069)
                  ·
                    refine ⟨1121048252077927999471993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95662784177316522621610069 1121048252077927999471993)
                    ·
                      rfl

theorem cell23_6549701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_6549701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549701 prefixEnd_6549701 := by exact prefixLift 6549701
  have htrace : WordTrace (prefixWord ++ tailWord_6549701) baseStart_6549701 baseEnd_6549701 := by
    simpa [prefixWord, tailWord_6549701, baseEnd_6549701] using wordTrace_append hprefix tailTrace_6549701
  have hstable : (prefixWord ++ tailWord_6549701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549701).length < 2 ^ (prefixWord ++ tailWord_6549701).sum := by decide
  have hdescent : baseEnd_6549701 < baseStart_6549701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549762 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_6549762 : Nat := 118140960795 + 6549762 * 2 ^ 59
def prefixEnd_6549762 : Nat := 4983230072969 + 3 ^ 40 * 6549762 * 2
def baseEnd_6549762 : Nat := 3363176078553708259753199

theorem tailTrace_6549762 : CollatzResearch.WordTrace tailWord_6549762 prefixEnd_6549762 3363176078553708259753199 := by
  unfold tailWord_6549762
  simp only [CollatzResearch.WordTrace]
  refine ⟨59722361424334589784398885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159259630464892239425063693 59722361424334589784398885)
  ·
    refine ⟨11197942767062735584574791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59722361424334589784398885 11197942767062735584574791)
    ·
      refine ⟨16796914150594103376862187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197942767062735584574791 16796914150594103376862187)
      ·
        refine ⟨25195371225891155065293281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16796914150594103376862187 25195371225891155065293281)
        ·
          refine ⟨18896528419418366298969961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25195371225891155065293281 18896528419418366298969961)
          ·
            refine ⟨14172396314563774724227471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18896528419418366298969961 14172396314563774724227471)
            ·
              refine ⟨21258594471845662086341207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14172396314563774724227471 21258594471845662086341207)
              ·
                refine ⟨31887891707768493129511811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21258594471845662086341207 31887891707768493129511811)
                ·
                  refine ⟨47831837561652739694267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31887891707768493129511811 47831837561652739694267717)
                  ·
                    refine ⟨8968469542809888692675197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47831837561652739694267717 8968469542809888692675197)
                    ·
                      refine ⟨3363176078553708259753199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968469542809888692675197 3363176078553708259753199)
                      ·
                        rfl

theorem cell23_6549762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_6549762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549762 prefixEnd_6549762 := by exact prefixLift 6549762
  have htrace : WordTrace (prefixWord ++ tailWord_6549762) baseStart_6549762 baseEnd_6549762 := by
    simpa [prefixWord, tailWord_6549762, baseEnd_6549762] using wordTrace_append hprefix tailTrace_6549762
  have hstable : (prefixWord ++ tailWord_6549762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549762).length < 2 ^ (prefixWord ++ tailWord_6549762).sum := by decide
  have hdescent : baseEnd_6549762 < baseStart_6549762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549792 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6549792 : Nat := 118140960795 + 6549792 * 2 ^ 59
def prefixEnd_6549792 : Nat := 4983230072969 + 3 ^ 40 * 6549792 * 2
def baseEnd_6549792 : Nat := 3363191482973343142378061

theorem tailTrace_6549792 : CollatzResearch.WordTrace tailWord_6549792 prefixEnd_6549792 3363191482973343142378061 := by
  unfold tailWord_6549792
  simp only [CollatzResearch.WordTrace]
  refine ⟨119445269943614837130593815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159260359924819782840791753 119445269943614837130593815)
  ·
    refine ⟨179167904915422255695890723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119445269943614837130593815 179167904915422255695890723)
    ·
      refine ⟨268751857373133383543836085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179167904915422255695890723 268751857373133383543836085)
      ·
        refine ⟨25195486628731254707234633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268751857373133383543836085 25195486628731254707234633)
        ·
          refine ⟨18896614971548441030425975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25195486628731254707234633 18896614971548441030425975)
          ·
            refine ⟨28344922457322661545638963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896614971548441030425975 28344922457322661545638963)
            ·
              refine ⟨42517383685983992318458445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28344922457322661545638963 42517383685983992318458445)
              ·
                refine ⟨15944018882243997119421917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42517383685983992318458445 15944018882243997119421917)
                ·
                  refine ⟨5979007080841498919783219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15944018882243997119421917 5979007080841498919783219)
                  ·
                    refine ⟨8968510621262248379674829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979007080841498919783219 8968510621262248379674829)
                    ·
                      refine ⟨3363191482973343142378061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968510621262248379674829 3363191482973343142378061)
                      ·
                        rfl

theorem cell23_6549792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6549792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549792 prefixEnd_6549792 := by exact prefixLift 6549792
  have htrace : WordTrace (prefixWord ++ tailWord_6549792) baseStart_6549792 baseEnd_6549792 := by
    simpa [prefixWord, tailWord_6549792, baseEnd_6549792] using wordTrace_append hprefix tailTrace_6549792
  have hstable : (prefixWord ++ tailWord_6549792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549792).length < 2 ^ (prefixWord ++ tailWord_6549792).sum := by decide
  have hdescent : baseEnd_6549792 < baseStart_6549792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549808 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_6549808 : Nat := 118140960795 + 6549808 * 2 ^ 59
def prefixEnd_6549808 : Nat := 4983230072969 + 3 ^ 40 * 6549808 * 2
def baseEnd_6549808 : Nat := 1121066566221271693259329

theorem tailTrace_6549808 : CollatzResearch.WordTrace tailWord_6549808 prefixEnd_6549808 1121066566221271693259329 := by
  unfold tailWord_6549808
  simp only [CollatzResearch.WordTrace]
  refine ⟨119445561727585854496885039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159260748970114472662513385 119445561727585854496885039)
  ·
    refine ⟨179168342591378781745327559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119445561727585854496885039 179168342591378781745327559)
    ·
      refine ⟨268752513887068172617991339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179168342591378781745327559 268752513887068172617991339)
      ·
        refine ⟨403128770830602258926987009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268752513887068172617991339 403128770830602258926987009)
        ·
          refine ⟨302346578122951694195240257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403128770830602258926987009 302346578122951694195240257)
          ·
            refine ⟨226759933592213770646430193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302346578122951694195240257 226759933592213770646430193)
            ·
              refine ⟨170069950194160327984822645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226759933592213770646430193 170069950194160327984822645)
              ·
                refine ⟨15944057830702530748577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170069950194160327984822645 15944057830702530748577123)
                ·
                  refine ⟨23916086746053796122865685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15944057830702530748577123 23916086746053796122865685)
                  ·
                    refine ⟨1121066566221271693259329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23916086746053796122865685 1121066566221271693259329)
                    ·
                      rfl

theorem cell23_6549808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_6549808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549808 prefixEnd_6549808 := by exact prefixLift 6549808
  have htrace : WordTrace (prefixWord ++ tailWord_6549808) baseStart_6549808 baseEnd_6549808 := by
    simpa [prefixWord, tailWord_6549808, baseEnd_6549808] using wordTrace_append hprefix tailTrace_6549808
  have hstable : (prefixWord ++ tailWord_6549808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549808).length < 2 ^ (prefixWord ++ tailWord_6549808).sum := by decide
  have hdescent : baseEnd_6549808 < baseStart_6549808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549812 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_6549812 : Nat := 118140960795 + 6549812 * 2 ^ 59
def prefixEnd_6549812 : Nat := 4983230072969 + 3 ^ 40 * 6549812 * 2
def baseEnd_6549812 : Nat := 1121067250862144354709323

theorem tailTrace_6549812 : CollatzResearch.WordTrace tailWord_6549812 prefixEnd_6549812 1121067250862144354709323 := by
  unfold tailWord_6549812
  simp only [CollatzResearch.WordTrace]
  refine ⟨119445634673578608838457845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159260846231438145117943793 119445634673578608838457845)
  ·
    refine ⟨11198028250647994578605423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119445634673578608838457845 11198028250647994578605423)
    ·
      refine ⟨16797042375971991867908135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198028250647994578605423 16797042375971991867908135)
      ·
        refine ⟨25195563563957987801862203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16797042375971991867908135 25195563563957987801862203)
        ·
          refine ⟨37793345345936981702793305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25195563563957987801862203 37793345345936981702793305)
          ·
            refine ⟨28345009009452736277094979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37793345345936981702793305 28345009009452736277094979)
            ·
              refine ⟨42517513514179104415642469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28345009009452736277094979 42517513514179104415642469)
              ·
                refine ⟨7972033783908582077932963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42517513514179104415642469 7972033783908582077932963)
                ·
                  refine ⟨11958050675862873116899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972033783908582077932963 11958050675862873116899445)
                  ·
                    refine ⟨1121067250862144354709323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11958050675862873116899445 1121067250862144354709323)
                    ·
                      rfl

theorem cell23_6549812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_6549812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549812 prefixEnd_6549812 := by exact prefixLift 6549812
  have htrace : WordTrace (prefixWord ++ tailWord_6549812) baseStart_6549812 baseEnd_6549812 := by
    simpa [prefixWord, tailWord_6549812, baseEnd_6549812] using wordTrace_append hprefix tailTrace_6549812
  have hstable : (prefixWord ++ tailWord_6549812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549812).length < 2 ^ (prefixWord ++ tailWord_6549812).sum := by decide
  have hdescent : baseEnd_6549812 < baseStart_6549812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549832 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_6549832 : Nat := 118140960795 + 6549832 * 2 ^ 59
def prefixEnd_6549832 : Nat := 4983230072969 + 3 ^ 40 * 6549832 * 2
def baseEnd_6549832 : Nat := 3363212022199522985877877

theorem tailTrace_6549832 : CollatzResearch.WordTrace tailWord_6549832 prefixEnd_6549832 3363212022199522985877877 := by
  unfold tailWord_6549832
  simp only [CollatzResearch.WordTrace]
  refine ⟨119445999403542380546321875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159261332538056507395095833 119445999403542380546321875)
  ·
    refine ⟨179168999105313570819482813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119445999403542380546321875 179168999105313570819482813)
    ·
      refine ⟨67188374664492589057306055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179168999105313570819482813 67188374664492589057306055)
      ·
        refine ⟨100782561996738883585959083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67188374664492589057306055 100782561996738883585959083)
        ·
          refine ⟨151173842995108325378938625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100782561996738883585959083 151173842995108325378938625)
          ·
            refine ⟨113380382246331244034203969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151173842995108325378938625 113380382246331244034203969)
            ·
              refine ⟨85035286684748433025652977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113380382246331244034203969 85035286684748433025652977)
              ·
                refine ⟨63776465013561324769239733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85035286684748433025652977 63776465013561324769239733)
                ·
                  refine ⟨5979043595021374197116225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63776465013561324769239733 5979043595021374197116225)
                  ·
                    refine ⟨4484282696266030647837169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979043595021374197116225 4484282696266030647837169)
                    ·
                      refine ⟨3363212022199522985877877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484282696266030647837169 3363212022199522985877877)
                      ·
                        rfl

theorem cell23_6549832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_6549832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549832 prefixEnd_6549832 := by exact prefixLift 6549832
  have htrace : WordTrace (prefixWord ++ tailWord_6549832) baseStart_6549832 baseEnd_6549832 := by
    simpa [prefixWord, tailWord_6549832, baseEnd_6549832] using wordTrace_append hprefix tailTrace_6549832
  have hstable : (prefixWord ++ tailWord_6549832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549832).length < 2 ^ (prefixWord ++ tailWord_6549832).sum := by decide
  have hdescent : baseEnd_6549832 < baseStart_6549832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549865 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_6549865 : Nat := 118140960795 + 6549865 * 2 ^ 59
def prefixEnd_6549865 : Nat := 4983230072969 + 3 ^ 40 * 6549865 * 2
def baseEnd_6549865 : Nat := 3363228967061121356765225

theorem tailTrace_6549865 : CollatzResearch.WordTrace tailWord_6549865 prefixEnd_6549865 3363228967061121356765225 := by
  unfold tailWord_6549865
  simp only [CollatzResearch.WordTrace]
  refine ⟨238893202415965207728595049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159262134943976805152396699 238893202415965207728595049)
  ·
    refine ⟨179169901811973905796446287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238893202415965207728595049 179169901811973905796446287)
    ·
      refine ⟨268754852717960858694669431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179169901811973905796446287 268754852717960858694669431)
      ·
        refine ⟨403132279076941288042004147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268754852717960858694669431 403132279076941288042004147)
        ·
          refine ⟨604698418615411932063006221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403132279076941288042004147 604698418615411932063006221)
          ·
            refine ⟨226761906980779474523627333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604698418615411932063006221 226761906980779474523627333)
            ·
              refine ⟨42517857558896151473180125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226761906980779474523627333 42517857558896151473180125)
              ·
                refine ⟨15944196584586056802442547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42517857558896151473180125 15944196584586056802442547)
                ·
                  refine ⟨23916294876879085203663821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15944196584586056802442547 23916294876879085203663821)
                  ·
                    refine ⟨8968610578829656951373933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23916294876879085203663821 8968610578829656951373933)
                    ·
                      refine ⟨3363228967061121356765225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968610578829656951373933 3363228967061121356765225)
                      ·
                        rfl

theorem cell23_6549865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_6549865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549865 prefixEnd_6549865 := by exact prefixLift 6549865
  have htrace : WordTrace (prefixWord ++ tailWord_6549865) baseStart_6549865 baseEnd_6549865 := by
    simpa [prefixWord, tailWord_6549865, baseEnd_6549865] using wordTrace_append hprefix tailTrace_6549865
  have hstable : (prefixWord ++ tailWord_6549865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549865).length < 2 ^ (prefixWord ++ tailWord_6549865).sum := by decide
  have hdescent : baseEnd_6549865 < baseStart_6549865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549875 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 7, 2]
def baseStart_6549875 : Nat := 118140960795 + 6549875 * 2 ^ 59
def prefixEnd_6549875 : Nat := 4983230072969 + 3 ^ 40 * 6549875 * 2
def baseEnd_6549875 : Nat := 3363234101867666317640179

theorem tailTrace_6549875 : CollatzResearch.WordTrace tailWord_6549875 prefixEnd_6549875 3363234101867666317640179 := by
  unfold tailWord_6549875
  simp only [CollatzResearch.WordTrace]
  refine ⟨238893567145928979436459079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159262378097285986290972719 238893567145928979436459079)
  ·
    refine ⟨358340350718893469154688619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238893567145928979436459079 358340350718893469154688619)
    ·
      refine ⟨537510526078340203732032929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358340350718893469154688619 537510526078340203732032929)
      ·
        refine ⟨403132894558755152799024697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537510526078340203732032929 403132894558755152799024697)
        ·
          refine ⟨302349670919066364599268523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403132894558755152799024697 302349670919066364599268523)
          ·
            refine ⟨453524506378599546898902785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302349670919066364599268523 453524506378599546898902785)
            ·
              refine ⟨340143379783949660174177089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453524506378599546898902785 340143379783949660174177089)
              ·
                refine ⟨255107534837962245130632817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340143379783949660174177089 255107534837962245130632817)
                ·
                  refine ⟨191330651128471683847974613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255107534837962245130632817 191330651128471683847974613)
                  ·
                    refine ⟨4484312135823555090186905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191330651128471683847974613 4484312135823555090186905)
                    ·
                      refine ⟨3363234101867666317640179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484312135823555090186905 3363234101867666317640179)
                      ·
                        rfl

theorem cell23_6549875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7, 2].length) (baseStart_6549875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549875 prefixEnd_6549875 := by exact prefixLift 6549875
  have htrace : WordTrace (prefixWord ++ tailWord_6549875) baseStart_6549875 baseEnd_6549875 := by
    simpa [prefixWord, tailWord_6549875, baseEnd_6549875] using wordTrace_append hprefix tailTrace_6549875
  have hstable : (prefixWord ++ tailWord_6549875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549875).length < 2 ^ (prefixWord ++ tailWord_6549875).sum := by decide
  have hdescent : baseEnd_6549875 < baseStart_6549875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549899 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 3]
def baseStart_6549899 : Nat := 118140960795 + 6549899 * 2 ^ 59
def prefixEnd_6549899 : Nat := 4983230072969 + 3 ^ 40 * 6549899 * 2
def baseEnd_6549899 : Nat := 3363246425403374223740069

theorem tailTrace_6549899 : CollatzResearch.WordTrace tailWord_6549899 prefixEnd_6549899 3363246425403374223740069 := by
  unfold tailWord_6549899
  simp only [CollatzResearch.WordTrace]
  refine ⟨238894442497842031535332751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159262961665228021023555167 238894442497842031535332751)
  ·
    refine ⟨358341663746763047302999127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238894442497842031535332751 358341663746763047302999127)
    ·
      refine ⟨537512495620144570954498691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358341663746763047302999127 537512495620144570954498691)
      ·
        refine ⟨806268743430216856431748037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537512495620144570954498691 806268743430216856431748037)
        ·
          refine ⟨151175389393165660580952757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 806268743430216856431748037 151175389393165660580952757)
          ·
            refine ⟨14172692755609280679464321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151175389393165660580952757 14172692755609280679464321)
            ·
              refine ⟨10629519566706960509598241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14172692755609280679464321 10629519566706960509598241)
              ·
                refine ⟨7972139675030220382198681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10629519566706960509598241 7972139675030220382198681)
                ·
                  refine ⟨5979104756272665286649011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972139675030220382198681 5979104756272665286649011)
                  ·
                    refine ⟨8968657134408997929973517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979104756272665286649011 8968657134408997929973517)
                    ·
                      refine ⟨3363246425403374223740069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968657134408997929973517 3363246425403374223740069)
                      ·
                        rfl

theorem cell23_6549899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 1, 3].length) (baseStart_6549899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549899 prefixEnd_6549899 := by exact prefixLift 6549899
  have htrace : WordTrace (prefixWord ++ tailWord_6549899) baseStart_6549899 baseEnd_6549899 := by
    simpa [prefixWord, tailWord_6549899, baseEnd_6549899] using wordTrace_append hprefix tailTrace_6549899
  have hstable : (prefixWord ++ tailWord_6549899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549899).length < 2 ^ (prefixWord ++ tailWord_6549899).sum := by decide
  have hdescent : baseEnd_6549899 < baseStart_6549899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549925 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_6549925 : Nat := 118140960795 + 6549925 * 2 ^ 59
def prefixEnd_6549925 : Nat := 4983230072969 + 3 ^ 40 * 6549925 * 2
def baseEnd_6549925 : Nat := 3363259775900391122014949

theorem tailTrace_6549925 : CollatzResearch.WordTrace tailWord_6549925 prefixEnd_6549925 3363259775900391122014949 := by
  unfold tailWord_6549925
  simp only [CollatzResearch.WordTrace]
  refine ⟨238895390795747837975779229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159263593863831891983852819 238895390795747837975779229)
  ·
    refine ⟨89585771548405439240917211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238895390795747837975779229 89585771548405439240917211)
    ·
      refine ⟨134378657322608158861375817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89585771548405439240917211 134378657322608158861375817)
      ·
        refine ⟨100783992991956119146031863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134378657322608158861375817 100783992991956119146031863)
        ·
          refine ⟨151175989487934178719047795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100783992991956119146031863 151175989487934178719047795)
          ·
            refine ⟨226763984231901268078571693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151175989487934178719047795 226763984231901268078571693)
            ·
              refine ⟨85036494086962975529464385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226763984231901268078571693 85036494086962975529464385)
              ·
                refine ⟨63777370565222231647098289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85036494086962975529464385 63777370565222231647098289)
                ·
                  refine ⟨47833027923916673735323717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63777370565222231647098289 47833027923916673735323717)
                  ·
                    refine ⟨8968692735734376325373197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47833027923916673735323717 8968692735734376325373197)
                    ·
                      refine ⟨3363259775900391122014949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968692735734376325373197 3363259775900391122014949)
                      ·
                        rfl

theorem cell23_6549925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_6549925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549925 prefixEnd_6549925 := by exact prefixLift 6549925
  have htrace : WordTrace (prefixWord ++ tailWord_6549925) baseStart_6549925 baseEnd_6549925 := by
    simpa [prefixWord, tailWord_6549925, baseEnd_6549925] using wordTrace_append hprefix tailTrace_6549925
  have hstable : (prefixWord ++ tailWord_6549925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549925).length < 2 ^ (prefixWord ++ tailWord_6549925).sum := by decide
  have hdescent : baseEnd_6549925 < baseStart_6549925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549962 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_6549962 : Nat := 118140960795 + 6549962 * 2 ^ 59
def prefixEnd_6549962 : Nat := 4983230072969 + 3 ^ 40 * 6549962 * 2
def baseEnd_6549962 : Nat := 373697641631623053028031

theorem tailTrace_6549962 : CollatzResearch.WordTrace tailWord_6549962 prefixEnd_6549962 373697641631623053028031 := by
  unfold tailWord_6549962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59724185074153448323719035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159264493531075862196584093 59724185074153448323719035)
  ·
    refine ⟨89586277611230172485578553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59724185074153448323719035 89586277611230172485578553)
    ·
      refine ⟨67189708208422629364183915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89586277611230172485578553 67189708208422629364183915)
      ·
        refine ⟨100784562312633944046275873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67189708208422629364183915 100784562312633944046275873)
        ·
          refine ⟨75588421734475458034706905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100784562312633944046275873 75588421734475458034706905)
          ·
            refine ⟨56691316300856593526030179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75588421734475458034706905 56691316300856593526030179)
            ·
              refine ⟨85036974451284890289045269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56691316300856593526030179 85036974451284890289045269)
              ·
                refine ⟨3986108177403979232298997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85036974451284890289045269 3986108177403979232298997)
                ·
                  refine ⟨373697641631623053028031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986108177403979232298997 373697641631623053028031)
                  ·
                    rfl

theorem cell23_6549962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_6549962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549962 prefixEnd_6549962 := by exact prefixLift 6549962
  have htrace : WordTrace (prefixWord ++ tailWord_6549962) baseStart_6549962 baseEnd_6549962 := by
    simpa [prefixWord, tailWord_6549962, baseEnd_6549962] using wordTrace_append hprefix tailTrace_6549962
  have hstable : (prefixWord ++ tailWord_6549962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549962).length < 2 ^ (prefixWord ++ tailWord_6549962).sum := by decide
  have hdescent : baseEnd_6549962 < baseStart_6549962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549973 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6549973 : Nat := 118140960795 + 6549973 * 2 ^ 59
def prefixEnd_6549973 : Nat := 4983230072969 + 3 ^ 40 * 6549973 * 2
def baseEnd_6549973 : Nat := 3363284422971806934214729

theorem tailTrace_6549973 : CollatzResearch.WordTrace tailWord_6549973 prefixEnd_6549973 3363284422971806934214729 := by
  unfold tailWord_6549973
  simp only [CollatzResearch.WordTrace]
  refine ⟨238897141499573942173526573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159264760999715961449017715 238897141499573942173526573)
  ·
    refine ⟨89586428062340228315072465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238897141499573942173526573 89586428062340228315072465)
    ·
      refine ⟨67189821046755171236304349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89586428062340228315072465 67189821046755171236304349)
      ·
        refine ⟨25196182892533189213614131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67189821046755171236304349 25196182892533189213614131)
        ·
          refine ⟨37794274338799783820421197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25196182892533189213614131 37794274338799783820421197)
          ·
            refine ⟨14172852877049918932657949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37794274338799783820421197 14172852877049918932657949)
            ·
              refine ⟨5314819828893719599746731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14172852877049918932657949 5314819828893719599746731)
              ·
                refine ⟨7972229743340579399620097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314819828893719599746731 7972229743340579399620097)
                ·
                  refine ⟨5979172307505434549715073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972229743340579399620097 5979172307505434549715073)
                  ·
                    refine ⟨4484379230629075912286305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979172307505434549715073 4484379230629075912286305)
                    ·
                      refine ⟨3363284422971806934214729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484379230629075912286305 3363284422971806934214729)
                      ·
                        rfl

theorem cell23_6549973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6549973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549973 prefixEnd_6549973 := by exact prefixLift 6549973
  have htrace : WordTrace (prefixWord ++ tailWord_6549973) baseStart_6549973 baseEnd_6549973 := by
    simpa [prefixWord, tailWord_6549973, baseEnd_6549973] using wordTrace_append hprefix tailTrace_6549973
  have hstable : (prefixWord ++ tailWord_6549973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549973).length < 2 ^ (prefixWord ++ tailWord_6549973).sum := by decide
  have hdescent : baseEnd_6549973 < baseStart_6549973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549995 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_6549995 : Nat := 118140960795 + 6549995 * 2 ^ 59
def prefixEnd_6549995 : Nat := 4983230072969 + 3 ^ 40 * 6549995 * 2
def baseEnd_6549995 : Nat := 3363295719546205848139627

theorem tailTrace_6549995 : CollatzResearch.WordTrace tailWord_6549995 prefixEnd_6549995 3363295719546205848139627 := by
  unfold tailWord_6549995
  simp only [CollatzResearch.WordTrace]
  refine ⟨238897943905494239930827439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159265295936996159953884959 238897943905494239930827439)
  ·
    refine ⟨358346915858241359896241159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238897943905494239930827439 358346915858241359896241159)
    ·
      refine ⟨537520373787362039844361739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358346915858241359896241159 537520373787362039844361739)
      ·
        refine ⟨806280560681043059766542609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537520373787362039844361739 806280560681043059766542609)
        ·
          refine ⟨604710420510782294824906957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806280560681043059766542609 604710420510782294824906957)
          ·
            refine ⟨226766407691543360559340109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604710420510782294824906957 226766407691543360559340109)
            ·
              refine ⟨85037402884328760209752541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226766407691543360559340109 85037402884328760209752541)
              ·
                refine ⟨31889026081623285078657203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85037402884328760209752541 31889026081623285078657203)
                ·
                  refine ⟨47833539122434927617985805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31889026081623285078657203 47833539122434927617985805)
                  ·
                    refine ⟨17937577170913097856744677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47833539122434927617985805 17937577170913097856744677)
                    ·
                      refine ⟨3363295719546205848139627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17937577170913097856744677 3363295719546205848139627)
                      ·
                        rfl

theorem cell23_6549995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_6549995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549995 prefixEnd_6549995 := by exact prefixLift 6549995
  have htrace : WordTrace (prefixWord ++ tailWord_6549995) baseStart_6549995 baseEnd_6549995 := by
    simpa [prefixWord, tailWord_6549995, baseEnd_6549995] using wordTrace_append hprefix tailTrace_6549995
  have hstable : (prefixWord ++ tailWord_6549995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549995).length < 2 ^ (prefixWord ++ tailWord_6549995).sum := by decide
  have hdescent : baseEnd_6549995 < baseStart_6549995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550025 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_6550025 : Nat := 118140960795 + 6550025 * 2 ^ 59
def prefixEnd_6550025 : Nat := 4983230072969 + 3 ^ 40 * 6550025 * 2
def baseEnd_6550025 : Nat := 3363311123965840730764489

theorem tailTrace_6550025 : CollatzResearch.WordTrace tailWord_6550025 prefixEnd_6550025 3363311123965840730764489 := by
  unfold tailWord_6550025
  simp only [CollatzResearch.WordTrace]
  refine ⟨238899038095385555054419529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159266025396923703369613019 238899038095385555054419529)
  ·
    refine ⟨179174278571539166290814647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238899038095385555054419529 179174278571539166290814647)
    ·
      refine ⟨268761417857308749436221971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179174278571539166290814647 268761417857308749436221971)
      ·
        refine ⟨403142126785963124154332957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268761417857308749436221971 403142126785963124154332957)
        ·
          refine ⟨151178297544736171557874859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403142126785963124154332957 151178297544736171557874859)
          ·
            refine ⟨226767446317104257336812289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151178297544736171557874859 226767446317104257336812289)
            ·
              refine ⟨170075584737828193002609217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226767446317104257336812289 170075584737828193002609217)
              ·
                refine ⟨127556688553371144751956913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170075584737828193002609217 127556688553371144751956913)
                ·
                  refine ⟨95667516415028358563967685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127556688553371144751956913 95667516415028358563967685)
                  ·
                    refine ⟨17937659327817817230743941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95667516415028358563967685 17937659327817817230743941)
                    ·
                      refine ⟨3363311123965840730764489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17937659327817817230743941 3363311123965840730764489)
                      ·
                        rfl

theorem cell23_6550025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_6550025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550025 prefixEnd_6550025 := by exact prefixLift 6550025
  have htrace : WordTrace (prefixWord ++ tailWord_6550025) baseStart_6550025 baseEnd_6550025 := by
    simpa [prefixWord, tailWord_6550025, baseEnd_6550025] using wordTrace_append hprefix tailTrace_6550025
  have hstable : (prefixWord ++ tailWord_6550025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550025).length < 2 ^ (prefixWord ++ tailWord_6550025).sum := by decide
  have hdescent : baseEnd_6550025 < baseStart_6550025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550049 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6550049 : Nat := 118140960795 + 6550049 * 2 ^ 59
def prefixEnd_6550049 : Nat := 4983230072969 + 3 ^ 40 * 6550049 * 2
def baseEnd_6550049 : Nat := 3363323447501548636864379

theorem tailTrace_6550049 : CollatzResearch.WordTrace tailWord_6550049 prefixEnd_6550049 3363323447501548636864379 := by
  unfold tailWord_6550049
  simp only [CollatzResearch.WordTrace]
  refine ⟨238899913447298607153293201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159266608964865738102195467 238899913447298607153293201)
  ·
    refine ⟨179174935085473955364969901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238899913447298607153293201 179174935085473955364969901)
    ·
      refine ⟨67190600657052733261863713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179174935085473955364969901 67190600657052733261863713)
      ·
        refine ⟨50392950492789549946397785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67190600657052733261863713 50392950492789549946397785)
        ·
          refine ⟨37794712869592162459798339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50392950492789549946397785 37794712869592162459798339)
          ·
            refine ⟨56692069304388243689697509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37794712869592162459798339 56692069304388243689697509)
            ·
              refine ⟨10629762994572795691818283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56692069304388243689697509 10629762994572795691818283)
              ·
                refine ⟨15944644491859193537727425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629762994572795691818283 15944644491859193537727425)
                ·
                  refine ⟨11958483368894395153295569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15944644491859193537727425 11958483368894395153295569)
                  ·
                    refine ⟨8968862526670796364971677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11958483368894395153295569 8968862526670796364971677)
                    ·
                      refine ⟨3363323447501548636864379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968862526670796364971677 3363323447501548636864379)
                      ·
                        rfl

theorem cell23_6550049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6550049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550049 prefixEnd_6550049 := by exact prefixLift 6550049
  have htrace : WordTrace (prefixWord ++ tailWord_6550049) baseStart_6550049 baseEnd_6550049 := by
    simpa [prefixWord, tailWord_6550049, baseEnd_6550049] using wordTrace_append hprefix tailTrace_6550049
  have hstable : (prefixWord ++ tailWord_6550049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550049).length < 2 ^ (prefixWord ++ tailWord_6550049).sum := by decide
  have hdescent : baseEnd_6550049 < baseStart_6550049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550079 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_6550079 : Nat := 118140960795 + 6550079 * 2 ^ 59
def prefixEnd_6550079 : Nat := 4983230072969 + 3 ^ 40 * 6550079 * 2
def baseEnd_6550079 : Nat := 3363338851921183519489241

theorem tailTrace_6550079 : CollatzResearch.WordTrace tailWord_6550079 prefixEnd_6550079 3363338851921183519489241 := by
  unfold tailWord_6550079
  simp only [CollatzResearch.WordTrace]
  refine ⟨238901007637189922276885291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159267338424793281517923527 238901007637189922276885291)
  ·
    refine ⟨358351511455784883415327937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238901007637189922276885291 358351511455784883415327937)
    ·
      refine ⟨268763633591838662561495953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358351511455784883415327937 268763633591838662561495953)
      ·
        refine ⟨201572725193878996921121965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268763633591838662561495953 201572725193878996921121965)
        ·
          refine ⟨75589771947704623845420737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201572725193878996921121965 75589771947704623845420737)
          ·
            refine ⟨56692328960778467884065553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75589771947704623845420737 56692328960778467884065553)
            ·
              refine ⟨42519246720583850913049165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56692328960778467884065553 42519246720583850913049165)
              ·
                refine ⟨15944717520218944092393437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42519246720583850913049165 15944717520218944092393437)
                ·
                  refine ⟨5979269070082104034647539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15944717520218944092393437 5979269070082104034647539)
                  ·
                    refine ⟨8968903605123156051971309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979269070082104034647539 8968903605123156051971309)
                    ·
                      refine ⟨3363338851921183519489241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968903605123156051971309 3363338851921183519489241)
                      ·
                        rfl

theorem cell23_6550079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_6550079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550079 prefixEnd_6550079 := by exact prefixLift 6550079
  have htrace : WordTrace (prefixWord ++ tailWord_6550079) baseStart_6550079 baseEnd_6550079 := by
    simpa [prefixWord, tailWord_6550079, baseEnd_6550079] using wordTrace_append hprefix tailTrace_6550079
  have hstable : (prefixWord ++ tailWord_6550079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550079).length < 2 ^ (prefixWord ++ tailWord_6550079).sum := by decide
  have hdescent : baseEnd_6550079 < baseStart_6550079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550086 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_6550086 : Nat := 118140960795 + 6550086 * 2 ^ 59
def prefixEnd_6550086 : Nat := 4983230072969 + 3 ^ 40 * 6550086 * 2
def baseEnd_6550086 : Nat := 373704716253973888011301

theorem tailTrace_6550086 : CollatzResearch.WordTrace tailWord_6550086 prefixEnd_6550086 373704716253973888011301 := by
  unfold tailWord_6550086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465664467130142577262191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159267508632109708314926741 7465664467130142577262191)
  ·
    refine ⟨11198496700695213865893287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7465664467130142577262191 11198496700695213865893287)
    ·
      refine ⟨16797745051042820798839931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198496700695213865893287 16797745051042820798839931)
      ·
        refine ⟨25196617576564231198259897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16797745051042820798839931 25196617576564231198259897)
        ·
          refine ⟨18897463182423173398694923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25196617576564231198259897 18897463182423173398694923)
          ·
            refine ⟨28346194773634760098042385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18897463182423173398694923 28346194773634760098042385)
            ·
              refine ⟨21259646080226070073531789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28346194773634760098042385 21259646080226070073531789)
              ·
                refine ⟨7972367280084776277574421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21259646080226070073531789 7972367280084776277574421)
                ·
                  refine ⟨373704716253973888011301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7972367280084776277574421 373704716253973888011301)
                  ·
                    rfl

theorem cell23_6550086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_6550086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550086 prefixEnd_6550086 := by exact prefixLift 6550086
  have htrace : WordTrace (prefixWord ++ tailWord_6550086) baseStart_6550086 baseEnd_6550086 := by
    simpa [prefixWord, tailWord_6550086, baseEnd_6550086] using wordTrace_append hprefix tailTrace_6550086
  have hstable : (prefixWord ++ tailWord_6550086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550086).length < 2 ^ (prefixWord ++ tailWord_6550086).sum := by decide
  have hdescent : baseEnd_6550086 < baseStart_6550086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550112 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_6550112 : Nat := 118140960795 + 6550112 * 2 ^ 59
def prefixEnd_6550112 : Nat := 4983230072969 + 3 ^ 40 * 6550112 * 2
def baseEnd_6550112 : Nat := 1121118598927593963458863

theorem tailTrace_6550112 : CollatzResearch.WordTrace tailWord_6550112 prefixEnd_6550112 1121118598927593963458863 := by
  unfold tailWord_6550112
  simp only [CollatzResearch.WordTrace]
  refine ⟨119451105623035184456418295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159268140830713579275224393 119451105623035184456418295)
  ·
    refine ⟨179176658434552776684627443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119451105623035184456418295 179176658434552776684627443)
    ·
      refine ⟨268764987651829165026941165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179176658434552776684627443 268764987651829165026941165)
      ·
        refine ⟨100786870369435936885102937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268764987651829165026941165 100786870369435936885102937)
        ·
          refine ⟨75590152777076952663827203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100786870369435936885102937 75590152777076952663827203)
          ·
            refine ⟨113385229165615428995740805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75590152777076952663827203 113385229165615428995740805)
            ·
              refine ⟨21259730468552892936701401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113385229165615428995740805 21259730468552892936701401)
              ·
                refine ⟨15944797851414669702526051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21259730468552892936701401 15944797851414669702526051)
                ·
                  refine ⟨23917196777122004553789077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15944797851414669702526051 23917196777122004553789077)
                  ·
                    refine ⟨1121118598927593963458863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23917196777122004553789077 1121118598927593963458863)
                    ·
                      rfl

theorem cell23_6550112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_6550112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550112 prefixEnd_6550112 := by exact prefixLift 6550112
  have htrace : WordTrace (prefixWord ++ tailWord_6550112) baseStart_6550112 baseEnd_6550112 := by
    simpa [prefixWord, tailWord_6550112, baseEnd_6550112] using wordTrace_append hprefix tailTrace_6550112
  have hstable : (prefixWord ++ tailWord_6550112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550112).length < 2 ^ (prefixWord ++ tailWord_6550112).sum := by decide
  have hdescent : baseEnd_6550112 < baseStart_6550112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550113 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_6550113 : Nat := 118140960795 + 6550113 * 2 ^ 59
def prefixEnd_6550113 : Nat := 4983230072969 + 3 ^ 40 * 6550113 * 2
def baseEnd_6550113 : Nat := 3363356310263436386464085

theorem tailTrace_6550113 : CollatzResearch.WordTrace tailWord_6550113 prefixEnd_6550113 3363356310263436386464085 := by
  unfold tailWord_6550113
  simp only [CollatzResearch.WordTrace]
  refine ⟨238902247719066746083622993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159268165146044497389081995 238902247719066746083622993)
  ·
    refine ⟨179176685789300059562717245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238902247719066746083622993 179176685789300059562717245)
    ·
      refine ⟨67191257170987522336018967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179176685789300059562717245 67191257170987522336018967)
      ·
        refine ⟨100786885756481283504028451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67191257170987522336018967 100786885756481283504028451)
        ·
          refine ⟨151180328634721925256042677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100786885756481283504028451 151180328634721925256042677)
          ·
            refine ⟨14173155809505180492754001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151180328634721925256042677 14173155809505180492754001)
            ·
              refine ⟨10629866857128885369565501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14173155809505180492754001 10629866857128885369565501)
              ·
                refine ⟨3986200071423332013587063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10629866857128885369565501 3986200071423332013587063)
                ·
                  refine ⟨5979300107134998020380595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986200071423332013587063 5979300107134998020380595)
                  ·
                    refine ⟨8968950160702497030570893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979300107134998020380595 8968950160702497030570893)
                    ·
                      refine ⟨3363356310263436386464085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8968950160702497030570893 3363356310263436386464085)
                      ·
                        rfl

theorem cell23_6550113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_6550113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550113 prefixEnd_6550113 := by exact prefixLift 6550113
  have htrace : WordTrace (prefixWord ++ tailWord_6550113) baseStart_6550113 baseEnd_6550113 := by
    simpa [prefixWord, tailWord_6550113, baseEnd_6550113] using wordTrace_append hprefix tailTrace_6550113
  have hstable : (prefixWord ++ tailWord_6550113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550113).length < 2 ^ (prefixWord ++ tailWord_6550113).sum := by decide
  have hdescent : baseEnd_6550113 < baseStart_6550113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550149 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_6550149 : Nat := 118140960795 + 6550149 * 2 ^ 59
def prefixEnd_6550149 : Nat := 4983230072969 + 3 ^ 40 * 6550149 * 2
def baseEnd_6550149 : Nat := 3363374795566998245613919

theorem tailTrace_6550149 : CollatzResearch.WordTrace tailWord_6550149 prefixEnd_6550149 3363374795566998245613919 := by
  unfold tailWord_6550149
  simp only [CollatzResearch.WordTrace]
  refine ⟨238903560746936324231933501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159269040497957549487955667 238903560746936324231933501)
  ·
    refine ⟨89588835280101121586975063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238903560746936324231933501 89588835280101121586975063)
    ·
      refine ⟨134383252920151682380462595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89588835280101121586975063 134383252920151682380462595)
      ·
        refine ⟨201574879380227523570693893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134383252920151682380462595 201574879380227523570693893)
        ·
          refine ⟨37795289883792660669505105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201574879380227523570693893 37795289883792660669505105)
          ·
            refine ⟨28346467412844495502128829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37795289883792660669505105 28346467412844495502128829)
            ·
              refine ⟨10629925279816685813298311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28346467412844495502128829 10629925279816685813298311)
              ·
                refine ⟨15944887919725028719947467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629925279816685813298311 15944887919725028719947467)
                ·
                  refine ⟨23917331879587543079921201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15944887919725028719947467 23917331879587543079921201)
                  ·
                    refine ⟨17937998909690657309940901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23917331879587543079921201 17937998909690657309940901)
                    ·
                      refine ⟨3363374795566998245613919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17937998909690657309940901 3363374795566998245613919)
                      ·
                        rfl

theorem cell23_6550149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_6550149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550149 prefixEnd_6550149 := by exact prefixLift 6550149
  have htrace : WordTrace (prefixWord ++ tailWord_6550149) baseStart_6550149 baseEnd_6550149 := by
    simpa [prefixWord, tailWord_6550149, baseEnd_6550149] using wordTrace_append hprefix tailTrace_6550149
  have hstable : (prefixWord ++ tailWord_6550149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550149).length < 2 ^ (prefixWord ++ tailWord_6550149).sum := by decide
  have hdescent : baseEnd_6550149 < baseStart_6550149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550169 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_6550169 : Nat := 118140960795 + 6550169 * 2 ^ 59
def prefixEnd_6550169 : Nat := 4983230072969 + 3 ^ 40 * 6550169 * 2
def baseEnd_6550169 : Nat := 3363385065180088167363827

theorem tailTrace_6550169 : CollatzResearch.WordTrace tailWord_6550169 prefixEnd_6550169 3363385065180088167363827 := by
  unfold tailWord_6550169
  simp only [CollatzResearch.WordTrace]
  refine ⟨238904290206863867647661561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159269526804575911765107707 238904290206863867647661561)
  ·
    refine ⟨179178217655147900735746171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238904290206863867647661561 179178217655147900735746171)
    ·
      refine ⟨268767326482721851103619257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179178217655147900735746171 268767326482721851103619257)
      ·
        refine ⟨201575494862041388327714443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268767326482721851103619257 201575494862041388327714443)
        ·
          refine ⟨302363242293062082491571665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201575494862041388327714443 302363242293062082491571665)
          ·
            refine ⟨226772431719796561868678749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302363242293062082491571665 226772431719796561868678749)
            ·
              refine ⟨85039661894923710700754531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226772431719796561868678749 85039661894923710700754531)
              ·
                refine ⟨127559492842385566051131797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85039661894923710700754531 127559492842385566051131797)
                ·
                  refine ⟨5979351226986823408646803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127559492842385566051131797 5979351226986823408646803)
                  ·
                    refine ⟨8969026840480235112970205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979351226986823408646803 8969026840480235112970205)
                    ·
                      refine ⟨3363385065180088167363827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969026840480235112970205 3363385065180088167363827)
                      ·
                        rfl

theorem cell23_6550169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_6550169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550169 prefixEnd_6550169 := by exact prefixLift 6550169
  have htrace : WordTrace (prefixWord ++ tailWord_6550169) baseStart_6550169 baseEnd_6550169 := by
    simpa [prefixWord, tailWord_6550169, baseEnd_6550169] using wordTrace_append hprefix tailTrace_6550169
  have hstable : (prefixWord ++ tailWord_6550169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550169).length < 2 ^ (prefixWord ++ tailWord_6550169).sum := by decide
  have hdescent : baseEnd_6550169 < baseStart_6550169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550192 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_6550192 : Nat := 118140960795 + 6550192 * 2 ^ 59
def prefixEnd_6550192 : Nat := 4983230072969 + 3 ^ 40 * 6550192 * 2
def baseEnd_6550192 : Nat := 3363396875235141577376221

theorem tailTrace_6550192 : CollatzResearch.WordTrace tailWord_6550192 prefixEnd_6550192 3363396875235141577376221 := by
  unfold tailWord_6550192
  simp only [CollatzResearch.WordTrace]
  refine ⟨119452564542890271287874415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159270086057187028383832553 119452564542890271287874415)
  ·
    refine ⟨179178846814335406931811623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119452564542890271287874415 179178846814335406931811623)
    ·
      refine ⟨268768270221503110397717435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179178846814335406931811623 268768270221503110397717435)
      ·
        refine ⟨403152405332254665596576153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268768270221503110397717435 403152405332254665596576153)
        ·
          refine ⟨302364303999190999197432115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403152405332254665596576153 302364303999190999197432115)
          ·
            refine ⟨453546455998786498796148173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302364303999190999197432115 453546455998786498796148173)
            ·
              refine ⟨170079920999544937048555565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453546455998786498796148173 170079920999544937048555565)
              ·
                refine ⟨63779970374829351393208337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170079920999544937048555565 63779970374829351393208337)
                ·
                  refine ⟨47834977781122013544906253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63779970374829351393208337 47834977781122013544906253)
                  ·
                    refine ⟨17938116667920755079339845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47834977781122013544906253 17938116667920755079339845)
                    ·
                      refine ⟨3363396875235141577376221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17938116667920755079339845 3363396875235141577376221)
                      ·
                        rfl

theorem cell23_6550192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_6550192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550192 prefixEnd_6550192 := by exact prefixLift 6550192
  have htrace : WordTrace (prefixWord ++ tailWord_6550192) baseStart_6550192 baseEnd_6550192 := by
    simpa [prefixWord, tailWord_6550192, baseEnd_6550192] using wordTrace_append hprefix tailTrace_6550192
  have hstable : (prefixWord ++ tailWord_6550192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550192).length < 2 ^ (prefixWord ++ tailWord_6550192).sum := by decide
  have hdescent : baseEnd_6550192 < baseStart_6550192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550202 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_6550202 : Nat := 118140960795 + 6550202 * 2 ^ 59
def prefixEnd_6550202 : Nat := 4983230072969 + 3 ^ 40 * 6550202 * 2
def baseEnd_6550202 : Nat := 1121134003347228846083725

theorem tailTrace_6550202 : CollatzResearch.WordTrace tailWord_6550202 prefixEnd_6550202 1121134003347228846083725 := by
  unfold tailWord_6550202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59726373453936078570903215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159270329210496209522408573 59726373453936078570903215)
  ·
    refine ⟨89589560180904117856354823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59726373453936078570903215 89589560180904117856354823)
    ·
      refine ⟨134384340271356176784532235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89589560180904117856354823 134384340271356176784532235)
      ·
        refine ⟨201576510407034265176798353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134384340271356176784532235 201576510407034265176798353)
        ·
          refine ⟨151182382805275698882598765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201576510407034265176798353 151182382805275698882598765)
          ·
            refine ⟨56693393551978387080974537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151182382805275698882598765 56693393551978387080974537)
            ·
              refine ⟨42520045163983790310730903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56693393551978387080974537 42520045163983790310730903)
              ·
                refine ⟨63780067745975685466096355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42520045163983790310730903 63780067745975685466096355)
                ·
                  refine ⟨95670101618963528199144533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63780067745975685466096355 95670101618963528199144533)
                  ·
                    refine ⟨1121134003347228846083725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95670101618963528199144533 1121134003347228846083725)
                    ·
                      rfl

theorem cell23_6550202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_6550202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550202 prefixEnd_6550202 := by exact prefixLift 6550202
  have htrace : WordTrace (prefixWord ++ tailWord_6550202) baseStart_6550202 baseEnd_6550202 := by
    simpa [prefixWord, tailWord_6550202, baseEnd_6550202] using wordTrace_append hprefix tailTrace_6550202
  have hstable : (prefixWord ++ tailWord_6550202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550202).length < 2 ^ (prefixWord ++ tailWord_6550202).sum := by decide
  have hdescent : baseEnd_6550202 < baseStart_6550202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550252 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_6550252 : Nat := 118140960795 + 6550252 * 2 ^ 59
def prefixEnd_6550252 : Nat := 4983230072969 + 3 ^ 40 * 6550252 * 2
def baseEnd_6550252 : Nat := 3363427684074411342625945

theorem tailTrace_6550252 : CollatzResearch.WordTrace tailWord_6550252 prefixEnd_6550252 3363427684074411342625945 := by
  unfold tailWord_6550252
  simp only [CollatzResearch.WordTrace]
  refine ⟨119453658732781586411466505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159271544977042115215288673 119453658732781586411466505)
  ·
    refine ⟨89590244049586189808599879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119453658732781586411466505 89590244049586189808599879)
    ·
      refine ⟨134385366074379284712899819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89590244049586189808599879 134385366074379284712899819)
      ·
        refine ⟨201578049111568927069349729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134385366074379284712899819 201578049111568927069349729)
        ·
          refine ⟨151183536833676695302012297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201578049111568927069349729 151183536833676695302012297)
          ·
            refine ⟨113387652625257521476509223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151183536833676695302012297 113387652625257521476509223)
            ·
              refine ⟨170081478937886282214763835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113387652625257521476509223 170081478937886282214763835)
              ·
                refine ⟨255122218406829423322145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170081478937886282214763835 255122218406829423322145753)
                ·
                  refine ⟨191341663805122067491609315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255122218406829423322145753 191341663805122067491609315)
                  ·
                    refine ⟨287012495707683101237413973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191341663805122067491609315 287012495707683101237413973)
                    ·
                      refine ⟨3363427684074411342625945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287012495707683101237413973 3363427684074411342625945)
                      ·
                        rfl

theorem cell23_6550252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_6550252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550252 prefixEnd_6550252 := by exact prefixLift 6550252
  have htrace : WordTrace (prefixWord ++ tailWord_6550252) baseStart_6550252 baseEnd_6550252 := by
    simpa [prefixWord, tailWord_6550252, baseEnd_6550252] using wordTrace_append hprefix tailTrace_6550252
  have hstable : (prefixWord ++ tailWord_6550252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550252).length < 2 ^ (prefixWord ++ tailWord_6550252).sum := by decide
  have hdescent : baseEnd_6550252 < baseStart_6550252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550316 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_6550316 : Nat := 118140960795 + 6550316 * 2 ^ 59
def prefixEnd_6550316 : Nat := 4983230072969 + 3 ^ 40 * 6550316 * 2
def baseEnd_6550316 : Nat := 3363460546836299092225651

theorem tailTrace_6550316 : CollatzResearch.WordTrace tailWord_6550316 prefixEnd_6550316 3363460546836299092225651 := by
  unfold tailWord_6550316
  simp only [CollatzResearch.WordTrace]
  refine ⟨119454825868665655876631401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159273101158220874502175201 119454825868665655876631401)
  ·
    refine ⟨89591119401499241907473551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119454825868665655876631401 89591119401499241907473551)
    ·
      refine ⟨134386679102248862861210327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89591119401499241907473551 134386679102248862861210327)
      ·
        refine ⟨201580018653373294291815491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134386679102248862861210327 201580018653373294291815491)
        ·
          refine ⟨302370027980059941437723237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201580018653373294291815491 302370027980059941437723237)
          ·
            refine ⟨56694380246261239019573107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302370027980059941437723237 56694380246261239019573107)
            ·
              refine ⟨85041570369391858529359661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56694380246261239019573107 85041570369391858529359661)
              ·
                refine ⟨31890588888521946948509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85041570369391858529359661 31890588888521946948509873)
                ·
                  refine ⟨23917941666391460211382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31890588888521946948509873 23917941666391460211382405)
                  ·
                    refine ⟨4484614062448398789634201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23917941666391460211382405 4484614062448398789634201)
                    ·
                      refine ⟨3363460546836299092225651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484614062448398789634201 3363460546836299092225651)
                      ·
                        rfl

theorem cell23_6550316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_6550316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550316 prefixEnd_6550316 := by exact prefixLift 6550316
  have htrace : WordTrace (prefixWord ++ tailWord_6550316) baseStart_6550316 baseEnd_6550316 := by
    simpa [prefixWord, tailWord_6550316, baseEnd_6550316] using wordTrace_append hprefix tailTrace_6550316
  have hstable : (prefixWord ++ tailWord_6550316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550316).length < 2 ^ (prefixWord ++ tailWord_6550316).sum := by decide
  have hdescent : baseEnd_6550316 < baseStart_6550316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550353 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_6550353 : Nat := 118140960795 + 6550353 * 2 ^ 59
def prefixEnd_6550353 : Nat := 4983230072969 + 3 ^ 40 * 6550353 * 2
def baseEnd_6550353 : Nat := 3363479545620515447462981

theorem tailTrace_6550353 : CollatzResearch.WordTrace tailWord_6550353 prefixEnd_6550353 3363479545620515447462981 := by
  unfold tailWord_6550353
  simp only [CollatzResearch.WordTrace]
  refine ⟨238911001238197267072359713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159274000825464844714906475 238911001238197267072359713)
  ·
    refine ⟨179183250928647950304269785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238911001238197267072359713 179183250928647950304269785)
    ·
      refine ⟨134387438196485962728202339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179183250928647950304269785 134387438196485962728202339)
      ·
        refine ⟨201581157294728944092303509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134387438196485962728202339 201581157294728944092303509)
        ·
          refine ⟨9449116748190419254326727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201581157294728944092303509 9449116748190419254326727)
          ·
            refine ⟨14173675122285628881490091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449116748190419254326727 14173675122285628881490091)
            ·
              refine ⟨21260512683428443322235137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14173675122285628881490091 21260512683428443322235137)
              ·
                refine ⟨15945384512571332491676353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21260512683428443322235137 15945384512571332491676353)
                ·
                  refine ⟨11959038384428499368757265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15945384512571332491676353 11959038384428499368757265)
                  ·
                    refine ⟨8969278788321374526567949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11959038384428499368757265 8969278788321374526567949)
                    ·
                      refine ⟨3363479545620515447462981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969278788321374526567949 3363479545620515447462981)
                      ·
                        rfl

theorem cell23_6550353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_6550353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550353 prefixEnd_6550353 := by exact prefixLift 6550353
  have htrace : WordTrace (prefixWord ++ tailWord_6550353) baseStart_6550353 baseEnd_6550353 := by
    simpa [prefixWord, tailWord_6550353, baseEnd_6550353] using wordTrace_append hprefix tailTrace_6550353
  have hstable : (prefixWord ++ tailWord_6550353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550353).length < 2 ^ (prefixWord ++ tailWord_6550353).sum := by decide
  have hdescent : baseEnd_6550353 < baseStart_6550353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550393 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6550393 : Nat := 118140960795 + 6550393 * 2 ^ 59
def prefixEnd_6550393 : Nat := 4983230072969 + 3 ^ 40 * 6550393 * 2
def baseEnd_6550393 : Nat := 3363500084846695290962797

theorem tailTrace_6550393 : CollatzResearch.WordTrace tailWord_6550393 prefixEnd_6550393 3363500084846695290962797 := by
  unfold tailWord_6550393
  simp only [CollatzResearch.WordTrace]
  refine ⟨238912460158052353903815833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159274973438701569269210555 238912460158052353903815833)
  ·
    refine ⟨179184345118539265427861875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238912460158052353903815833 179184345118539265427861875)
    ·
      refine ⟨268776517677808898141792813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179184345118539265427861875 268776517677808898141792813)
      ·
        refine ⟨100791194129178336803172305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268776517677808898141792813 100791194129178336803172305)
        ·
          refine ⟨75593395596883752602379229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100791194129178336803172305 75593395596883752602379229)
          ·
            refine ⟨28347523348831407225892211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75593395596883752602379229 28347523348831407225892211)
            ·
              refine ⟨42521285023247110838838317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28347523348831407225892211 42521285023247110838838317)
              ·
                refine ⟨15945481883717666564564369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42521285023247110838838317 15945481883717666564564369)
                ·
                  refine ⟨11959111412788249923423277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15945481883717666564564369 11959111412788249923423277)
                  ·
                    refine ⟨4484666779795593721283729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11959111412788249923423277 4484666779795593721283729)
                    ·
                      refine ⟨3363500084846695290962797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484666779795593721283729 3363500084846695290962797)
                      ·
                        rfl

theorem cell23_6550393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6550393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550393 prefixEnd_6550393 := by exact prefixLift 6550393
  have htrace : WordTrace (prefixWord ++ tailWord_6550393) baseStart_6550393 baseEnd_6550393 := by
    simpa [prefixWord, tailWord_6550393, baseEnd_6550393] using wordTrace_append hprefix tailTrace_6550393
  have hstable : (prefixWord ++ tailWord_6550393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550393).length < 2 ^ (prefixWord ++ tailWord_6550393).sum := by decide
  have hdescent : baseEnd_6550393 < baseStart_6550393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550399 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 6]
def baseStart_6550399 : Nat := 118140960795 + 6550399 * 2 ^ 59
def prefixEnd_6550399 : Nat := 4983230072969 + 3 ^ 40 * 6550399 * 2
def baseEnd_6550399 : Nat := 1121167721910207422495923

theorem tailTrace_6550399 : CollatzResearch.WordTrace tailWord_6550399 prefixEnd_6550399 1121167721910207422495923 := by
  unfold tailWord_6550399
  simp only [CollatzResearch.WordTrace]
  refine ⟨238912678996030616928534251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159275119330687077952356167 238912678996030616928534251)
  ·
    refine ⟨358369018494045925392801377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238912678996030616928534251 358369018494045925392801377)
    ·
      refine ⟨268776763870534444044601033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358369018494045925392801377 268776763870534444044601033)
      ·
        refine ⟨201582572902900833033450775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268776763870534444044601033 201582572902900833033450775)
        ·
          refine ⟨302373859354351249550176163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201582572902900833033450775 302373859354351249550176163)
          ·
            refine ⟨453560789031526874325264245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302373859354351249550176163 453560789031526874325264245)
            ·
              refine ⟨42521323971705644467993523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 453560789031526874325264245 42521323971705644467993523)
              ·
                refine ⟨63781985957558466701990285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42521323971705644467993523 63781985957558466701990285)
                ·
                  refine ⟨23918244734084425013246357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63781985957558466701990285 23918244734084425013246357)
                  ·
                    refine ⟨1121167721910207422495923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23918244734084425013246357 1121167721910207422495923)
                    ·
                      rfl

theorem cell23_6550399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_6550399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550399 prefixEnd_6550399 := by exact prefixLift 6550399
  have htrace : WordTrace (prefixWord ++ tailWord_6550399) baseStart_6550399 baseEnd_6550399 := by
    simpa [prefixWord, tailWord_6550399, baseEnd_6550399] using wordTrace_append hprefix tailTrace_6550399
  have hstable : (prefixWord ++ tailWord_6550399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550399).length < 2 ^ (prefixWord ++ tailWord_6550399).sum := by decide
  have hdescent : baseEnd_6550399 < baseStart_6550399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550403 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 1, 5]
def baseStart_6550403 : Nat := 118140960795 + 6550403 * 2 ^ 59
def prefixEnd_6550403 : Nat := 4983230072969 + 3 ^ 40 * 6550403 * 2
def baseEnd_6550403 : Nat := 1121168406551080083945917

theorem tailTrace_6550403 : CollatzResearch.WordTrace tailWord_6550403 prefixEnd_6550403 1121168406551080083945917 := by
  unfold tailWord_6550403
  simp only [CollatzResearch.WordTrace]
  refine ⟨238912824888016125611679863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159275216592010750407786575 238912824888016125611679863)
  ·
    refine ⟨358369237332024188417519795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238912824888016125611679863 358369237332024188417519795)
    ·
      refine ⟨537553855998036282626279693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358369237332024188417519795 537553855998036282626279693)
      ·
        refine ⟨201582695999263605984854885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537553855998036282626279693 201582695999263605984854885)
        ·
          refine ⟨37796755499861926122160291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201582695999263605984854885 37796755499861926122160291)
          ·
            refine ⟨56695133249792889183240437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37796755499861926122160291 56695133249792889183240437)
            ·
              refine ⟨5315168742168083360928791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56695133249792889183240437 5315168742168083360928791)
              ·
                refine ⟨7972753113252125041393187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315168742168083360928791 7972753113252125041393187)
                ·
                  refine ⟨11959129669878187562089781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972753113252125041393187 11959129669878187562089781)
                  ·
                    refine ⟨1121168406551080083945917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11959129669878187562089781 1121168406551080083945917)
                    ·
                      rfl

theorem cell23_6550403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 5].length) (baseStart_6550403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550403 prefixEnd_6550403 := by exact prefixLift 6550403
  have htrace : WordTrace (prefixWord ++ tailWord_6550403) baseStart_6550403 baseEnd_6550403 := by
    simpa [prefixWord, tailWord_6550403, baseEnd_6550403] using wordTrace_append hprefix tailTrace_6550403
  have hstable : (prefixWord ++ tailWord_6550403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550403).length < 2 ^ (prefixWord ++ tailWord_6550403).sum := by decide
  have hdescent : baseEnd_6550403 < baseStart_6550403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550410 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6550410 : Nat := 118140960795 + 6550410 * 2 ^ 59
def prefixEnd_6550410 : Nat := 4983230072969 + 3 ^ 40 * 6550410 * 2
def baseEnd_6550410 : Nat := 3363508814017821724450219

theorem tailTrace_6550410 : CollatzResearch.WordTrace tailWord_6550410 prefixEnd_6550410 3363508814017821724450219 := by
  unfold tailWord_6550410
  simp only [CollatzResearch.WordTrace]
  refine ⟨59728270049747691451796171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159275386799327177204789789 59728270049747691451796171)
  ·
    refine ⟨89592405074621537177694257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59728270049747691451796171 89592405074621537177694257)
    ·
      refine ⟨67194303805966152883270693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89592405074621537177694257 67194303805966152883270693)
      ·
        refine ⟨12598931963618653665613255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67194303805966152883270693 12598931963618653665613255)
        ·
          refine ⟨18898397945427980498419883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598931963618653665613255 18898397945427980498419883)
          ·
            refine ⟨28347596918141970747629825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18898397945427980498419883 28347596918141970747629825)
            ·
              refine ⟨21260697688606478060722369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28347596918141970747629825 21260697688606478060722369)
              ·
                refine ⟨15945523266454858545541777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21260697688606478060722369 15945523266454858545541777)
                ·
                  refine ⟨11959142449841143909156333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15945523266454858545541777 11959142449841143909156333)
                  ·
                    refine ⟨4484678418690428965933625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11959142449841143909156333 4484678418690428965933625)
                    ·
                      refine ⟨3363508814017821724450219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484678418690428965933625 3363508814017821724450219)
                      ·
                        rfl

theorem cell23_6550410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6550410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550410 prefixEnd_6550410 := by exact prefixLift 6550410
  have htrace : WordTrace (prefixWord ++ tailWord_6550410) baseStart_6550410 baseEnd_6550410 := by
    simpa [prefixWord, tailWord_6550410, baseEnd_6550410] using wordTrace_append hprefix tailTrace_6550410
  have hstable : (prefixWord ++ tailWord_6550410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550410).length < 2 ^ (prefixWord ++ tailWord_6550410).sum := by decide
  have hdescent : baseEnd_6550410 < baseStart_6550410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_6550419 : Nat := 118140960795 + 6550419 * 2 ^ 59
def prefixEnd_6550419 : Nat := 4983230072969 + 3 ^ 40 * 6550419 * 2
def baseEnd_6550419 : Nat := 3363513435343712189237677

theorem tailTrace_6550419 : CollatzResearch.WordTrace tailWord_6550419 prefixEnd_6550419 3363513435343712189237677 := by
  unfold tailWord_6550419
  simp only [CollatzResearch.WordTrace]
  refine ⟨238913408455958160344262311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159275605637305440229508207 238913408455958160344262311)
  ·
    refine ⟨358370112683937240516393467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238913408455958160344262311 358370112683937240516393467)
    ·
      refine ⟨537555169025905860774590201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358370112683937240516393467 537555169025905860774590201)
      ·
        refine ⟨403166376769429395580942651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537555169025905860774590201 403166376769429395580942651)
        ·
          refine ⟨604749565154144093371413977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403166376769429395580942651 604749565154144093371413977)
          ·
            refine ⟨453562173865608070028560483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604749565154144093371413977 453562173865608070028560483)
            ·
              refine ⟨680343260798412105042840725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453562173865608070028560483 680343260798412105042840725)
              ·
                refine ⟨31891090349925567423883159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 680343260798412105042840725 31891090349925567423883159)
                ·
                  refine ⟨47836635524888351135824739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31891090349925567423883159 47836635524888351135824739)
                  ·
                    refine ⟨71754953287332526703737109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47836635524888351135824739 71754953287332526703737109)
                    ·
                      refine ⟨3363513435343712189237677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71754953287332526703737109 3363513435343712189237677)
                      ·
                        rfl

theorem cell23_6550419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_6550419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550419 prefixEnd_6550419 := by exact prefixLift 6550419
  have htrace : WordTrace (prefixWord ++ tailWord_6550419) baseStart_6550419 baseEnd_6550419 := by
    simpa [prefixWord, tailWord_6550419, baseEnd_6550419] using wordTrace_append hprefix tailTrace_6550419
  have hstable : (prefixWord ++ tailWord_6550419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550419).length < 2 ^ (prefixWord ++ tailWord_6550419).sum := by decide
  have hdescent : baseEnd_6550419 < baseStart_6550419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550433 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_6550433 : Nat := 118140960795 + 6550433 * 2 ^ 59
def prefixEnd_6550433 : Nat := 4983230072969 + 3 ^ 40 * 6550433 * 2
def baseEnd_6550433 : Nat := 1121173541357625044820871

theorem tailTrace_6550433 : CollatzResearch.WordTrace tailWord_6550433 prefixEnd_6550433 1121173541357625044820871 := by
  unfold tailWord_6550433
  simp only [CollatzResearch.WordTrace]
  refine ⟨238913919077907440735271953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159275946051938293823514635 238913919077907440735271953)
  ·
    refine ⟨179185439308430580551453965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238913919077907440735271953 179185439308430580551453965)
    ·
      refine ⟨67194539740661467706795237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179185439308430580551453965 67194539740661467706795237)
      ·
        refine ⟨12598976201374025195024107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67194539740661467706795237 12598976201374025195024107)
        ·
          refine ⟨18898464302061037792536161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598976201374025195024107 18898464302061037792536161)
          ·
            refine ⟨14173848226545778344402121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18898464302061037792536161 14173848226545778344402121)
            ·
              refine ⟨10630386169909333758301591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14173848226545778344402121 10630386169909333758301591)
              ·
                refine ⟨15945579254864000637452387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10630386169909333758301591 15945579254864000637452387)
                ·
                  refine ⟨23918368882296000956178581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15945579254864000637452387 23918368882296000956178581)
                  ·
                    refine ⟨1121173541357625044820871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23918368882296000956178581 1121173541357625044820871)
                    ·
                      rfl

theorem cell23_6550433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_6550433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550433 prefixEnd_6550433 := by exact prefixLift 6550433
  have htrace : WordTrace (prefixWord ++ tailWord_6550433) baseStart_6550433 baseEnd_6550433 := by
    simpa [prefixWord, tailWord_6550433, baseEnd_6550433] using wordTrace_append hprefix tailTrace_6550433
  have hstable : (prefixWord ++ tailWord_6550433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550433).length < 2 ^ (prefixWord ++ tailWord_6550433).sum := by decide
  have hdescent : baseEnd_6550433 < baseStart_6550433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550454 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6550454 : Nat := 118140960795 + 6550454 * 2 ^ 59
def prefixEnd_6550454 : Nat := 4983230072969 + 3 ^ 40 * 6550454 * 2
def baseEnd_6550454 : Nat := 1121177135722206517433339

theorem tailTrace_6550454 : CollatzResearch.WordTrace tailWord_6550454 prefixEnd_6550454 1121177135722206517433339 := by
  unfold tailWord_6550454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932167813176960082611651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159276456673887574214524277 14932167813176960082611651)
  ·
    refine ⟨22398251719765440123917477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14932167813176960082611651 22398251719765440123917477)
    ·
      refine ⟨4199672197456020023234527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22398251719765440123917477 4199672197456020023234527)
      ·
        refine ⟨6299508296184030034851791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199672197456020023234527 6299508296184030034851791)
        ·
          refine ⟨9449262444276045052277687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299508296184030034851791 9449262444276045052277687)
          ·
            refine ⟨14173893666414067578416531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449262444276045052277687 14173893666414067578416531)
            ·
              refine ⟨21260840499621101367624797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14173893666414067578416531 21260840499621101367624797)
              ·
                refine ⟨7972815187357913012859299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21260840499621101367624797 7972815187357913012859299)
                ·
                  refine ⟨11959222781036869519288949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7972815187357913012859299 11959222781036869519288949)
                  ·
                    refine ⟨1121177135722206517433339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11959222781036869519288949 1121177135722206517433339)
                    ·
                      rfl

theorem cell23_6550454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6550454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550454 prefixEnd_6550454 := by exact prefixLift 6550454
  have htrace : WordTrace (prefixWord ++ tailWord_6550454) baseStart_6550454 baseEnd_6550454 := by
    simpa [prefixWord, tailWord_6550454, baseEnd_6550454] using wordTrace_append hprefix tailTrace_6550454
  have hstable : (prefixWord ++ tailWord_6550454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550454).length < 2 ^ (prefixWord ++ tailWord_6550454).sum := by decide
  have hdescent : baseEnd_6550454 < baseStart_6550454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550457 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6550457 : Nat := 118140960795 + 6550457 * 2 ^ 59
def prefixEnd_6550457 : Nat := 4983230072969 + 3 ^ 40 * 6550457 * 2
def baseEnd_6550457 : Nat := 3363532947608583040562503

theorem tailTrace_6550457 : CollatzResearch.WordTrace tailWord_6550457 prefixEnd_6550457 3363532947608583040562503 := by
  unfold tailWord_6550457
  simp only [CollatzResearch.WordTrace]
  refine ⟨238914794429820492834145625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159276529619880328556097083 238914794429820492834145625)
  ·
    refine ⟨179186095822365369625609219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238914794429820492834145625 179186095822365369625609219)
    ·
      refine ⟨268779143733548054438413829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179186095822365369625609219 268779143733548054438413829)
      ·
        refine ⟨50396089450040260207202593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268779143733548054438413829 50396089450040260207202593)
        ·
          refine ⟨37797067087530195155401945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50396089450040260207202593 37797067087530195155401945)
          ·
            refine ⟨28347800315647646366551459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37797067087530195155401945 28347800315647646366551459)
            ·
              refine ⟨42521700473471469549827189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28347800315647646366551459 42521700473471469549827189)
              ·
                refine ⟨3986409419387950270296299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42521700473471469549827189 3986409419387950270296299)
                ·
                  refine ⟨5979614129081925405444449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986409419387950270296299 5979614129081925405444449)
                  ·
                    refine ⟨4484710596811444054083337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979614129081925405444449 4484710596811444054083337)
                    ·
                      refine ⟨3363532947608583040562503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484710596811444054083337 3363532947608583040562503)
                      ·
                        rfl

theorem cell23_6550457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6550457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550457 prefixEnd_6550457 := by exact prefixLift 6550457
  have htrace : WordTrace (prefixWord ++ tailWord_6550457) baseStart_6550457 baseEnd_6550457 := by
    simpa [prefixWord, tailWord_6550457, baseEnd_6550457] using wordTrace_append hprefix tailTrace_6550457
  have hstable : (prefixWord ++ tailWord_6550457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550457).length < 2 ^ (prefixWord ++ tailWord_6550457).sum := by decide
  have hdescent : baseEnd_6550457 < baseStart_6550457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550490 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_6550490 : Nat := 118140960795 + 6550490 * 2 ^ 59
def prefixEnd_6550490 : Nat := 4983230072969 + 3 ^ 40 * 6550490 * 2
def baseEnd_6550490 : Nat := 3363549892470181411449851

theorem tailTrace_6550490 : CollatzResearch.WordTrace tailWord_6550490 prefixEnd_6550490 3363549892470181411449851 := by
  unfold tailWord_6550490
  simp only [CollatzResearch.WordTrace]
  refine ⟨59728999509675234867524231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159277332025800626313397949 59728999509675234867524231)
  ·
    refine ⟨89593499264512852301286347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59728999509675234867524231 89593499264512852301286347)
    ·
      refine ⟨134390248896769278451929521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89593499264512852301286347 134390248896769278451929521)
      ·
        refine ⟨100792686672576958838947141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134390248896769278451929521 100792686672576958838947141)
        ·
          refine ⟨18898628751108179782302589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100792686672576958838947141 18898628751108179782302589)
          ·
            refine ⟨7086985781665567418363471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18898628751108179782302589 7086985781665567418363471)
            ·
              refine ⟨10630478672498351127545207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086985781665567418363471 10630478672498351127545207)
              ·
                refine ⟨15945718008747526691317811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10630478672498351127545207 15945718008747526691317811)
                ·
                  refine ⟨23918577013121290036976717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15945718008747526691317811 23918577013121290036976717)
                  ·
                    refine ⟨8969466379920483763866269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23918577013121290036976717 8969466379920483763866269)
                    ·
                      refine ⟨3363549892470181411449851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969466379920483763866269 3363549892470181411449851)
                      ·
                        rfl

theorem cell23_6550490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_6550490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550490 prefixEnd_6550490 := by exact prefixLift 6550490
  have htrace : WordTrace (prefixWord ++ tailWord_6550490) baseStart_6550490 baseEnd_6550490 := by
    simpa [prefixWord, tailWord_6550490, baseEnd_6550490] using wordTrace_append hprefix tailTrace_6550490
  have hstable : (prefixWord ++ tailWord_6550490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550490).length < 2 ^ (prefixWord ++ tailWord_6550490).sum := by decide
  have hdescent : baseEnd_6550490 < baseStart_6550490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550576 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_6550576 : Nat := 118140960795 + 6550576 * 2 ^ 59
def prefixEnd_6550576 : Nat := 4983230072969 + 3 ^ 40 * 6550576 * 2
def baseEnd_6550576 : Nat := 3363594051806468074974455

theorem tailTrace_6550576 : CollatzResearch.WordTrace tailWord_6550576 prefixEnd_6550576 3363594051806468074974455 := by
  unfold tailWord_6550576
  simp only [CollatzResearch.WordTrace]
  refine ⟨119459567358194688078863791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159279423144259584105151721 119459567358194688078863791)
  ·
    refine ⟨179189351037292032118295687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119459567358194688078863791 179189351037292032118295687)
    ·
      refine ⟨268784026555938048177443531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179189351037292032118295687 268784026555938048177443531)
      ·
        refine ⟨403176039833907072266165297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268784026555938048177443531 403176039833907072266165297)
        ·
          refine ⟨302382029875430304199623973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403176039833907072266165297 302382029875430304199623973)
          ·
            refine ⟨56696630601643182037429495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302382029875430304199623973 56696630601643182037429495)
            ·
              refine ⟨85044945902464773056144243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56696630601643182037429495 85044945902464773056144243)
              ·
                refine ⟨127567418853697159584216365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85044945902464773056144243 127567418853697159584216365)
                ·
                  refine ⟨47837782070136434844081137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127567418853697159584216365 47837782070136434844081137)
                  ·
                    refine ⟨35878336552602326133060853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47837782070136434844081137 35878336552602326133060853)
                    ·
                      refine ⟨3363594051806468074974455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35878336552602326133060853 3363594051806468074974455)
                      ·
                        rfl

theorem cell23_6550576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_6550576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550576 prefixEnd_6550576 := by exact prefixLift 6550576
  have htrace : WordTrace (prefixWord ++ tailWord_6550576) baseStart_6550576 baseEnd_6550576 := by
    simpa [prefixWord, tailWord_6550576, baseEnd_6550576] using wordTrace_append hprefix tailTrace_6550576
  have hstable : (prefixWord ++ tailWord_6550576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550576).length < 2 ^ (prefixWord ++ tailWord_6550576).sum := by decide
  have hdescent : baseEnd_6550576 < baseStart_6550576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550620 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6550620 : Nat := 118140960795 + 6550620 * 2 ^ 59
def prefixEnd_6550620 : Nat := 4983230072969 + 3 ^ 40 * 6550620 * 2
def baseEnd_6550620 : Nat := 3363616644955265902824253

theorem tailTrace_6550620 : CollatzResearch.WordTrace tailWord_6550620 prefixEnd_6550620 3363616644955265902824253 := by
  unfold tailWord_6550620
  simp only [CollatzResearch.WordTrace]
  refine ⟨119460369764114985836164657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159280493018819981114886209 119460369764114985836164657)
  ·
    refine ⟨89595277323086239377123493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119460369764114985836164657 89595277323086239377123493)
    ·
      refine ⟨16799114498078669883210655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89595277323086239377123493 16799114498078669883210655)
      ·
        refine ⟨25198671747118004824815983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16799114498078669883210655 25198671747118004824815983)
        ·
          refine ⟨37798007620677007237223975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25198671747118004824815983 37798007620677007237223975)
          ·
            refine ⟨56697011431015510855835963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37798007620677007237223975 56697011431015510855835963)
            ·
              refine ⟨85045517146523266283753945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56697011431015510855835963 85045517146523266283753945)
              ·
                refine ⟨63784137859892449712815459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85045517146523266283753945 63784137859892449712815459)
                ·
                  refine ⟨95676206789838674569223189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63784137859892449712815459 95676206789838674569223189)
                  ·
                    refine ⟨4484822193273687870432337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95676206789838674569223189 4484822193273687870432337)
                    ·
                      refine ⟨3363616644955265902824253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484822193273687870432337 3363616644955265902824253)
                      ·
                        rfl

theorem cell23_6550620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6550620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550620 prefixEnd_6550620 := by exact prefixLift 6550620
  have htrace : WordTrace (prefixWord ++ tailWord_6550620) baseStart_6550620 baseEnd_6550620 := by
    simpa [prefixWord, tailWord_6550620, baseEnd_6550620] using wordTrace_append hprefix tailTrace_6550620
  have hstable : (prefixWord ++ tailWord_6550620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550620).length < 2 ^ (prefixWord ++ tailWord_6550620).sum := by decide
  have hdescent : baseEnd_6550620 < baseStart_6550620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550623 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_6550623 : Nat := 118140960795 + 6550623 * 2 ^ 59
def prefixEnd_6550623 : Nat := 4983230072969 + 3 ^ 40 * 6550623 * 2
def baseEnd_6550623 : Nat := 3363618185397229391086739

theorem tailTrace_6550623 : CollatzResearch.WordTrace tailWord_6550623 prefixEnd_6550623 3363618185397229391086739 := by
  unfold tailWord_6550623
  simp only [CollatzResearch.WordTrace]
  refine ⟨238920848947219103184688523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159280565964812735456459015 238920848947219103184688523)
  ·
    refine ⟨358381273420828654777032785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238920848947219103184688523 358381273420828654777032785)
    ·
      refine ⟨268785955065621491082774589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358381273420828654777032785 268785955065621491082774589)
      ·
        refine ⟨100794733149608059156040471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268785955065621491082774589 100794733149608059156040471)
        ·
          refine ⟨151192099724412088734060707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100794733149608059156040471 151192099724412088734060707)
          ·
            refine ⟨226788149586618133101091061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151192099724412088734060707 226788149586618133101091061)
            ·
              refine ⟨21261389023745449978227287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226788149586618133101091061 21261389023745449978227287)
              ·
                refine ⟨31892083535618174967340931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21261389023745449978227287 31892083535618174967340931)
                ·
                  refine ⟨47838125303427262451011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31892083535618174967340931 47838125303427262451011397)
                  ·
                    refine ⟨8969648494392611709564637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47838125303427262451011397 8969648494392611709564637)
                    ·
                      refine ⟨3363618185397229391086739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969648494392611709564637 3363618185397229391086739)
                      ·
                        rfl

theorem cell23_6550623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_6550623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550623 prefixEnd_6550623 := by exact prefixLift 6550623
  have htrace : WordTrace (prefixWord ++ tailWord_6550623) baseStart_6550623 baseEnd_6550623 := by
    simpa [prefixWord, tailWord_6550623, baseEnd_6550623] using wordTrace_append hprefix tailTrace_6550623
  have hstable : (prefixWord ++ tailWord_6550623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550623).length < 2 ^ (prefixWord ++ tailWord_6550623).sum := by decide
  have hdescent : baseEnd_6550623 < baseStart_6550623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550724 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6550724 : Nat := 118140960795 + 6550724 * 2 ^ 59
def prefixEnd_6550724 : Nat := 4983230072969 + 3 ^ 40 * 6550724 * 2
def baseEnd_6550724 : Nat := 1121223348981111165307925

theorem tailTrace_6550724 : CollatzResearch.WordTrace tailWord_6550724 prefixEnd_6550724 1121223348981111165307925 := by
  unfold tailWord_6550724
  simp only [CollatzResearch.WordTrace]
  refine ⟨119462266359926598717057613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159283021813235464956076817 119462266359926598717057613)
  ·
    refine ⟨44798349884972474518896605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119462266359926598717057613 44798349884972474518896605)
    ·
      refine ⟨16799381206864677944586227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44798349884972474518896605 16799381206864677944586227)
      ·
        refine ⟨25199071810297016916879341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16799381206864677944586227 25199071810297016916879341)
        ·
          refine ⟨9449651928861381343829753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25199071810297016916879341 9449651928861381343829753)
          ·
            refine ⟨7087238946646036007872315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9449651928861381343829753 7087238946646036007872315)
            ·
              refine ⟨10630858419969054011808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087238946646036007872315 10630858419969054011808473)
              ·
                refine ⟨7973143814976790508856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10630858419969054011808473 7973143814976790508856355)
                ·
                  refine ⟨11959715722465185763284533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973143814976790508856355 11959715722465185763284533)
                  ·
                    refine ⟨1121223348981111165307925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11959715722465185763284533 1121223348981111165307925)
                    ·
                      rfl

theorem cell23_6550724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6550724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550724 prefixEnd_6550724 := by exact prefixLift 6550724
  have htrace : WordTrace (prefixWord ++ tailWord_6550724) baseStart_6550724 baseEnd_6550724 := by
    simpa [prefixWord, tailWord_6550724, baseEnd_6550724] using wordTrace_append hprefix tailTrace_6550724
  have hstable : (prefixWord ++ tailWord_6550724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550724).length < 2 ^ (prefixWord ++ tailWord_6550724).sum := by decide
  have hdescent : baseEnd_6550724 < baseStart_6550724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550727 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_6550727 : Nat := 118140960795 + 6550727 * 2 ^ 59
def prefixEnd_6550727 : Nat := 4983230072969 + 3 ^ 40 * 6550727 * 2
def baseEnd_6550727 : Nat := 3363671587385296984186261

theorem tailTrace_6550727 : CollatzResearch.WordTrace tailWord_6550727 prefixEnd_6550727 3363671587385296984186261 := by
  unfold tailWord_6550727
  simp only [CollatzResearch.WordTrace]
  refine ⟨238924642138842328946474435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159283094759228219297649623 238924642138842328946474435)
  ·
    refine ⟨358386963208263493419711653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238924642138842328946474435 358386963208263493419711653)
    ·
      refine ⟨67197555601549405016195935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358386963208263493419711653 67197555601549405016195935)
      ·
        refine ⟨100796333402324107524293903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67197555601549405016195935 100796333402324107524293903)
        ·
          refine ⟨151194500103486161286440855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100796333402324107524293903 151194500103486161286440855)
          ·
            refine ⟨226791750155229241929661283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151194500103486161286440855 226791750155229241929661283)
            ·
              refine ⟨340187625232843862894491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226791750155229241929661283 340187625232843862894491925)
              ·
                refine ⟨15946294932789556073179309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340187625232843862894491925 15946294932789556073179309)
                ·
                  refine ⟨5979860599796083527442241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15946294932789556073179309 5979860599796083527442241)
                  ·
                    refine ⟨4484895449847062645581681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979860599796083527442241 4484895449847062645581681)
                    ·
                      refine ⟨3363671587385296984186261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484895449847062645581681 3363671587385296984186261)
                      ·
                        rfl

theorem cell23_6550727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_6550727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550727 prefixEnd_6550727 := by exact prefixLift 6550727
  have htrace : WordTrace (prefixWord ++ tailWord_6550727) baseStart_6550727 baseEnd_6550727 := by
    simpa [prefixWord, tailWord_6550727, baseEnd_6550727] using wordTrace_append hprefix tailTrace_6550727
  have hstable : (prefixWord ++ tailWord_6550727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550727).length < 2 ^ (prefixWord ++ tailWord_6550727).sum := by decide
  have hdescent : baseEnd_6550727 < baseStart_6550727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550744 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_6550744 : Nat := 118140960795 + 6550744 * 2 ^ 59
def prefixEnd_6550744 : Nat := 4983230072969 + 3 ^ 40 * 6550744 * 2
def baseEnd_6550744 : Nat := 3363680316556423417673683

theorem tailTrace_6550744 : CollatzResearch.WordTrace tailWord_6550744 prefixEnd_6550744 3363680316556423417673683 := by
  unfold tailWord_6550744
  simp only [CollatzResearch.WordTrace]
  refine ⟨119462631089890370424921643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159283508119853827233228857 119462631089890370424921643)
  ·
    refine ⟨179193946634835555637382465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119462631089890370424921643 179193946634835555637382465)
    ·
      refine ⟨134395459976126666728036849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179193946634835555637382465 134395459976126666728036849)
      ·
        refine ⟨100796594982095000046027637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134395459976126666728036849 100796594982095000046027637)
        ·
          refine ⟨9449680779571406254315091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100796594982095000046027637 9449680779571406254315091)
          ·
            refine ⟨14174521169357109381472637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449680779571406254315091 14174521169357109381472637)
            ·
              refine ⟨5315445438508916018052239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14174521169357109381472637 5315445438508916018052239)
              ·
                refine ⟨7973168157763374027078359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315445438508916018052239 7973168157763374027078359)
                ·
                  refine ⟨11959752236645061040617539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973168157763374027078359 11959752236645061040617539)
                  ·
                    refine ⟨17939628354967591560926309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11959752236645061040617539 17939628354967591560926309)
                    ·
                      refine ⟨3363680316556423417673683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17939628354967591560926309 3363680316556423417673683)
                      ·
                        rfl

theorem cell23_6550744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_6550744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550744 prefixEnd_6550744 := by exact prefixLift 6550744
  have htrace : WordTrace (prefixWord ++ tailWord_6550744) baseStart_6550744 baseEnd_6550744 := by
    simpa [prefixWord, tailWord_6550744, baseEnd_6550744] using wordTrace_append hprefix tailTrace_6550744
  have hstable : (prefixWord ++ tailWord_6550744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550744).length < 2 ^ (prefixWord ++ tailWord_6550744).sum := by decide
  have hdescent : baseEnd_6550744 < baseStart_6550744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550760 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6550760 : Nat := 118140960795 + 6550760 * 2 ^ 59
def prefixEnd_6550760 : Nat := 4983230072969 + 3 ^ 40 * 6550760 * 2
def baseEnd_6550760 : Nat := 3363688532246895355073609

theorem tailTrace_6550760 : CollatzResearch.WordTrace tailWord_6550760 prefixEnd_6550760 3363688532246895355073609 := by
  unfold tailWord_6550760
  simp only [CollatzResearch.WordTrace]
  refine ⟨119462922873861387791212867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159283897165148517054950489 119462922873861387791212867)
  ·
    refine ⟨179194384310792081686819301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119462922873861387791212867 179194384310792081686819301)
    ·
      refine ⟨33598947058273515316278619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179194384310792081686819301 33598947058273515316278619)
      ·
        refine ⟨50398420587410272974417929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33598947058273515316278619 50398420587410272974417929)
        ·
          refine ⟨37798815440557704730813447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50398420587410272974417929 37798815440557704730813447)
          ·
            refine ⟨56698223160836557096220171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37798815440557704730813447 56698223160836557096220171)
            ·
              refine ⟨85047334741254835644330257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56698223160836557096220171 85047334741254835644330257)
              ·
                refine ⟨63785501055941126733247693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85047334741254835644330257 63785501055941126733247693)
                ·
                  refine ⟨23919562895977922524967885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63785501055941126733247693 23919562895977922524967885)
                  ·
                    refine ⟨8969836085991720946862957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23919562895977922524967885 8969836085991720946862957)
                    ·
                      refine ⟨3363688532246895355073609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969836085991720946862957 3363688532246895355073609)
                      ·
                        rfl

theorem cell23_6550760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6550760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550760 prefixEnd_6550760 := by exact prefixLift 6550760
  have htrace : WordTrace (prefixWord ++ tailWord_6550760) baseStart_6550760 baseEnd_6550760 := by
    simpa [prefixWord, tailWord_6550760, baseEnd_6550760] using wordTrace_append hprefix tailTrace_6550760
  have hstable : (prefixWord ++ tailWord_6550760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550760).length < 2 ^ (prefixWord ++ tailWord_6550760).sum := by decide
  have hdescent : baseEnd_6550760 < baseStart_6550760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550763 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 7]
def baseStart_6550763 : Nat := 118140960795 + 6550763 * 2 ^ 59
def prefixEnd_6550763 : Nat := 4983230072969 + 3 ^ 40 * 6550763 * 2
def baseEnd_6550763 : Nat := 1121230024229619614445365

theorem tailTrace_6550763 : CollatzResearch.WordTrace tailWord_6550763 prefixEnd_6550763 1121230024229619614445365 := by
  unfold tailWord_6550763
  simp only [CollatzResearch.WordTrace]
  refine ⟨238925955166711907094784943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159283970111141271396523295 238925955166711907094784943)
  ·
    refine ⟨358388932750067860642177415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238925955166711907094784943 358388932750067860642177415)
    ·
      refine ⟨537583399125101790963266123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358388932750067860642177415 537583399125101790963266123)
      ·
        refine ⟨806375098687652686444899185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537583399125101790963266123 806375098687652686444899185)
        ·
          refine ⟨604781324015739514833674389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806375098687652686444899185 604781324015739514833674389)
          ·
            refine ⟨28349124563237789757828487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 604781324015739514833674389 28349124563237789757828487)
            ·
              refine ⟨42523686844856684636742731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28349124563237789757828487 42523686844856684636742731)
              ·
                refine ⟨63785530267285026955114097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42523686844856684636742731 63785530267285026955114097)
                ·
                  refine ⟨47839147700463770216335573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63785530267285026955114097 47839147700463770216335573)
                  ·
                    refine ⟨1121230024229619614445365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47839147700463770216335573 1121230024229619614445365)
                    ·
                      rfl

theorem cell23_6550763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_6550763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550763 prefixEnd_6550763 := by exact prefixLift 6550763
  have htrace : WordTrace (prefixWord ++ tailWord_6550763) baseStart_6550763 baseEnd_6550763 := by
    simpa [prefixWord, tailWord_6550763, baseEnd_6550763] using wordTrace_append hprefix tailTrace_6550763
  have hstable : (prefixWord ++ tailWord_6550763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550763).length < 2 ^ (prefixWord ++ tailWord_6550763).sum := by decide
  have hdescent : baseEnd_6550763 < baseStart_6550763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550767 : List Nat := [1, 1, 2, 1, 8, 1, 1, 8]
def baseStart_6550767 : Nat := 118140960795 + 6550767 * 2 ^ 59
def prefixEnd_6550767 : Nat := 4983230072969 + 3 ^ 40 * 6550767 * 2
def baseEnd_6550767 : Nat := 124581189874499141766151

theorem tailTrace_6550767 : CollatzResearch.WordTrace tailWord_6550767 prefixEnd_6550767 124581189874499141766151 := by
  unfold tailWord_6550767
  simp only [CollatzResearch.WordTrace]
  refine ⟨238926101058697415777930555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159284067372464943851953703 238926101058697415777930555)
  ·
    refine ⟨358389151588046123666895833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238926101058697415777930555 358389151588046123666895833)
    ·
      refine ⟨268791863691034592750171875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358389151588046123666895833 268791863691034592750171875)
      ·
        refine ⟨403187795536551889125257813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268791863691034592750171875 403187795536551889125257813)
        ·
          refine ⟨4724856978943967450686615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 403187795536551889125257813 4724856978943967450686615)
          ·
            refine ⟨7087285468415951176029923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724856978943967450686615 7087285468415951176029923)
            ·
              refine ⟨10630928202623926764044885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087285468415951176029923 10630928202623926764044885)
              ·
                refine ⟨124581189874499141766151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10630928202623926764044885 124581189874499141766151)
                ·
                  rfl

theorem cell23_6550767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 8].length) (baseStart_6550767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550767 prefixEnd_6550767 := by exact prefixLift 6550767
  have htrace : WordTrace (prefixWord ++ tailWord_6550767) baseStart_6550767 baseEnd_6550767 := by
    simpa [prefixWord, tailWord_6550767, baseEnd_6550767] using wordTrace_append hprefix tailTrace_6550767
  have hstable : (prefixWord ++ tailWord_6550767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550767).length < 2 ^ (prefixWord ++ tailWord_6550767).sum := by decide
  have hdescent : baseEnd_6550767 < baseStart_6550767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550777 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_6550777 : Nat := 118140960795 + 6550777 * 2 ^ 59
def prefixEnd_6550777 : Nat := 4983230072969 + 3 ^ 40 * 6550777 * 2
def baseEnd_6550777 : Nat := 3363697261418021788561031

theorem tailTrace_6550777 : CollatzResearch.WordTrace tailWord_6550777 prefixEnd_6550777 3363697261418021788561031 := by
  unfold tailWord_6550777
  simp only [CollatzResearch.WordTrace]
  refine ⟨238926465788661187485794585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159284310525774124990529723 238926465788661187485794585)
  ·
    refine ⟨179194849341495890614345939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238926465788661187485794585 179194849341495890614345939)
    ·
      refine ⟨268792274012243835921518909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179194849341495890614345939 268792274012243835921518909)
      ·
        refine ⟨100797102754591438470569591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268792274012243835921518909 100797102754591438470569591)
        ·
          refine ⟨151195654131887157705854387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100797102754591438470569591 151195654131887157705854387)
          ·
            refine ⟨226793481197830736558781581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151195654131887157705854387 226793481197830736558781581)
            ·
              refine ⟨85047555449186526209543093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226793481197830736558781581 85047555449186526209543093)
              ·
                refine ⟨7973208323361236832144665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85047555449186526209543093 7973208323361236832144665)
                ·
                  refine ⟨5979906242520927624108499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7973208323361236832144665 5979906242520927624108499)
                  ·
                    refine ⟨8969859363781391436162749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979906242520927624108499 8969859363781391436162749)
                    ·
                      refine ⟨3363697261418021788561031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8969859363781391436162749 3363697261418021788561031)
                      ·
                        rfl

theorem cell23_6550777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_6550777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550777 prefixEnd_6550777 := by exact prefixLift 6550777
  have htrace : WordTrace (prefixWord ++ tailWord_6550777) baseStart_6550777 baseEnd_6550777 := by
    simpa [prefixWord, tailWord_6550777, baseEnd_6550777] using wordTrace_append hprefix tailTrace_6550777
  have hstable : (prefixWord ++ tailWord_6550777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550777).length < 2 ^ (prefixWord ++ tailWord_6550777).sum := by decide
  have hdescent : baseEnd_6550777 < baseStart_6550777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550787 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 3, 3, 2]
def baseStart_6550787 : Nat := 118140960795 + 6550787 * 2 ^ 59
def prefixEnd_6550787 : Nat := 4983230072969 + 3 ^ 40 * 6550787 * 2
def baseEnd_6550787 : Nat := 3363702396224566749435985

theorem tailTrace_6550787 : CollatzResearch.WordTrace tailWord_6550787 prefixEnd_6550787 3363702396224566749435985 := by
  unfold tailWord_6550787
  simp only [CollatzResearch.WordTrace]
  refine ⟨238926830518624959193658615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159284553679083306129105743 238926830518624959193658615)
  ·
    refine ⟨358390245777937438790487923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238926830518624959193658615 358390245777937438790487923)
    ·
      refine ⟨537585368666906158185731885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358390245777937438790487923 537585368666906158185731885)
      ·
        refine ⟨201594513250089809319649457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537585368666906158185731885 201594513250089809319649457)
        ·
          refine ⟨151195884937567356989737093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201594513250089809319649457 151195884937567356989737093)
          ·
            refine ⟨28349228425793879435575705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151195884937567356989737093 28349228425793879435575705)
            ·
              refine ⟨21261921319345409576681779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28349228425793879435575705 21261921319345409576681779)
              ·
                refine ⟨31892881979018114365022669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21261921319345409576681779 31892881979018114365022669)
                ·
                  refine ⟨11959830742131792886883501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31892881979018114365022669 11959830742131792886883501)
                  ·
                    refine ⟨4484936528299422332581313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11959830742131792886883501 4484936528299422332581313)
                    ·
                      refine ⟨3363702396224566749435985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484936528299422332581313 3363702396224566749435985)
                      ·
                        rfl

theorem cell23_6550787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_6550787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550787 prefixEnd_6550787 := by exact prefixLift 6550787
  have htrace : WordTrace (prefixWord ++ tailWord_6550787) baseStart_6550787 baseEnd_6550787 := by
    simpa [prefixWord, tailWord_6550787, baseEnd_6550787] using wordTrace_append hprefix tailTrace_6550787
  have hstable : (prefixWord ++ tailWord_6550787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550787).length < 2 ^ (prefixWord ++ tailWord_6550787).sum := by decide
  have hdescent : baseEnd_6550787 < baseStart_6550787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550793 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_6550793 : Nat := 118140960795 + 6550793 * 2 ^ 59
def prefixEnd_6550793 : Nat := 4983230072969 + 3 ^ 40 * 6550793 * 2
def baseEnd_6550793 : Nat := 1121235159036164575320319

theorem tailTrace_6550793 : CollatzResearch.WordTrace tailWord_6550793 prefixEnd_6550793 1121235159036164575320319 := by
  unfold tailWord_6550793
  simp only [CollatzResearch.WordTrace]
  refine ⟨238927049356603222218377033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159284699571068814812251355 238927049356603222218377033)
  ·
    refine ⟨179195287017452416663782775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238927049356603222218377033 179195287017452416663782775)
    ·
      refine ⟨268792930526178624995674163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179195287017452416663782775 268792930526178624995674163)
      ·
        refine ⟨403189395789267937493511245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268792930526178624995674163 403189395789267937493511245)
        ·
          refine ⟨151196023420975476560066717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403189395789267937493511245 151196023420975476560066717)
          ·
            refine ⟨56698508782865803710025019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151196023420975476560066717 56698508782865803710025019)
            ·
              refine ⟨85047763174298705565037529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56698508782865803710025019 85047763174298705565037529)
              ·
                refine ⟨63785822380724029173778147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85047763174298705565037529 63785822380724029173778147)
                ·
                  refine ⟨95678733571086043760667221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63785822380724029173778147 95678733571086043760667221)
                  ·
                    refine ⟨1121235159036164575320319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95678733571086043760667221 1121235159036164575320319)
                    ·
                      rfl

theorem cell23_6550793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_6550793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550793 prefixEnd_6550793 := by exact prefixLift 6550793
  have htrace : WordTrace (prefixWord ++ tailWord_6550793) baseStart_6550793 baseEnd_6550793 := by
    simpa [prefixWord, tailWord_6550793, baseEnd_6550793] using wordTrace_append hprefix tailTrace_6550793
  have hstable : (prefixWord ++ tailWord_6550793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550793).length < 2 ^ (prefixWord ++ tailWord_6550793).sum := by decide
  have hdescent : baseEnd_6550793 < baseStart_6550793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2]
def baseStart_6550800 : Nat := 118140960795 + 6550800 * 2 ^ 59
def prefixEnd_6550800 : Nat := 4983230072969 + 3 ^ 40 * 6550800 * 2
def baseEnd_6550800 : Nat := 3363709071473075198573425

theorem tailTrace_6550800 : CollatzResearch.WordTrace tailWord_6550800 prefixEnd_6550800 3363709071473075198573425 := by
  unfold tailWord_6550800
  simp only [CollatzResearch.WordTrace]
  refine ⟨119463652333788931206940927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159284869778385241609254569 119463652333788931206940927)
  ·
    refine ⟨179195478500683396810411391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119463652333788931206940927 179195478500683396810411391)
    ·
      refine ⟨268793217751025095215617087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179195478500683396810411391 268793217751025095215617087)
      ·
        refine ⟨403189826626537642823425631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268793217751025095215617087 403189826626537642823425631)
        ·
          refine ⟨604784739939806464235138447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403189826626537642823425631 604784739939806464235138447)
          ·
            refine ⟨907177109909709696352707671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604784739939806464235138447 907177109909709696352707671)
            ·
              refine ⟨1360765664864564544529061507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907177109909709696352707671 1360765664864564544529061507)
              ·
                refine ⟨2041148497296846816793592261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360765664864564544529061507 2041148497296846816793592261)
                ·
                  refine ⟨382715343243158778148798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041148497296846816793592261 382715343243158778148798549)
                  ·
                    refine ⟨4484945428630766931431233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 382715343243158778148798549 4484945428630766931431233)
                    ·
                      refine ⟨3363709071473075198573425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484945428630766931431233 3363709071473075198573425)
                      ·
                        rfl

theorem cell23_6550800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2].length) (baseStart_6550800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550800 prefixEnd_6550800 := by exact prefixLift 6550800
  have htrace : WordTrace (prefixWord ++ tailWord_6550800) baseStart_6550800 baseEnd_6550800 := by
    simpa [prefixWord, tailWord_6550800, baseEnd_6550800] using wordTrace_append hprefix tailTrace_6550800
  have hstable : (prefixWord ++ tailWord_6550800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550800).length < 2 ^ (prefixWord ++ tailWord_6550800).sum := by decide
  have hdescent : baseEnd_6550800 < baseStart_6550800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550810 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_6550810 : Nat := 118140960795 + 6550810 * 2 ^ 59
def prefixEnd_6550810 : Nat := 4983230072969 + 3 ^ 40 * 6550810 * 2
def baseEnd_6550810 : Nat := 1121238068759873386482793

theorem tailTrace_6550810 : CollatzResearch.WordTrace tailWord_6550810 prefixEnd_6550810 1121238068759873386482793 := by
  unfold tailWord_6550810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731917349385408530436471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159285112931694422747830589 59731917349385408530436471)
  ·
    refine ⟨89597876024078112795654707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59731917349385408530436471 89597876024078112795654707)
    ·
      refine ⟨134396814036117169193482061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89597876024078112795654707 134396814036117169193482061)
      ·
        refine ⟨50398805263543938447555773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134396814036117169193482061 50398805263543938447555773)
        ·
          refine ⟨18899551973828976917833415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50398805263543938447555773 18899551973828976917833415)
          ·
            refine ⟨28349327960743465376750123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18899551973828976917833415 28349327960743465376750123)
            ·
              refine ⟨42523991941115198065125185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28349327960743465376750123 42523991941115198065125185)
              ·
                refine ⟨31892993955836398548843889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42523991941115198065125185 31892993955836398548843889)
                ·
                  refine ⟨23919745466877298911632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31892993955836398548843889 23919745466877298911632917)
                  ·
                    refine ⟨1121238068759873386482793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23919745466877298911632917 1121238068759873386482793)
                    ·
                      rfl

theorem cell23_6550810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_6550810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550810 prefixEnd_6550810 := by exact prefixLift 6550810
  have htrace : WordTrace (prefixWord ++ tailWord_6550810) baseStart_6550810 baseEnd_6550810 := by
    simpa [prefixWord, tailWord_6550810, baseEnd_6550810] using wordTrace_append hprefix tailTrace_6550810
  have hstable : (prefixWord ++ tailWord_6550810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550810).length < 2 ^ (prefixWord ++ tailWord_6550810).sum := by decide
  have hdescent : baseEnd_6550810 < baseStart_6550810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550834 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_6550834 : Nat := 118140960795 + 6550834 * 2 ^ 59
def prefixEnd_6550834 : Nat := 4983230072969 + 3 ^ 40 * 6550834 * 2
def baseEnd_6550834 : Nat := 3363726529815328065548269

theorem tailTrace_6550834 : CollatzResearch.WordTrace tailWord_6550834 prefixEnd_6550834 3363726529815328065548269 := by
  unfold tailWord_6550834
  simp only [CollatzResearch.WordTrace]
  refine ⟨59732136187363671555154889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159285696499636457480413037 59732136187363671555154889)
  ·
    refine ⟨44799102140522753666366167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59732136187363671555154889 44799102140522753666366167)
    ·
      refine ⟨67198653210784130499549251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44799102140522753666366167 67198653210784130499549251)
      ·
        refine ⟨100797979816176195749323877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67198653210784130499549251 100797979816176195749323877)
        ·
          refine ⟨18899621215533036702998227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100797979816176195749323877 18899621215533036702998227)
          ·
            refine ⟨28349431823299555054497341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18899621215533036702998227 28349431823299555054497341)
            ·
              refine ⟨10631036933737333145436503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28349431823299555054497341 10631036933737333145436503)
              ·
                refine ⟨15946555400605999718154755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631036933737333145436503 15946555400605999718154755)
                ·
                  refine ⟨23919833100908999577232133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15946555400605999718154755 23919833100908999577232133)
                  ·
                    refine ⟨4484968706420437420731025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23919833100908999577232133 4484968706420437420731025)
                    ·
                      refine ⟨3363726529815328065548269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484968706420437420731025 3363726529815328065548269)
                      ·
                        rfl

theorem cell23_6550834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_6550834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550834 prefixEnd_6550834 := by exact prefixLift 6550834
  have htrace : WordTrace (prefixWord ++ tailWord_6550834) baseStart_6550834 baseEnd_6550834 := by
    simpa [prefixWord, tailWord_6550834, baseEnd_6550834] using wordTrace_append hprefix tailTrace_6550834
  have hstable : (prefixWord ++ tailWord_6550834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550834).length < 2 ^ (prefixWord ++ tailWord_6550834).sum := by decide
  have hdescent : baseEnd_6550834 < baseStart_6550834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550843 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_6550843 : Nat := 118140960795 + 6550843 * 2 ^ 59
def prefixEnd_6550843 : Nat := 4983230072969 + 3 ^ 40 * 6550843 * 2
def baseEnd_6550843 : Nat := 3363731151141218530335727

theorem tailTrace_6550843 : CollatzResearch.WordTrace tailWord_6550843 prefixEnd_6550843 3363731151141218530335727 := by
  unfold tailWord_6550843
  simp only [CollatzResearch.WordTrace]
  refine ⟨238928873006422080757697183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159285915337614720505131455 238928873006422080757697183)
  ·
    refine ⟨358393309509633121136545775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238928873006422080757697183 358393309509633121136545775)
    ·
      refine ⟨537589964264449681704818663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358393309509633121136545775 537589964264449681704818663)
      ·
        refine ⟨806384946396674522557227995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537589964264449681704818663 806384946396674522557227995)
        ·
          refine ⟨1209577419595011783835841993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806384946396674522557227995 1209577419595011783835841993)
          ·
            refine ⟨907183064696258837876881495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209577419595011783835841993 907183064696258837876881495)
            ·
              refine ⟨1360774597044388256815322243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907183064696258837876881495 1360774597044388256815322243)
              ·
                refine ⟨2041161895566582385222983365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360774597044388256815322243 2041161895566582385222983365)
                ·
                  refine ⟨382717855418734197229309381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041161895566582385222983365 382717855418734197229309381)
                  ·
                    refine ⟨71759597891012661980495509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382717855418734197229309381 71759597891012661980495509)
                    ·
                      refine ⟨3363731151141218530335727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71759597891012661980495509 3363731151141218530335727)
                      ·
                        rfl

theorem cell23_6550843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_6550843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550843 prefixEnd_6550843 := by exact prefixLift 6550843
  have htrace : WordTrace (prefixWord ++ tailWord_6550843) baseStart_6550843 baseEnd_6550843 := by
    simpa [prefixWord, tailWord_6550843, baseEnd_6550843] using wordTrace_append hprefix tailTrace_6550843
  have hstable : (prefixWord ++ tailWord_6550843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550843).length < 2 ^ (prefixWord ++ tailWord_6550843).sum := by decide
  have hdescent : baseEnd_6550843 < baseStart_6550843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550857 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 5]
def baseStart_6550857 : Nat := 118140960795 + 6550857 * 2 ^ 59
def prefixEnd_6550857 : Nat := 4983230072969 + 3 ^ 40 * 6550857 * 2
def baseEnd_6550857 : Nat := 373748704430042386173407

theorem tailTrace_6550857 : CollatzResearch.WordTrace tailWord_6550857 prefixEnd_6550857 373748704430042386173407 := by
  unfold tailWord_6550857
  simp only [CollatzResearch.WordTrace]
  refine ⟨238929383628371361148706825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159286255752247574099137883 238929383628371361148706825)
  ·
    refine ⟨179197037721278520861530119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238929383628371361148706825 179197037721278520861530119)
    ·
      refine ⟨268795556581917781292295179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179197037721278520861530119 268795556581917781292295179)
      ·
        refine ⟨403193334872876671938442769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268795556581917781292295179 403193334872876671938442769)
        ·
          refine ⟨302395001154657503953832077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403193334872876671938442769 302395001154657503953832077)
          ·
            refine ⟨113398125432996563982687029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302395001154657503953832077 113398125432996563982687029)
            ·
              refine ⟨10631074259343427873376909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113398125432996563982687029 10631074259343427873376909)
              ·
                refine ⟨3986652847253785452516341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10631074259343427873376909 3986652847253785452516341)
                ·
                  refine ⟨373748704430042386173407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986652847253785452516341 373748704430042386173407)
                  ·
                    rfl

theorem cell23_6550857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 5].length) (baseStart_6550857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550857 prefixEnd_6550857 := by exact prefixLift 6550857
  have htrace : WordTrace (prefixWord ++ tailWord_6550857) baseStart_6550857 baseEnd_6550857 := by
    simpa [prefixWord, tailWord_6550857, baseEnd_6550857] using wordTrace_append hprefix tailTrace_6550857
  have hstable : (prefixWord ++ tailWord_6550857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550857).length < 2 ^ (prefixWord ++ tailWord_6550857).sum := by decide
  have hdescent : baseEnd_6550857 < baseStart_6550857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550880 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6550880 : Nat := 118140960795 + 6550880 * 2 ^ 59
def prefixEnd_6550880 : Nat := 4983230072969 + 3 ^ 40 * 6550880 * 2
def baseEnd_6550880 : Nat := 3363750149925434885573057

theorem tailTrace_6550880 : CollatzResearch.WordTrace tailWord_6550880 prefixEnd_6550880 3363750149925434885573057 := by
  unfold tailWord_6550880
  simp only [CollatzResearch.WordTrace]
  refine ⟨119465111253644018038397047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159286815004858690717862729 119465111253644018038397047)
  ·
    refine ⟨179197666880466027057595571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119465111253644018038397047 179197666880466027057595571)
    ·
      refine ⟨268796500320699040586393357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179197666880466027057595571 268796500320699040586393357)
      ·
        refine ⟨100798687620262140219897509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268796500320699040586393357 100798687620262140219897509)
        ·
          refine ⟨18899753928799151291230783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100798687620262140219897509 18899753928799151291230783)
          ·
            refine ⟨28349630893198726936846175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18899753928799151291230783 28349630893198726936846175)
            ·
              refine ⟨42524446339798090405269263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28349630893198726936846175 42524446339798090405269263)
              ·
                refine ⟨63786669509697135607903895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42524446339798090405269263 63786669509697135607903895)
                ·
                  refine ⟨95680004264545703411855843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63786669509697135607903895 95680004264545703411855843)
                  ·
                    refine ⟨143520006396818555117783765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95680004264545703411855843 143520006396818555117783765)
                    ·
                      refine ⟨3363750149925434885573057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143520006396818555117783765 3363750149925434885573057)
                      ·
                        rfl

theorem cell23_6550880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6550880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550880 prefixEnd_6550880 := by exact prefixLift 6550880
  have htrace : WordTrace (prefixWord ++ tailWord_6550880) baseStart_6550880 baseEnd_6550880 := by
    simpa [prefixWord, tailWord_6550880, baseEnd_6550880] using wordTrace_append hprefix tailTrace_6550880
  have hstable : (prefixWord ++ tailWord_6550880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550880).length < 2 ^ (prefixWord ++ tailWord_6550880).sum := by decide
  have hdescent : baseEnd_6550880 < baseStart_6550880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550907 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4]
def baseStart_6550907 : Nat := 118140960795 + 6550907 * 2 ^ 59
def prefixEnd_6550907 : Nat := 4983230072969 + 3 ^ 40 * 6550907 * 2
def baseEnd_6550907 : Nat := 3363764013903106279935433

theorem tailTrace_6550907 : CollatzResearch.WordTrace tailWord_6550907 prefixEnd_6550907 3363764013903106279935433 := by
  unfold tailWord_6550907
  simp only [CollatzResearch.WordTrace]
  refine ⟨238931207278190219688026975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159287471518793479792017983 238931207278190219688026975)
  ·
    refine ⟨358396810917285329532040463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238931207278190219688026975 358396810917285329532040463)
    ·
      refine ⟨537595216375927994298060695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358396810917285329532040463 537595216375927994298060695)
      ·
        refine ⟨806392824563891991447091043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537595216375927994298060695 806392824563891991447091043)
        ·
          refine ⟨1209589236845837987170636565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806392824563891991447091043 1209589236845837987170636565)
          ·
            refine ⟨56699495477148655648623589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1209589236845837987170636565 56699495477148655648623589)
            ·
              refine ⟨10631155401965372934116923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56699495477148655648623589 10631155401965372934116923)
              ·
                refine ⟨15946733102948059401175385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631155401965372934116923 15946733102948059401175385)
                ·
                  refine ⟨11960049827211044550881539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15946733102948059401175385 11960049827211044550881539)
                  ·
                    refine ⟨17940074740816566826322309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11960049827211044550881539 17940074740816566826322309)
                    ·
                      refine ⟨3363764013903106279935433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17940074740816566826322309 3363764013903106279935433)
                      ·
                        rfl

theorem cell23_6550907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 4].length) (baseStart_6550907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550907 prefixEnd_6550907 := by exact prefixLift 6550907
  have htrace : WordTrace (prefixWord ++ tailWord_6550907) baseStart_6550907 baseEnd_6550907 := by
    simpa [prefixWord, tailWord_6550907, baseEnd_6550907] using wordTrace_append hprefix tailTrace_6550907
  have hstable : (prefixWord ++ tailWord_6550907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550907).length < 2 ^ (prefixWord ++ tailWord_6550907).sum := by decide
  have hdescent : baseEnd_6550907 < baseStart_6550907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550914 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6550914 : Nat := 118140960795 + 6550914 * 2 ^ 59
def prefixEnd_6550914 : Nat := 4983230072969 + 3 ^ 40 * 6550914 * 2
def baseEnd_6550914 : Nat := 3363767608267687752547901

theorem tailTrace_6550914 : CollatzResearch.WordTrace tailWord_6550914 prefixEnd_6550914 3363767608267687752547901 := by
  unfold tailWord_6550914
  simp only [CollatzResearch.WordTrace]
  refine ⟨59732865647291214970882949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159287641726109906589021197 59732865647291214970882949)
  ·
    refine ⟨11199912308867102807040553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59732865647291214970882949 11199912308867102807040553)
    ·
      refine ⟨8399934231650327105280415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11199912308867102807040553 8399934231650327105280415)
      ·
        refine ⟨12599901347475490657920623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399934231650327105280415 12599901347475490657920623)
        ·
          refine ⟨18899852021213235986880935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12599901347475490657920623 18899852021213235986880935)
          ·
            refine ⟨28349778031819853980321403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18899852021213235986880935 28349778031819853980321403)
            ·
              refine ⟨42524667047729780970482105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28349778031819853980321403 42524667047729780970482105)
              ·
                refine ⟨31893500285797335727861579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42524667047729780970482105 31893500285797335727861579)
                ·
                  refine ⟨47840250428696003591792369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31893500285797335727861579 47840250428696003591792369)
                  ·
                    refine ⟨35880187821522002693844277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47840250428696003591792369 35880187821522002693844277)
                    ·
                      refine ⟨3363767608267687752547901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35880187821522002693844277 3363767608267687752547901)
                      ·
                        rfl

theorem cell23_6550914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6550914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550914 prefixEnd_6550914 := by exact prefixLift 6550914
  have htrace : WordTrace (prefixWord ++ tailWord_6550914) baseStart_6550914 baseEnd_6550914 := by
    simpa [prefixWord, tailWord_6550914, baseEnd_6550914] using wordTrace_append hprefix tailTrace_6550914
  have hstable : (prefixWord ++ tailWord_6550914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550914).length < 2 ^ (prefixWord ++ tailWord_6550914).sum := by decide
  have hdescent : baseEnd_6550914 < baseStart_6550914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550970 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_6550970 : Nat := 118140960795 + 6550970 * 2 ^ 59
def prefixEnd_6550970 : Nat := 4983230072969 + 3 ^ 40 * 6550970 * 2
def baseEnd_6550970 : Nat := 3363796363184339533447643

theorem tailTrace_6550970 : CollatzResearch.WordTrace tailWord_6550970 prefixEnd_6550970 3363796363184339533447643 := by
  unfold tailWord_6550970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733376269240495361892591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159289003384641320965046909 59733376269240495361892591)
  ·
    refine ⟨89600064403860743042838887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59733376269240495361892591 89600064403860743042838887)
    ·
      refine ⟨134400096605791114564258331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89600064403860743042838887 134400096605791114564258331)
      ·
        refine ⟨201600144908686671846387497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134400096605791114564258331 201600144908686671846387497)
        ·
          refine ⟨151200108681515003884790623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201600144908686671846387497 151200108681515003884790623)
          ·
            refine ⟨226800163022272505827185935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151200108681515003884790623 226800163022272505827185935)
            ·
              refine ⟨340200244533408758740778903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226800163022272505827185935 340200244533408758740778903)
              ·
                refine ⟨510300366800113138111168355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340200244533408758740778903 510300366800113138111168355)
                ·
                  refine ⟨765450550200169707166752533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510300366800113138111168355 765450550200169707166752533)
                  ·
                    refine ⟨35880494540632955023441525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 765450550200169707166752533 35880494540632955023441525)
                    ·
                      refine ⟨3363796363184339533447643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35880494540632955023441525 3363796363184339533447643)
                      ·
                        rfl

theorem cell23_6550970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_6550970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550970 prefixEnd_6550970 := by exact prefixLift 6550970
  have htrace : WordTrace (prefixWord ++ tailWord_6550970) baseStart_6550970 baseEnd_6550970 := by
    simpa [prefixWord, tailWord_6550970, baseEnd_6550970] using wordTrace_append hprefix tailTrace_6550970
  have hstable : (prefixWord ++ tailWord_6550970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550970).length < 2 ^ (prefixWord ++ tailWord_6550970).sum := by decide
  have hdescent : baseEnd_6550970 < baseStart_6550970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550974 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_6550974 : Nat := 118140960795 + 6550974 * 2 ^ 59
def prefixEnd_6550974 : Nat := 4983230072969 + 3 ^ 40 * 6550974 * 2
def baseEnd_6550974 : Nat := 3363798417106957517797625

theorem tailTrace_6550974 : CollatzResearch.WordTrace tailWord_6550974 prefixEnd_6550974 3363798417106957517797625 := by
  unfold tailWord_6550974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29866706371118436266339497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159289100645964993420477317 29866706371118436266339497)
  ·
    refine ⟨22400029778338827199754623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29866706371118436266339497 22400029778338827199754623)
    ·
      refine ⟨33600044667508240799631935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22400029778338827199754623 33600044667508240799631935)
      ·
        refine ⟨50400067001262361199447903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33600044667508240799631935 50400067001262361199447903)
        ·
          refine ⟨75600100501893541799171855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50400067001262361199447903 75600100501893541799171855)
          ·
            refine ⟨113400150752840312698757783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75600100501893541799171855 113400150752840312698757783)
            ·
              refine ⟨170100226129260469048136675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113400150752840312698757783 170100226129260469048136675)
              ·
                refine ⟨255150339193890703572205013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170100226129260469048136675 255150339193890703572205013)
                ·
                  refine ⟨5980086074856813364973555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255150339193890703572205013 5980086074856813364973555)
                  ·
                    refine ⟨8970129112285220047460333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980086074856813364973555 8970129112285220047460333)
                    ·
                      refine ⟨3363798417106957517797625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970129112285220047460333 3363798417106957517797625)
                      ·
                        rfl

theorem cell23_6550974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_6550974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550974 prefixEnd_6550974 := by exact prefixLift 6550974
  have htrace : WordTrace (prefixWord ++ tailWord_6550974) baseStart_6550974 baseEnd_6550974 := by
    simpa [prefixWord, tailWord_6550974, baseEnd_6550974] using wordTrace_append hprefix tailTrace_6550974
  have hstable : (prefixWord ++ tailWord_6550974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550974).length < 2 ^ (prefixWord ++ tailWord_6550974).sum := by decide
  have hdescent : baseEnd_6550974 < baseStart_6550974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550984 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_6550984 : Nat := 118140960795 + 6550984 * 2 ^ 59
def prefixEnd_6550984 : Nat := 4983230072969 + 3 ^ 40 * 6550984 * 2
def baseEnd_6550984 : Nat := 3363803551913502478672579

theorem tailTrace_6550984 : CollatzResearch.WordTrace tailWord_6550984 prefixEnd_6550984 3363803551913502478672579 := by
  unfold tailWord_6550984
  simp only [CollatzResearch.WordTrace]
  refine ⟨119467007849455630919290003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159289343799274174559053337 119467007849455630919290003)
  ·
    refine ⟨179200511774183446378935005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119467007849455630919290003 179200511774183446378935005)
    ·
      refine ⟨67200191915318792392100627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179200511774183446378935005 67200191915318792392100627)
      ·
        refine ⟨100800287872978188588150941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67200191915318792392100627 100800287872978188588150941)
        ·
          refine ⟨37800107952366820720556603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100800287872978188588150941 37800107952366820720556603)
          ·
            refine ⟨56700161928550231080834905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37800107952366820720556603 56700161928550231080834905)
            ·
              refine ⟨42525121446412673310626179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56700161928550231080834905 42525121446412673310626179)
              ·
                refine ⟨63787682169619009965939269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42525121446412673310626179 63787682169619009965939269)
                ·
                  refine ⟨11960190406803564368613613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63787682169619009965939269 11960190406803564368613613)
                  ·
                    refine ⟨4485071402551336638230105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11960190406803564368613613 4485071402551336638230105)
                    ·
                      refine ⟨3363803551913502478672579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485071402551336638230105 3363803551913502478672579)
                      ·
                        rfl

theorem cell23_6550984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_6550984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550984 prefixEnd_6550984 := by exact prefixLift 6550984
  have htrace : WordTrace (prefixWord ++ tailWord_6550984) baseStart_6550984 baseEnd_6550984 := by
    simpa [prefixWord, tailWord_6550984, baseEnd_6550984] using wordTrace_append hprefix tailTrace_6550984
  have hstable : (prefixWord ++ tailWord_6550984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550984).length < 2 ^ (prefixWord ++ tailWord_6550984).sum := by decide
  have hdescent : baseEnd_6550984 < baseStart_6550984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6550991 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 1, 1, 3]
def baseStart_6550991 : Nat := 118140960795 + 6550991 * 2 ^ 59
def prefixEnd_6550991 : Nat := 4983230072969 + 3 ^ 40 * 6550991 * 2
def baseEnd_6550991 : Nat := 3363807146278083951285047

theorem tailTrace_6550991 : CollatzResearch.WordTrace tailWord_6550991 prefixEnd_6550991 3363807146278083951285047 := by
  unfold tailWord_6550991
  simp only [CollatzResearch.WordTrace]
  refine ⟨238934271009885902034084827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159289514006590601356056551 238934271009885902034084827)
  ·
    refine ⟨358401406514828853051127241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238934271009885902034084827 358401406514828853051127241)
    ·
      refine ⟨268801054886121639788345431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358401406514828853051127241 268801054886121639788345431)
      ·
        refine ⟨403201582329182459682518147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268801054886121639788345431 403201582329182459682518147)
        ·
          refine ⟨604802373493773689523777221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403201582329182459682518147 604802373493773689523777221)
          ·
            refine ⟨113400445030082566785708229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 604802373493773689523777221 113400445030082566785708229)
            ·
              refine ⟨21262583443140481272320293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113400445030082566785708229 21262583443140481272320293)
              ·
                refine ⟨3986734395588840238560055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21262583443140481272320293 3986734395588840238560055)
                ·
                  refine ⟨5980101593383260357840083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986734395588840238560055 5980101593383260357840083)
                  ·
                    refine ⟨8970152390074890536760125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980101593383260357840083 8970152390074890536760125)
                    ·
                      refine ⟨3363807146278083951285047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970152390074890536760125 3363807146278083951285047)
                      ·
                        rfl

theorem cell23_6550991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 1, 3].length) (baseStart_6550991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6550991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6550991 prefixEnd_6550991 := by exact prefixLift 6550991
  have htrace : WordTrace (prefixWord ++ tailWord_6550991) baseStart_6550991 baseEnd_6550991 := by
    simpa [prefixWord, tailWord_6550991, baseEnd_6550991] using wordTrace_append hprefix tailTrace_6550991
  have hstable : (prefixWord ++ tailWord_6550991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6550991).length < 2 ^ (prefixWord ++ tailWord_6550991).sum := by decide
  have hdescent : baseEnd_6550991 < baseStart_6550991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6550991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551017 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_6551017 : Nat := 118140960795 + 6551017 * 2 ^ 59
def prefixEnd_6551017 : Nat := 4983230072969 + 3 ^ 40 * 6551017 * 2
def baseEnd_6551017 : Nat := 3363820496775100849559927

theorem tailTrace_6551017 : CollatzResearch.WordTrace tailWord_6551017 prefixEnd_6551017 3363820496775100849559927 := by
  unfold tailWord_6551017
  simp only [CollatzResearch.WordTrace]
  refine ⟨238935219307791708474531305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159290146205194472316354203 238935219307791708474531305)
  ·
    refine ⟨179201414480843781355898479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238935219307791708474531305 179201414480843781355898479)
    ·
      refine ⟨268802121721265672033847719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179201414480843781355898479 268802121721265672033847719)
      ·
        refine ⟨403203182581898508050771579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268802121721265672033847719 403203182581898508050771579)
        ·
          refine ⟨604804773872847762076157369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403203182581898508050771579 604804773872847762076157369)
          ·
            refine ⟨453603580404635821557118027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604804773872847762076157369 453603580404635821557118027)
            ·
              refine ⟨680405370606953732335677041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453603580404635821557118027 680405370606953732335677041)
              ·
                refine ⟨510304027955215299251757781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680405370606953732335677041 510304027955215299251757781)
                ·
                  refine ⟨11960250655200358576213073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 510304027955215299251757781 11960250655200358576213073)
                  ·
                    refine ⟨8970187991400268932159805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11960250655200358576213073 8970187991400268932159805)
                    ·
                      refine ⟨3363820496775100849559927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970187991400268932159805 3363820496775100849559927)
                      ·
                        rfl

theorem cell23_6551017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_6551017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551017 prefixEnd_6551017 := by exact prefixLift 6551017
  have htrace : WordTrace (prefixWord ++ tailWord_6551017) baseStart_6551017 baseEnd_6551017 := by
    simpa [prefixWord, tailWord_6551017, baseEnd_6551017] using wordTrace_append hprefix tailTrace_6551017
  have hstable : (prefixWord ++ tailWord_6551017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551017).length < 2 ^ (prefixWord ++ tailWord_6551017).sum := by decide
  have hdescent : baseEnd_6551017 < baseStart_6551017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551034 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_6551034 : Nat := 118140960795 + 6551034 * 2 ^ 59
def prefixEnd_6551034 : Nat := 4983230072969 + 3 ^ 40 * 6551034 * 2
def baseEnd_6551034 : Nat := 3363829225946227283047349

theorem tailTrace_6551034 : CollatzResearch.WordTrace tailWord_6551034 prefixEnd_6551034 3363829225946227283047349 := by
  unfold tailWord_6551034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733959837182530094475039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159290559565820080251933437 59733959837182530094475039)
  ·
    refine ⟨89600939755773795141712559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59733959837182530094475039 89600939755773795141712559)
    ·
      refine ⟨134401409633660692712568839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89600939755773795141712559 134401409633660692712568839)
      ·
        refine ⟨201602114450491039068853259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134401409633660692712568839 201602114450491039068853259)
        ·
          refine ⟨302403171675736558603279889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201602114450491039068853259 302403171675736558603279889)
          ·
            refine ⟨226802378756802418952459917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302403171675736558603279889 226802378756802418952459917)
            ·
              refine ⟨85050892033800907107172469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226802378756802418952459917 85050892033800907107172469)
              ·
                refine ⟨7973521128168835041297419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85050892033800907107172469 7973521128168835041297419)
                ·
                  refine ⟨11960281692253252561946129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973521128168835041297419 11960281692253252561946129)
                  ·
                    refine ⟨8970211269189939421459597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11960281692253252561946129 8970211269189939421459597)
                    ·
                      refine ⟨3363829225946227283047349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970211269189939421459597 3363829225946227283047349)
                      ·
                        rfl

theorem cell23_6551034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_6551034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551034 prefixEnd_6551034 := by exact prefixLift 6551034
  have htrace : WordTrace (prefixWord ++ tailWord_6551034) baseStart_6551034 baseEnd_6551034 := by
    simpa [prefixWord, tailWord_6551034, baseEnd_6551034] using wordTrace_append hprefix tailTrace_6551034
  have hstable : (prefixWord ++ tailWord_6551034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551034).length < 2 ^ (prefixWord ++ tailWord_6551034).sum := by decide
  have hdescent : baseEnd_6551034 < baseStart_6551034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551037 : List Nat := [1, 4, 1, 1, 1, 6, 9]
def baseStart_6551037 : Nat := 118140960795 + 6551037 * 2 ^ 59
def prefixEnd_6551037 : Nat := 4983230072969 + 3 ^ 40 * 6551037 * 2
def baseEnd_6551037 : Nat := 41528774893681367547035

theorem tailTrace_6551037 : CollatzResearch.WordTrace tailWord_6551037 prefixEnd_6551037 41528774893681367547035 := by
  unfold tailWord_6551037
  simp only [CollatzResearch.WordTrace]
  refine ⟨238935948767719251890259365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159290632511812834593506243 238935948767719251890259365)
  ·
    refine ⟨44800490393947359729423631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238935948767719251890259365 44800490393947359729423631)
    ·
      refine ⟨67200735590921039594135447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44800490393947359729423631 67200735590921039594135447)
      ·
        refine ⟨100801103386381559391203171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67200735590921039594135447 100801103386381559391203171)
        ·
          refine ⟨151201655079572339086804757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100801103386381559391203171 151201655079572339086804757)
          ·
            refine ⟨7087577581854953394693973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151201655079572339086804757 7087577581854953394693973)
            ·
              refine ⟨41528774893681367547035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7087577581854953394693973 41528774893681367547035)
              ·
                rfl

theorem cell23_6551037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 9].length) (baseStart_6551037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551037 prefixEnd_6551037 := by exact prefixLift 6551037
  have htrace : WordTrace (prefixWord ++ tailWord_6551037) baseStart_6551037 baseEnd_6551037 := by
    simpa [prefixWord, tailWord_6551037, baseEnd_6551037] using wordTrace_append hprefix tailTrace_6551037
  have hstable : (prefixWord ++ tailWord_6551037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551037).length < 2 ^ (prefixWord ++ tailWord_6551037).sum := by decide
  have hdescent : baseEnd_6551037 < baseStart_6551037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551042 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6551042 : Nat := 118140960795 + 6551042 * 2 ^ 59
def prefixEnd_6551042 : Nat := 4983230072969 + 3 ^ 40 * 6551042 * 2
def baseEnd_6551042 : Nat := 3363833333791463251747313

theorem tailTrace_6551042 : CollatzResearch.WordTrace tailWord_6551042 prefixEnd_6551042 3363833333791463251747313 := by
  unfold tailWord_6551042
  simp only [CollatzResearch.WordTrace]
  refine ⟨59734032783175284436047845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159290754088467425162794253 59734032783175284436047845)
  ·
    refine ⟨11200131146845365831758971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59734032783175284436047845 11200131146845365831758971)
    ·
      refine ⟨16800196720268048747638457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200131146845365831758971 16800196720268048747638457)
      ·
        refine ⟨12600147540201036560728843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16800196720268048747638457 12600147540201036560728843)
        ·
          refine ⟨18900221310301554841093265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600147540201036560728843 18900221310301554841093265)
          ·
            refine ⟨14175165982726166130819949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18900221310301554841093265 14175165982726166130819949)
            ·
              refine ⟨5315687243522312299057481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14175165982726166130819949 5315687243522312299057481)
              ·
                refine ⟨3986765432641734224293111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315687243522312299057481 3986765432641734224293111)
                ·
                  refine ⟨5980148148962601336439667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986765432641734224293111 5980148148962601336439667)
                  ·
                    refine ⟨8970222223443902004659501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980148148962601336439667 8970222223443902004659501)
                    ·
                      refine ⟨3363833333791463251747313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970222223443902004659501 3363833333791463251747313)
                      ·
                        rfl

theorem cell23_6551042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6551042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551042 prefixEnd_6551042 := by exact prefixLift 6551042
  have htrace : WordTrace (prefixWord ++ tailWord_6551042) baseStart_6551042 baseEnd_6551042 := by
    simpa [prefixWord, tailWord_6551042, baseEnd_6551042] using wordTrace_append hprefix tailTrace_6551042
  have hstable : (prefixWord ++ tailWord_6551042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551042).length < 2 ^ (prefixWord ++ tailWord_6551042).sum := by decide
  have hdescent : baseEnd_6551042 < baseStart_6551042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551048 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_6551048 : Nat := 118140960795 + 6551048 * 2 ^ 59
def prefixEnd_6551048 : Nat := 4983230072969 + 3 ^ 40 * 6551048 * 2
def baseEnd_6551048 : Nat := 3363836414675390228272285

theorem tailTrace_6551048 : CollatzResearch.WordTrace tailWord_6551048 prefixEnd_6551048 3363836414675390228272285 := by
  unfold tailWord_6551048
  simp only [CollatzResearch.WordTrace]
  refine ⟨119468174985339700384454899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159290899980452933845939865 119468174985339700384454899)
  ·
    refine ⟨179202262478009550576682349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119468174985339700384454899 179202262478009550576682349)
    ·
      refine ⟨67200848429253581466255881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179202262478009550576682349 67200848429253581466255881)
      ·
        refine ⟨50400636321940186099691911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67200848429253581466255881 50400636321940186099691911)
        ·
          refine ⟨75600954482910279149537867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50400636321940186099691911 75600954482910279149537867)
          ·
            refine ⟨113401431724365418724306801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75600954482910279149537867 113401431724365418724306801)
            ·
              refine ⟨85051073793274064043230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113401431724365418724306801 85051073793274064043230101)
              ·
                refine ⟨3986769084059721752026411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85051073793274064043230101 3986769084059721752026411)
                ·
                  refine ⟨5980153626089582628039617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986769084059721752026411 5980153626089582628039617)
                  ·
                    refine ⟨4485115219567186971029713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980153626089582628039617 4485115219567186971029713)
                    ·
                      refine ⟨3363836414675390228272285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485115219567186971029713 3363836414675390228272285)
                      ·
                        rfl

theorem cell23_6551048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_6551048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551048 prefixEnd_6551048 := by exact prefixLift 6551048
  have htrace : WordTrace (prefixWord ++ tailWord_6551048) baseStart_6551048 baseEnd_6551048 := by
    simpa [prefixWord, tailWord_6551048, baseEnd_6551048] using wordTrace_append hprefix tailTrace_6551048
  have hstable : (prefixWord ++ tailWord_6551048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551048).length < 2 ^ (prefixWord ++ tailWord_6551048).sum := by decide
  have hdescent : baseEnd_6551048 < baseStart_6551048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551054 : List Nat := [4, 1, 1, 2, 4, 1, 2, 8]
def baseStart_6551054 : Nat := 118140960795 + 6551054 * 2 ^ 59
def prefixEnd_6551054 : Nat := 4983230072969 + 3 ^ 40 * 6551054 * 2
def baseEnd_6551054 : Nat := 124586647983678414992491

theorem tailTrace_6551054 : CollatzResearch.WordTrace tailWord_6551054 prefixEnd_6551054 124586647983678414992491 := by
  unfold tailWord_6551054
  simp only [CollatzResearch.WordTrace]
  refine ⟨29867071101082207974203527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159291045872438442529085477 29867071101082207974203527)
  ·
    refine ⟨44800606651623311961305291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29867071101082207974203527 44800606651623311961305291)
    ·
      refine ⟨67200909977434967941957937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44800606651623311961305291 67200909977434967941957937)
      ·
        refine ⟨50400682483076225956468453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67200909977434967941957937 50400682483076225956468453)
        ·
          refine ⟨9450127965576792366837835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50400682483076225956468453 9450127965576792366837835)
          ·
            refine ⟨14175191948365188550256753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9450127965576792366837835 14175191948365188550256753)
            ·
              refine ⟨10631393961273891412692565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14175191948365188550256753 10631393961273891412692565)
              ·
                refine ⟨124586647983678414992491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10631393961273891412692565 124586647983678414992491)
                ·
                  rfl

theorem cell23_6551054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_6551054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551054 prefixEnd_6551054 := by exact prefixLift 6551054
  have htrace : WordTrace (prefixWord ++ tailWord_6551054) baseStart_6551054 baseEnd_6551054 := by
    simpa [prefixWord, tailWord_6551054, baseEnd_6551054] using wordTrace_append hprefix tailTrace_6551054
  have hstable : (prefixWord ++ tailWord_6551054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551054).length < 2 ^ (prefixWord ++ tailWord_6551054).sum := by decide
  have hdescent : baseEnd_6551054 < baseStart_6551054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2]
def baseStart_6551104 : Nat := 118140960795 + 6551104 * 2 ^ 59
def prefixEnd_6551104 : Nat := 4983230072969 + 3 ^ 40 * 6551104 * 2
def baseEnd_6551104 : Nat := 3363865169592042009172027

theorem tailTrace_6551104 : CollatzResearch.WordTrace tailWord_6551104 prefixEnd_6551104 3363865169592042009172027 := by
  unfold tailWord_6551104
  simp only [CollatzResearch.WordTrace]
  refine ⟨119469196229238261166474183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159292261638984348221965577 119469196229238261166474183)
  ·
    refine ⟨179203794343857391749711275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119469196229238261166474183 179203794343857391749711275)
    ·
      refine ⟨268805691515786087624566913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179203794343857391749711275 268805691515786087624566913)
      ·
        refine ⟨201604268636839565718425185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268805691515786087624566913 201604268636839565718425185)
        ·
          refine ⟨151203201477629674288818889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201604268636839565718425185 151203201477629674288818889)
          ·
            refine ⟨113402401108222255716614167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151203201477629674288818889 113402401108222255716614167)
            ·
              refine ⟨170103601662333383574921251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113402401108222255716614167 170103601662333383574921251)
              ·
                refine ⟨255155402493500075362381877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170103601662333383574921251 255155402493500075362381877)
                ·
                  refine ⟨23920818983765632065223301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255155402493500075362381877 23920818983765632065223301)
                  ·
                    refine ⟨4485153559456056012229369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23920818983765632065223301 4485153559456056012229369)
                    ·
                      refine ⟨3363865169592042009172027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485153559456056012229369 3363865169592042009172027)
                      ·
                        rfl

theorem cell23_6551104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_6551104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551104 prefixEnd_6551104 := by exact prefixLift 6551104
  have htrace : WordTrace (prefixWord ++ tailWord_6551104) baseStart_6551104 baseEnd_6551104 := by
    simpa [prefixWord, tailWord_6551104, baseEnd_6551104] using wordTrace_append hprefix tailTrace_6551104
  have hstable : (prefixWord ++ tailWord_6551104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551104).length < 2 ^ (prefixWord ++ tailWord_6551104).sum := by decide
  have hdescent : baseEnd_6551104 < baseStart_6551104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551121 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_6551121 : Nat := 118140960795 + 6551121 * 2 ^ 59
def prefixEnd_6551121 : Nat := 4983230072969 + 3 ^ 40 * 6551121 * 2
def baseEnd_6551121 : Nat := 3363873898763168442659449

theorem tailTrace_6551121 : CollatzResearch.WordTrace tailWord_6551121 prefixEnd_6551121 3363873898763168442659449 := by
  unfold tailWord_6551121
  simp only [CollatzResearch.WordTrace]
  refine ⟨238939012499414934236317217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159292674999609956157544811 238939012499414934236317217)
  ·
    refine ⟨179204259374561200677237913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238939012499414934236317217 179204259374561200677237913)
    ·
      refine ⟨134403194530920900507928435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179204259374561200677237913 134403194530920900507928435)
      ·
        refine ⟨201604791796381350761892653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134403194530920900507928435 201604791796381350761892653)
        ·
          refine ⟨75601796923643006535709745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201604791796381350761892653 75601796923643006535709745)
          ·
            refine ⟨56701347692732254901782309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75601796923643006535709745 56701347692732254901782309)
            ·
              refine ⟨10631502692387297794084183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56701347692732254901782309 10631502692387297794084183)
              ·
                refine ⟨15947254038580946691126275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631502692387297794084183 15947254038580946691126275)
                ·
                  refine ⟨23920881057871420036689413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15947254038580946691126275 23920881057871420036689413)
                  ·
                    refine ⟨4485165198350891256879265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23920881057871420036689413 4485165198350891256879265)
                    ·
                      refine ⟨3363873898763168442659449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485165198350891256879265 3363873898763168442659449)
                      ·
                        rfl

theorem cell23_6551121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_6551121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551121 prefixEnd_6551121 := by exact prefixLift 6551121
  have htrace : WordTrace (prefixWord ++ tailWord_6551121) baseStart_6551121 baseEnd_6551121 := by
    simpa [prefixWord, tailWord_6551121, baseEnd_6551121] using wordTrace_append hprefix tailTrace_6551121
  have hstable : (prefixWord ++ tailWord_6551121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551121).length < 2 ^ (prefixWord ++ tailWord_6551121).sum := by decide
  have hdescent : baseEnd_6551121 < baseStart_6551121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551124 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_6551124 : Nat := 118140960795 + 6551124 * 2 ^ 59
def prefixEnd_6551124 : Nat := 4983230072969 + 3 ^ 40 * 6551124 * 2
def baseEnd_6551124 : Nat := 3363875439205131930921935

theorem tailTrace_6551124 : CollatzResearch.WordTrace tailWord_6551124 prefixEnd_6551124 3363875439205131930921935 := by
  unfold tailWord_6551124
  simp only [CollatzResearch.WordTrace]
  refine ⟨119469560959202032874338213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159292747945602710499117617 119469560959202032874338213)
  ·
    refine ⟨22400542679850381163938415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119469560959202032874338213 22400542679850381163938415)
    ·
      refine ⟨33600814019775571745907623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22400542679850381163938415 33600814019775571745907623)
      ·
        refine ⟨50401221029663357618861435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33600814019775571745907623 50401221029663357618861435)
        ·
          refine ⟨75601831544495036428292153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50401221029663357618861435 75601831544495036428292153)
          ·
            refine ⟨56701373658371277321219115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75601831544495036428292153 56701373658371277321219115)
            ·
              refine ⟨85052060487556915981828673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56701373658371277321219115 85052060487556915981828673)
              ·
                refine ⟨63789045365667686986371505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85052060487556915981828673 63789045365667686986371505)
                ·
                  refine ⟨47841784024250765239778629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63789045365667686986371505 47841784024250765239778629)
                  ·
                    refine ⟨8970334504547018482458493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47841784024250765239778629 8970334504547018482458493)
                    ·
                      refine ⟨3363875439205131930921935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970334504547018482458493 3363875439205131930921935)
                      ·
                        rfl

theorem cell23_6551124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_6551124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551124 prefixEnd_6551124 := by exact prefixLift 6551124
  have htrace : WordTrace (prefixWord ++ tailWord_6551124) baseStart_6551124 baseEnd_6551124 := by
    simpa [prefixWord, tailWord_6551124, baseEnd_6551124] using wordTrace_append hprefix tailTrace_6551124
  have hstable : (prefixWord ++ tailWord_6551124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551124).length < 2 ^ (prefixWord ++ tailWord_6551124).sum := by decide
  have hdescent : baseEnd_6551124 < baseStart_6551124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551127 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 9]
def baseStart_6551127 : Nat := 118140960795 + 6551127 * 2 ^ 59
def prefixEnd_6551127 : Nat := 4983230072969 + 3 ^ 40 * 6551127 * 2
def baseEnd_6551127 : Nat := 373764108849677268798269

theorem tailTrace_6551127 : CollatzResearch.WordTrace tailWord_6551127 prefixEnd_6551127 373764108849677268798269 := by
  unfold tailWord_6551127
  simp only [CollatzResearch.WordTrace]
  refine ⟨238939231337393197261035635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159292820891595464840690423 238939231337393197261035635)
  ·
    refine ⟨358408847006089795891553453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238939231337393197261035635 358408847006089795891553453)
    ·
      refine ⟨134403317627283673459332545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358408847006089795891553453 134403317627283673459332545)
      ·
        refine ⟨100802488220462755094499409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134403317627283673459332545 100802488220462755094499409)
        ·
          refine ⟨75601866165347066320874557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100802488220462755094499409 75601866165347066320874557)
          ·
            refine ⟨28350699812005149870327959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75601866165347066320874557 28350699812005149870327959)
            ·
              refine ⟨42526049718007724805491939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28350699812005149870327959 42526049718007724805491939)
              ·
                refine ⟨63789074577011587208237909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42526049718007724805491939 63789074577011587208237909)
                ·
                  refine ⟨373764108849677268798269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63789074577011587208237909 373764108849677268798269)
                  ·
                    rfl

theorem cell23_6551127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 9].length) (baseStart_6551127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551127 prefixEnd_6551127 := by exact prefixLift 6551127
  have htrace : WordTrace (prefixWord ++ tailWord_6551127) baseStart_6551127 baseEnd_6551127 := by
    simpa [prefixWord, tailWord_6551127, baseEnd_6551127] using wordTrace_append hprefix tailTrace_6551127
  have hstable : (prefixWord ++ tailWord_6551127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551127).length < 2 ^ (prefixWord ++ tailWord_6551127).sum := by decide
  have hdescent : baseEnd_6551127 < baseStart_6551127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551167 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_6551167 : Nat := 118140960795 + 6551167 * 2 ^ 59
def prefixEnd_6551167 : Nat := 4983230072969 + 3 ^ 40 * 6551167 * 2
def baseEnd_6551167 : Nat := 3363897518873275262684237

theorem tailTrace_6551167 : CollatzResearch.WordTrace tailWord_6551167 prefixEnd_6551167 3363897518873275262684237 := by
  unfold tailWord_6551167
  simp only [CollatzResearch.WordTrace]
  refine ⟨238940690257248284092491755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159293793504832189394994503 238940690257248284092491755)
  ·
    refine ⟨358411035385872426138737633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238940690257248284092491755 358411035385872426138737633)
    ·
      refine ⟨268808276539404319604053225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358411035385872426138737633 268808276539404319604053225)
      ·
        refine ⟨201606207404553239703039919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268808276539404319604053225 201606207404553239703039919)
        ·
          refine ⟨302409311106829859554559879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201606207404553239703039919 302409311106829859554559879)
          ·
            refine ⟨453613966660244789331839819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302409311106829859554559879 453613966660244789331839819)
            ·
              refine ⟨680420949990367183997759729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453613966660244789331839819 680420949990367183997759729)
              ·
                refine ⟨510315712492775387998319797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680420949990367183997759729 510315712492775387998319797)
                ·
                  refine ⟨47842098046197692624842481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510315712492775387998319797 47842098046197692624842481)
                  ·
                    refine ⟨35881573534648269468631861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47842098046197692624842481 35881573534648269468631861)
                    ·
                      refine ⟨3363897518873275262684237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35881573534648269468631861 3363897518873275262684237)
                      ·
                        rfl

theorem cell23_6551167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_6551167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551167 prefixEnd_6551167 := by exact prefixLift 6551167
  have htrace : WordTrace (prefixWord ++ tailWord_6551167) baseStart_6551167 baseEnd_6551167 := by
    simpa [prefixWord, tailWord_6551167, baseEnd_6551167] using wordTrace_append hprefix tailTrace_6551167
  have hstable : (prefixWord ++ tailWord_6551167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551167).length < 2 ^ (prefixWord ++ tailWord_6551167).sum := by decide
  have hdescent : baseEnd_6551167 < baseStart_6551167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551172 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6551172 : Nat := 118140960795 + 6551172 * 2 ^ 59
def prefixEnd_6551172 : Nat := 4983230072969 + 3 ^ 40 * 6551172 * 2
def baseEnd_6551172 : Nat := 3363900086276547743121715

theorem tailTrace_6551172 : CollatzResearch.WordTrace tailWord_6551172 prefixEnd_6551172 3363900086276547743121715 := by
  unfold tailWord_6551172
  simp only [CollatzResearch.WordTrace]
  refine ⟨119470436311115084973211885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159293915081486779964282513 119470436311115084973211885)
  ·
    refine ⟨44801413616668156864954457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119470436311115084973211885 44801413616668156864954457)
    ·
      refine ⟨33601060212501117648715843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44801413616668156864954457 33601060212501117648715843)
      ·
        refine ⟨50401590318751676473073765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33601060212501117648715843 50401590318751676473073765)
        ·
          refine ⟨9450298184765939338701331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50401590318751676473073765 9450298184765939338701331)
          ·
            refine ⟨14175447277148909008051997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9450298184765939338701331 14175447277148909008051997)
            ·
              refine ⟨5315792728930840878019499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14175447277148909008051997 5315792728930840878019499)
              ·
                refine ⟨7973689093396261317029249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315792728930840878019499 7973689093396261317029249)
                ·
                  refine ⟨5980266820047195987771937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7973689093396261317029249 5980266820047195987771937)
                  ·
                    refine ⟨4485200115035396990828953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980266820047195987771937 4485200115035396990828953)
                    ·
                      refine ⟨3363900086276547743121715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485200115035396990828953 3363900086276547743121715)
                      ·
                        rfl

theorem cell23_6551172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6551172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551172 prefixEnd_6551172 := by exact prefixLift 6551172
  have htrace : WordTrace (prefixWord ++ tailWord_6551172) baseStart_6551172 baseEnd_6551172 := by
    simpa [prefixWord, tailWord_6551172, baseEnd_6551172] using wordTrace_append hprefix tailTrace_6551172
  have hstable : (prefixWord ++ tailWord_6551172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551172).length < 2 ^ (prefixWord ++ tailWord_6551172).sum := by decide
  have hdescent : baseEnd_6551172 < baseStart_6551172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551245 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6551245 : Nat := 118140960795 + 6551245 * 2 ^ 59
def prefixEnd_6551245 : Nat := 4983230072969 + 3 ^ 40 * 6551245 * 2
def baseEnd_6551245 : Nat := 3363937570364325957508879

theorem tailTrace_6551245 : CollatzResearch.WordTrace tailWord_6551245 prefixEnd_6551245 3363937570364325957508879 := by
  unfold tailWord_6551245
  simp only [CollatzResearch.WordTrace]
  refine ⟨238943535150965703413831189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159295690100643802275887459 238943535150965703413831189)
  ·
    refine ⟨11200478210201517347523337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238943535150965703413831189 11200478210201517347523337)
    ·
      refine ⟨8400358657651138010642503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11200478210201517347523337 8400358657651138010642503)
      ·
        refine ⟨12600537986476707015963755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8400358657651138010642503 12600537986476707015963755)
        ·
          refine ⟨18900806979715060523945633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600537986476707015963755 18900806979715060523945633)
          ·
            refine ⟨14175605234786295392959225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18900806979715060523945633 14175605234786295392959225)
            ·
              refine ⟨10631703926089721544719419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14175605234786295392959225 10631703926089721544719419)
              ·
                refine ⟨15947555889134582317079129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10631703926089721544719419 15947555889134582317079129)
                ·
                  refine ⟨11960666916850936737809347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15947555889134582317079129 11960666916850936737809347)
                  ·
                    refine ⟨17941000375276405106714021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11960666916850936737809347 17941000375276405106714021)
                    ·
                      refine ⟨3363937570364325957508879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17941000375276405106714021 3363937570364325957508879)
                      ·
                        rfl

theorem cell23_6551245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6551245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551245 prefixEnd_6551245 := by exact prefixLift 6551245
  have htrace : WordTrace (prefixWord ++ tailWord_6551245) baseStart_6551245 baseEnd_6551245 := by
    simpa [prefixWord, tailWord_6551245, baseEnd_6551245] using wordTrace_append hprefix tailTrace_6551245
  have hstable : (prefixWord ++ tailWord_6551245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551245).length < 2 ^ (prefixWord ++ tailWord_6551245).sum := by decide
  have hdescent : baseEnd_6551245 < baseStart_6551245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551272 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6551272 : Nat := 118140960795 + 6551272 * 2 ^ 59
def prefixEnd_6551272 : Nat := 4983230072969 + 3 ^ 40 * 6551272 * 2
def baseEnd_6551272 : Nat := 1121317144780665783957085

theorem tailTrace_6551272 : CollatzResearch.WordTrace tailWord_6551272 prefixEnd_6551272 1121317144780665783957085 := by
  unfold tailWord_6551272
  simp only [CollatzResearch.WordTrace]
  refine ⟨119472259960933943512532035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159296346614578591350042713 119472259960933943512532035)
  ·
    refine ⟨179208389941400915268798053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119472259960933943512532035 179208389941400915268798053)
    ·
      refine ⟨33601573114012671612899635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179208389941400915268798053 33601573114012671612899635)
      ·
        refine ⟨50402359671019007419349453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33601573114012671612899635 50402359671019007419349453)
        ·
          refine ⟨18900884876632127782256045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50402359671019007419349453 18900884876632127782256045)
          ·
            refine ⟨7087831828737047918346017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18900884876632127782256045 7087831828737047918346017)
            ·
              refine ⟨5315873871552785938759513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7087831828737047918346017 5315873871552785938759513)
              ·
                refine ⟨3986905403664589454069635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315873871552785938759513 3986905403664589454069635)
                ·
                  refine ⟨5980358105496884181104453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986905403664589454069635 5980358105496884181104453)
                  ·
                    refine ⟨1121317144780665783957085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980358105496884181104453 1121317144780665783957085)
                    ·
                      rfl

theorem cell23_6551272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6551272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551272 prefixEnd_6551272 := by exact prefixLift 6551272
  have htrace : WordTrace (prefixWord ++ tailWord_6551272) baseStart_6551272 baseEnd_6551272 := by
    simpa [prefixWord, tailWord_6551272, baseEnd_6551272] using wordTrace_append hprefix tailTrace_6551272
  have hstable : (prefixWord ++ tailWord_6551272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551272).length < 2 ^ (prefixWord ++ tailWord_6551272).sum := by decide
  have hdescent : baseEnd_6551272 < baseStart_6551272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551278 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_6551278 : Nat := 118140960795 + 6551278 * 2 ^ 59
def prefixEnd_6551278 : Nat := 4983230072969 + 3 ^ 40 * 6551278 * 2
def baseEnd_6551278 : Nat := 3363954515225924328396227

theorem tailTrace_6551278 : CollatzResearch.WordTrace tailWord_6551278 prefixEnd_6551278 3363954515225924328396227 := by
  unfold tailWord_6551278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29868092344980768756222811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159296492506564100033188325 29868092344980768756222811)
  ·
    refine ⟨44802138517471153134334217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29868092344980768756222811 44802138517471153134334217)
    ·
      refine ⟨33601603888103364850750663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44802138517471153134334217 33601603888103364850750663)
      ·
        refine ⟨50402405832155047276125995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33601603888103364850750663 50402405832155047276125995)
        ·
          refine ⟨75603608748232570914188993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50402405832155047276125995 75603608748232570914188993)
          ·
            refine ⟨56702706561174428185641745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75603608748232570914188993 56702706561174428185641745)
            ·
              refine ⟨42527029920880821139231309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56702706561174428185641745 42527029920880821139231309)
              ·
                refine ⟨15947636220330307927211741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42527029920880821139231309 15947636220330307927211741)
                ·
                  refine ⟨5980363582623865472704403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15947636220330307927211741 5980363582623865472704403)
                  ·
                    refine ⟨8970545373935798209056605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980363582623865472704403 8970545373935798209056605)
                    ·
                      refine ⟨3363954515225924328396227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970545373935798209056605 3363954515225924328396227)
                      ·
                        rfl

theorem cell23_6551278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_6551278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551278 prefixEnd_6551278 := by exact prefixLift 6551278
  have htrace : WordTrace (prefixWord ++ tailWord_6551278) baseStart_6551278 baseEnd_6551278 := by
    simpa [prefixWord, tailWord_6551278, baseEnd_6551278] using wordTrace_append hprefix tailTrace_6551278
  have hstable : (prefixWord ++ tailWord_6551278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551278).length < 2 ^ (prefixWord ++ tailWord_6551278).sum := by decide
  have hdescent : baseEnd_6551278 < baseStart_6551278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551298 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_6551298 : Nat := 118140960795 + 6551298 * 2 ^ 59
def prefixEnd_6551298 : Nat := 4983230072969 + 3 ^ 40 * 6551298 * 2
def baseEnd_6551298 : Nat := 1121321594946338083382045

theorem tailTrace_6551298 : CollatzResearch.WordTrace tailWord_6551298 prefixEnd_6551298 1121321594946338083382045 := by
  unfold tailWord_6551298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59736367054943423366377637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159296978813182462310340365 59736367054943423366377637)
  ·
    refine ⟨11200568822801891881195807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59736367054943423366377637 11200568822801891881195807)
    ·
      refine ⟨16800853234202837821793711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200568822801891881195807 16800853234202837821793711)
      ·
        refine ⟨25201279851304256732690567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800853234202837821793711 25201279851304256732690567)
        ·
          refine ⟨37801919776956385099035851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25201279851304256732690567 37801919776956385099035851)
          ·
            refine ⟨56702879665434577648553777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37801919776956385099035851 56702879665434577648553777)
            ·
              refine ⟨42527159749075933236415333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56702879665434577648553777 42527159749075933236415333)
              ·
                refine ⟨7973842452951737481827875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42527159749075933236415333 7973842452951737481827875)
                ·
                  refine ⟨11960763679427606222741813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973842452951737481827875 11960763679427606222741813)
                  ·
                    refine ⟨1121321594946338083382045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11960763679427606222741813 1121321594946338083382045)
                    ·
                      rfl

theorem cell23_6551298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_6551298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551298 prefixEnd_6551298 := by exact prefixLift 6551298
  have htrace : WordTrace (prefixWord ++ tailWord_6551298) baseStart_6551298 baseEnd_6551298 := by
    simpa [prefixWord, tailWord_6551298, baseEnd_6551298] using wordTrace_append hprefix tailTrace_6551298
  have hstable : (prefixWord ++ tailWord_6551298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551298).length < 2 ^ (prefixWord ++ tailWord_6551298).sum := by decide
  have hdescent : baseEnd_6551298 < baseStart_6551298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551324 : List Nat := [2, 2, 3, 1, 1, 2, 12]
def baseStart_6551324 : Nat := 118140960795 + 6551324 * 2 ^ 59
def prefixEnd_6551324 : Nat := 4983230072969 + 3 ^ 40 * 6551324 * 2
def baseEnd_6551324 : Nat := 41530594263407791955815

theorem tailTrace_6551324 : CollatzResearch.WordTrace tailWord_6551324 prefixEnd_6551324 41530594263407791955815 := by
  unfold tailWord_6551324
  simp only [CollatzResearch.WordTrace]
  refine ⟨119473208258839749952978513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159297611011786333270638017 119473208258839749952978513)
  ·
    refine ⟨89604906194129812464733885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119473208258839749952978513 89604906194129812464733885)
    ·
      refine ⟨33601839822798679674275207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89604906194129812464733885 33601839822798679674275207)
      ·
        refine ⟨50402759734198019511412811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33601839822798679674275207 50402759734198019511412811)
        ·
          refine ⟨75604139601297029267119217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50402759734198019511412811 75604139601297029267119217)
          ·
            refine ⟨56703104700972771950339413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75604139601297029267119217 56703104700972771950339413)
            ·
              refine ⟨41530594263407791955815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56703104700972771950339413 41530594263407791955815)
              ·
                rfl

theorem cell23_6551324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 12].length) (baseStart_6551324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551324 prefixEnd_6551324 := by exact prefixLift 6551324
  have htrace : WordTrace (prefixWord ++ tailWord_6551324) baseStart_6551324 baseEnd_6551324 := by
    simpa [prefixWord, tailWord_6551324, baseEnd_6551324] using wordTrace_append hprefix tailTrace_6551324
  have hstable : (prefixWord ++ tailWord_6551324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551324).length < 2 ^ (prefixWord ++ tailWord_6551324).sum := by decide
  have hdescent : baseEnd_6551324 < baseStart_6551324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551345 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_6551345 : Nat := 118140960795 + 6551345 * 2 ^ 59
def prefixEnd_6551345 : Nat := 4983230072969 + 3 ^ 40 * 6551345 * 2
def baseEnd_6551345 : Nat := 1121329639476591855419473

theorem tailTrace_6551345 : CollatzResearch.WordTrace tailWord_6551345 prefixEnd_6551345 1121329639476591855419473 := by
  unfold tailWord_6551345
  simp only [CollatzResearch.WordTrace]
  refine ⟨238947182450603420492471489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159298121633735613661647659 238947182450603420492471489)
  ·
    refine ⟨179210386837952565369353617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238947182450603420492471489 179210386837952565369353617)
    ·
      refine ⟨134407790128464424027015213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179210386837952565369353617 134407790128464424027015213)
      ·
        refine ⟨50402921298174159010130705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134407790128464424027015213 50402921298174159010130705)
        ·
          refine ⟨37802190973630619257598029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50402921298174159010130705 37802190973630619257598029)
          ·
            refine ⟨14175821615111482221599261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37802190973630619257598029 14175821615111482221599261)
            ·
              refine ⟨5315933105666805833099723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14175821615111482221599261 5315933105666805833099723)
              ·
                refine ⟨7973899658500208749649585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315933105666805833099723 7973899658500208749649585)
                ·
                  refine ⟨5980424743875156562237189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7973899658500208749649585 5980424743875156562237189)
                  ·
                    refine ⟨1121329639476591855419473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980424743875156562237189 1121329639476591855419473)
                    ·
                      rfl

theorem cell23_6551345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_6551345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551345 prefixEnd_6551345 := by exact prefixLift 6551345
  have htrace : WordTrace (prefixWord ++ tailWord_6551345) baseStart_6551345 baseEnd_6551345 := by
    simpa [prefixWord, tailWord_6551345, baseEnd_6551345] using wordTrace_append hprefix tailTrace_6551345
  have hstable : (prefixWord ++ tailWord_6551345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551345).length < 2 ^ (prefixWord ++ tailWord_6551345).sum := by decide
  have hdescent : baseEnd_6551345 < baseStart_6551345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551348 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6551348 : Nat := 118140960795 + 6551348 * 2 ^ 59
def prefixEnd_6551348 : Nat := 4983230072969 + 3 ^ 40 * 6551348 * 2
def baseEnd_6551348 : Nat := 3363990458871739054520905

theorem tailTrace_6551348 : CollatzResearch.WordTrace tailWord_6551348 prefixEnd_6551348 3363990458871739054520905 := by
  unfold tailWord_6551348
  simp only [CollatzResearch.WordTrace]
  refine ⟨119473645934796276002415349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159298194579728368003220465 119473645934796276002415349)
  ·
    refine ⟨11200654306387150875226439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119473645934796276002415349 11200654306387150875226439)
    ·
      refine ⟨16800981459580726312839659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200654306387150875226439 16800981459580726312839659)
      ·
        refine ⟨25201472189371089469259489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800981459580726312839659 25201472189371089469259489)
        ·
          refine ⟨18901104142028317101944617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25201472189371089469259489 18901104142028317101944617)
          ·
            refine ⟨14175828106521237826458463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18901104142028317101944617 14175828106521237826458463)
            ·
              refine ⟨21263742159781856739687695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14175828106521237826458463 21263742159781856739687695)
              ·
                refine ⟨31895613239672785109531543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21263742159781856739687695 31895613239672785109531543)
                ·
                  refine ⟨47843419859509177664297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31895613239672785109531543 47843419859509177664297315)
                  ·
                    refine ⟨71765129789263766496445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47843419859509177664297315 71765129789263766496445973)
                    ·
                      refine ⟨3363990458871739054520905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71765129789263766496445973 3363990458871739054520905)
                      ·
                        rfl

theorem cell23_6551348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6551348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551348 prefixEnd_6551348 := by exact prefixLift 6551348
  have htrace : WordTrace (prefixWord ++ tailWord_6551348) baseStart_6551348 baseEnd_6551348 := by
    simpa [prefixWord, tailWord_6551348, baseEnd_6551348] using wordTrace_append hprefix tailTrace_6551348
  have hstable : (prefixWord ++ tailWord_6551348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551348).length < 2 ^ (prefixWord ++ tailWord_6551348).sum := by decide
  have hdescent : baseEnd_6551348 < baseStart_6551348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551351 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_6551351 : Nat := 118140960795 + 6551351 * 2 ^ 59
def prefixEnd_6551351 : Nat := 4983230072969 + 3 ^ 40 * 6551351 * 2
def baseEnd_6551351 : Nat := 3363991999313702542783391

theorem tailTrace_6551351 : CollatzResearch.WordTrace tailWord_6551351 prefixEnd_6551351 3363991999313702542783391 := by
  unfold tailWord_6551351
  simp only [CollatzResearch.WordTrace]
  refine ⟨238947401288581683517189907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159298267525721122344793271 238947401288581683517189907)
  ·
    refine ⟨358421101932872525275784861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238947401288581683517189907 358421101932872525275784861)
    ·
      refine ⟨134407913224827196978419323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358421101932872525275784861 134407913224827196978419323)
      ·
        refine ⟨201611869837240795467628985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134407913224827196978419323 201611869837240795467628985)
        ·
          refine ⟨151208902377930596600721739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201611869837240795467628985 151208902377930596600721739)
          ·
            refine ⟨226813353566895894901082609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151208902377930596600721739 226813353566895894901082609)
            ·
              refine ⟨170110015175171921175811957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226813353566895894901082609 170110015175171921175811957)
              ·
                refine ⟨15947813922672367610232371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170110015175171921175811957 15947813922672367610232371)
                ·
                  refine ⟨23921720884008551415348557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15947813922672367610232371 23921720884008551415348557)
                  ·
                    refine ⟨8970645331503206780755709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23921720884008551415348557 8970645331503206780755709)
                    ·
                      refine ⟨3363991999313702542783391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970645331503206780755709 3363991999313702542783391)
                      ·
                        rfl

theorem cell23_6551351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_6551351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551351 prefixEnd_6551351 := by exact prefixLift 6551351
  have htrace : WordTrace (prefixWord ++ tailWord_6551351) baseStart_6551351 baseEnd_6551351 := by
    simpa [prefixWord, tailWord_6551351, baseEnd_6551351] using wordTrace_append hprefix tailTrace_6551351
  have hstable : (prefixWord ++ tailWord_6551351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551351).length < 2 ^ (prefixWord ++ tailWord_6551351).sum := by decide
  have hdescent : baseEnd_6551351 < baseStart_6551351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551358 : List Nat := [4, 2, 1, 2, 2, 1, 4, 7]
def baseStart_6551358 : Nat := 118140960795 + 6551358 * 2 ^ 59
def prefixEnd_6551358 : Nat := 4983230072969 + 3 ^ 40 * 6551358 * 2
def baseEnd_6551358 : Nat := 124592429395492000570217

theorem tailTrace_6551358 : CollatzResearch.WordTrace tailWord_6551358 prefixEnd_6551358 124592429395492000570217 := by
  unfold tailWord_6551358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29868457074944540464086841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159298437733037549141796485 29868457074944540464086841)
  ·
    refine ⟨22401342806208405348065131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29868457074944540464086841 22401342806208405348065131)
    ·
      refine ⟨33602014209312608022097697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22401342806208405348065131 33602014209312608022097697)
      ·
        refine ⟨25201510656984456016573273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33602014209312608022097697 25201510656984456016573273)
        ·
          refine ⟨18901132992738342012429955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25201510656984456016573273 18901132992738342012429955)
          ·
            refine ⟨28351699489107513018644933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18901132992738342012429955 28351699489107513018644933)
            ·
              refine ⟨5315943654207658690995925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28351699489107513018644933 5315943654207658690995925)
              ·
                refine ⟨124592429395492000570217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5315943654207658690995925 124592429395492000570217)
                ·
                  rfl

theorem cell23_6551358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_6551358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551358 prefixEnd_6551358 := by exact prefixLift 6551358
  have htrace : WordTrace (prefixWord ++ tailWord_6551358) baseStart_6551358 baseEnd_6551358 := by
    simpa [prefixWord, tailWord_6551358, baseEnd_6551358] using wordTrace_append hprefix tailTrace_6551358
  have hstable : (prefixWord ++ tailWord_6551358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551358).length < 2 ^ (prefixWord ++ tailWord_6551358).sum := by decide
  have hdescent : baseEnd_6551358 < baseStart_6551358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551368 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_6551368 : Nat := 118140960795 + 6551368 * 2 ^ 59
def prefixEnd_6551368 : Nat := 4983230072969 + 3 ^ 40 * 6551368 * 2
def baseEnd_6551368 : Nat := 3364000728484828976270813

theorem tailTrace_6551368 : CollatzResearch.WordTrace tailWord_6551368 prefixEnd_6551368 3364000728484828976270813 := by
  unfold tailWord_6551368
  simp only [CollatzResearch.WordTrace]
  refine ⟨119474010664760047710279379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159298680886346730280372505 119474010664760047710279379)
  ·
    refine ⟨179211015997140071565419069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119474010664760047710279379 179211015997140071565419069)
    ·
      refine ⟨67204130998927526837032151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179211015997140071565419069 67204130998927526837032151)
      ·
        refine ⟨100806196498391290255548227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67204130998927526837032151 100806196498391290255548227)
        ·
          refine ⟨151209294747586935383322341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100806196498391290255548227 151209294747586935383322341)
          ·
            refine ⟨28351742765172550384372939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151209294747586935383322341 28351742765172550384372939)
            ·
              refine ⟨42527614147758825576559409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28351742765172550384372939 42527614147758825576559409)
              ·
                refine ⟨31895710610819119182419557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42527614147758825576559409 31895710610819119182419557)
                ·
                  refine ⟨5980445739528584846703667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31895710610819119182419557 5980445739528584846703667)
                  ·
                    refine ⟨8970668609292877270055501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980445739528584846703667 8970668609292877270055501)
                    ·
                      refine ⟨3364000728484828976270813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8970668609292877270055501 3364000728484828976270813)
                      ·
                        rfl

theorem cell23_6551368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_6551368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551368 prefixEnd_6551368 := by exact prefixLift 6551368
  have htrace : WordTrace (prefixWord ++ tailWord_6551368) baseStart_6551368 baseEnd_6551368 := by
    simpa [prefixWord, tailWord_6551368, baseEnd_6551368] using wordTrace_append hprefix tailTrace_6551368
  have hstable : (prefixWord ++ tailWord_6551368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551368).length < 2 ^ (prefixWord ++ tailWord_6551368).sum := by decide
  have hdescent : baseEnd_6551368 < baseStart_6551368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551408 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2]
def baseStart_6551408 : Nat := 118140960795 + 6551408 * 2 ^ 59
def prefixEnd_6551408 : Nat := 4983230072969 + 3 ^ 40 * 6551408 * 2
def baseEnd_6551408 : Nat := 3364021267711008819770629

theorem tailTrace_6551408 : CollatzResearch.WordTrace tailWord_6551408 prefixEnd_6551408 3364021267711008819770629 := by
  unfold tailWord_6551408
  simp only [CollatzResearch.WordTrace]
  refine ⟨119474740124687591126007439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159299653499583454834676585 119474740124687591126007439)
  ·
    refine ⟨179212110187031386689011159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119474740124687591126007439 179212110187031386689011159)
    ·
      refine ⟨268818165280547080033516739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179212110187031386689011159 268818165280547080033516739)
      ·
        refine ⟨403227247920820620050275109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268818165280547080033516739 403227247920820620050275109)
        ·
          refine ⟨75605108985153866259426583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403227247920820620050275109 75605108985153866259426583)
          ·
            refine ⟨113407663477730799389139875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75605108985153866259426583 113407663477730799389139875)
            ·
              refine ⟨170111495216596199083709813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113407663477730799389139875 170111495216596199083709813)
              ·
                refine ⟨15947952676555893664097795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170111495216596199083709813 15947952676555893664097795)
                ·
                  refine ⟨23921929014833840496146693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15947952676555893664097795 23921929014833840496146693)
                  ·
                    refine ⟨4485361690281345093027505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23921929014833840496146693 4485361690281345093027505)
                    ·
                      refine ⟨3364021267711008819770629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485361690281345093027505 3364021267711008819770629)
                      ·
                        rfl

theorem cell23_6551408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2].length) (baseStart_6551408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551408 prefixEnd_6551408 := by exact prefixLift 6551408
  have htrace : WordTrace (prefixWord ++ tailWord_6551408) baseStart_6551408 baseEnd_6551408 := by
    simpa [prefixWord, tailWord_6551408, baseEnd_6551408] using wordTrace_append hprefix tailTrace_6551408
  have hstable : (prefixWord ++ tailWord_6551408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551408).length < 2 ^ (prefixWord ++ tailWord_6551408).sum := by decide
  have hdescent : baseEnd_6551408 < baseStart_6551408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551421 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_6551421 : Nat := 118140960795 + 6551421 * 2 ^ 59
def prefixEnd_6551421 : Nat := 4983230072969 + 3 ^ 40 * 6551421 * 2
def baseEnd_6551421 : Nat := 3364027942959517268908069

theorem tailTrace_6551421 : CollatzResearch.WordTrace tailWord_6551421 prefixEnd_6551421 3364027942959517268908069 := by
  unfold tailWord_6551421
  simp only [CollatzResearch.WordTrace]
  refine ⟨238949954398328085472238117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159299969598885390314825411 238949954398328085472238117)
  ·
    refine ⟨44803116449686516026044647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238949954398328085472238117 44803116449686516026044647)
    ·
      refine ⟨67204674674529774039066971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44803116449686516026044647 67204674674529774039066971)
      ·
        refine ⟨100807012011794661058600457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67204674674529774039066971 100807012011794661058600457)
        ·
          refine ⟨75605259008845995793950343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100807012011794661058600457 75605259008845995793950343)
          ·
            refine ⟨113407888513268993690925515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75605259008845995793950343 113407888513268993690925515)
            ·
              refine ⟨170111832769903490536388273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113407888513268993690925515 170111832769903490536388273)
              ·
                refine ⟨127583874577427617902291205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170111832769903490536388273 127583874577427617902291205)
                ·
                  refine ⟨23921976483267678356679601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127583874577427617902291205 23921976483267678356679601)
                  ·
                    refine ⟨17941482362450758767509701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23921976483267678356679601 17941482362450758767509701)
                    ·
                      refine ⟨3364027942959517268908069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17941482362450758767509701 3364027942959517268908069)
                      ·
                        rfl

theorem cell23_6551421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_6551421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551421 prefixEnd_6551421 := by exact prefixLift 6551421
  have htrace : WordTrace (prefixWord ++ tailWord_6551421) baseStart_6551421 baseEnd_6551421 := by
    simpa [prefixWord, tailWord_6551421, baseEnd_6551421] using wordTrace_append hprefix tailTrace_6551421
  have hstable : (prefixWord ++ tailWord_6551421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551421).length < 2 ^ (prefixWord ++ tailWord_6551421).sum := by decide
  have hdescent : baseEnd_6551421 < baseStart_6551421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551461 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_6551461 : Nat := 118140960795 + 6551461 * 2 ^ 59
def prefixEnd_6551461 : Nat := 4983230072969 + 3 ^ 40 * 6551461 * 2
def baseEnd_6551461 : Nat := 1121349494061899037469295

theorem tailTrace_6551461 : CollatzResearch.WordTrace tailWord_6551461 prefixEnd_6551461 1121349494061899037469295 := by
  unfold tailWord_6551461
  simp only [CollatzResearch.WordTrace]
  refine ⟨238951413318183172303694237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159300942212122114869129491 238951413318183172303694237)
  ·
    refine ⟨89606779994318689613885339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238951413318183172303694237 89606779994318689613885339)
    ·
      refine ⟨134410169991478034420828009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89606779994318689613885339 134410169991478034420828009)
      ·
        refine ⟨100807627493608525815621007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134410169991478034420828009 100807627493608525815621007)
        ·
          refine ⟨151211441240412788723431511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100807627493608525815621007 151211441240412788723431511)
          ·
            refine ⟨226817161860619183085147267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151211441240412788723431511 226817161860619183085147267)
            ·
              refine ⟨340225742790928774627720901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226817161860619183085147267 340225742790928774627720901)
              ·
                refine ⟨63792326773299145242697669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340225742790928774627720901 63792326773299145242697669)
                ·
                  refine ⟨11961061269993589733005813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63792326773299145242697669 11961061269993589733005813)
                  ·
                    refine ⟨1121349494061899037469295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11961061269993589733005813 1121349494061899037469295)
                    ·
                      rfl

theorem cell23_6551461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_6551461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551461 prefixEnd_6551461 := by exact prefixLift 6551461
  have htrace : WordTrace (prefixWord ++ tailWord_6551461) baseStart_6551461 baseEnd_6551461 := by
    simpa [prefixWord, tailWord_6551461, baseEnd_6551461] using wordTrace_append hprefix tailTrace_6551461
  have hstable : (prefixWord ++ tailWord_6551461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551461).length < 2 ^ (prefixWord ++ tailWord_6551461).sum := by decide
  have hdescent : baseEnd_6551461 < baseStart_6551461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551498 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_6551498 : Nat := 118140960795 + 6551498 * 2 ^ 59
def prefixEnd_6551498 : Nat := 4983230072969 + 3 ^ 40 * 6551498 * 2
def baseEnd_6551498 : Nat := 3364067480969913467645215

theorem tailTrace_6551498 : CollatzResearch.WordTrace tailWord_6551498 prefixEnd_6551498 3364067480969913467645215 := by
  unfold tailWord_6551498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59738190704762281905697787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159301841879366085081860765 59738190704762281905697787)
  ·
    refine ⟨89607286057143422858546681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59738190704762281905697787 89607286057143422858546681)
    ·
      refine ⟨67205464542857567143910011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89607286057143422858546681 67205464542857567143910011)
      ·
        refine ⟨100808196814286350715865017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67205464542857567143910011 100808196814286350715865017)
        ·
          refine ⟨75606147610714763036898763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100808196814286350715865017 75606147610714763036898763)
          ·
            refine ⟨113409221416072144555348145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75606147610714763036898763 113409221416072144555348145)
            ·
              refine ⟨85056916062054108416511109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113409221416072144555348145 85056916062054108416511109)
              ·
                refine ⟨15948171761635145328095833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85056916062054108416511109 15948171761635145328095833)
                ·
                  refine ⟨11961128821226358996071875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15948171761635145328095833 11961128821226358996071875)
                  ·
                    refine ⟨17941693231839538494107813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11961128821226358996071875 17941693231839538494107813)
                    ·
                      refine ⟨3364067480969913467645215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17941693231839538494107813 3364067480969913467645215)
                      ·
                        rfl

theorem cell23_6551498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_6551498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551498 prefixEnd_6551498 := by exact prefixLift 6551498
  have htrace : WordTrace (prefixWord ++ tailWord_6551498) baseStart_6551498 baseEnd_6551498 := by
    simpa [prefixWord, tailWord_6551498, baseEnd_6551498] using wordTrace_append hprefix tailTrace_6551498
  have hstable : (prefixWord ++ tailWord_6551498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551498).length < 2 ^ (prefixWord ++ tailWord_6551498).sum := by decide
  have hdescent : baseEnd_6551498 < baseStart_6551498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551511 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_6551511 : Nat := 118140960795 + 6551511 * 2 ^ 59
def prefixEnd_6551511 : Nat := 4983230072969 + 3 ^ 40 * 6551511 * 2
def baseEnd_6551511 : Nat := 3364074156218421916782655

theorem tailTrace_6551511 : CollatzResearch.WordTrace tailWord_6551511 prefixEnd_6551511 3364074156218421916782655 := by
  unfold tailWord_6551511
  simp only [CollatzResearch.WordTrace]
  refine ⟨238953236968002030843014387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159302157978668020562009591 238953236968002030843014387)
  ·
    refine ⟨358429855452003046264521581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238953236968002030843014387 358429855452003046264521581)
    ·
      refine ⟨134411195794501142349195593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358429855452003046264521581 134411195794501142349195593)
      ·
        refine ⟨100808396845875856761896695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134411195794501142349195593 100808396845875856761896695)
        ·
          refine ⟨151212595268813785142845043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100808396845875856761896695 151212595268813785142845043)
          ·
            refine ⟨226818892903220677714267565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151212595268813785142845043 226818892903220677714267565)
            ·
              refine ⟨85057084838707754142850337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226818892903220677714267565 85057084838707754142850337)
              ·
                refine ⟨63792813629030815607137753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85057084838707754142850337 63792813629030815607137753)
                ·
                  refine ⟨47844610221773111705353315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63792813629030815607137753 47844610221773111705353315)
                  ·
                    refine ⟨71766915332659667558029973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47844610221773111705353315 71766915332659667558029973)
                    ·
                      refine ⟨3364074156218421916782655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71766915332659667558029973 3364074156218421916782655)
                      ·
                        rfl

theorem cell23_6551511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_6551511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551511 prefixEnd_6551511 := by exact prefixLift 6551511
  have htrace : WordTrace (prefixWord ++ tailWord_6551511) baseStart_6551511 baseEnd_6551511 := by
    simpa [prefixWord, tailWord_6551511, baseEnd_6551511] using wordTrace_append hprefix tailTrace_6551511
  have hstable : (prefixWord ++ tailWord_6551511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551511).length < 2 ^ (prefixWord ++ tailWord_6551511).sum := by decide
  have hdescent : baseEnd_6551511 < baseStart_6551511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551559 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 1, 4]
def baseStart_6551559 : Nat := 118140960795 + 6551559 * 2 ^ 59
def prefixEnd_6551559 : Nat := 4983230072969 + 3 ^ 40 * 6551559 * 2
def baseEnd_6551559 : Nat := 1121366267763279242994145

theorem tailTrace_6551559 : CollatzResearch.WordTrace tailWord_6551559 prefixEnd_6551559 1121366267763279242994145 := by
  unfold tailWord_6551559
  simp only [CollatzResearch.WordTrace]
  refine ⟨238954987671828135040761731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159303325114552090027174487 238954987671828135040761731)
  ·
    refine ⟨358432481507742202561142597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238954987671828135040761731 358432481507742202561142597)
    ·
      refine ⟨67206090282701662980214237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358432481507742202561142597 67206090282701662980214237)
      ·
        refine ⟨25202283856013123617580339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67206090282701662980214237 25202283856013123617580339)
        ·
          refine ⟨37803425784019685426370509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25202283856013123617580339 37803425784019685426370509)
          ·
            refine ⟨14176284669007382034888941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37803425784019685426370509 14176284669007382034888941)
            ·
              refine ⟨5316106750877768263083353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14176284669007382034888941 5316106750877768263083353)
              ·
                refine ⟨3987080063158326197312515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316106750877768263083353 3987080063158326197312515)
                ·
                  refine ⟨5980620094737489295968773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987080063158326197312515 5980620094737489295968773)
                  ·
                    refine ⟨1121366267763279242994145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980620094737489295968773 1121366267763279242994145)
                    ·
                      rfl

theorem cell23_6551559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_6551559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551559 prefixEnd_6551559 := by exact prefixLift 6551559
  have htrace : WordTrace (prefixWord ++ tailWord_6551559) baseStart_6551559 baseEnd_6551559 := by
    simpa [prefixWord, tailWord_6551559, baseEnd_6551559] using wordTrace_append hprefix tailTrace_6551559
  have hstable : (prefixWord ++ tailWord_6551559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551559).length < 2 ^ (prefixWord ++ tailWord_6551559).sum := by decide
  have hdescent : baseEnd_6551559 < baseStart_6551559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551561 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_6551561 : Nat := 118140960795 + 6551561 * 2 ^ 59
def prefixEnd_6551561 : Nat := 4983230072969 + 3 ^ 40 * 6551561 * 2
def baseEnd_6551561 : Nat := 3364099830251146721157425

theorem tailTrace_6551561 : CollatzResearch.WordTrace tailWord_6551561 prefixEnd_6551561 3364099830251146721157425 := by
  unfold tailWord_6551561
  simp only [CollatzResearch.WordTrace]
  refine ⟨238955060617820889382334537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159303373745213926254889691 238955060617820889382334537)
  ·
    refine ⟨179216295463365667036750903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238955060617820889382334537 179216295463365667036750903)
    ·
      refine ⟨268824443195048500555126355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179216295463365667036750903 268824443195048500555126355)
      ·
        refine ⟨403236664792572750832689533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268824443195048500555126355 403236664792572750832689533)
        ·
          refine ⟨151213749297214781562258575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403236664792572750832689533 151213749297214781562258575)
          ·
            refine ⟨226820623945822172343387863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151213749297214781562258575 226820623945822172343387863)
            ·
              refine ⟨340230935918733258515081795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226820623945822172343387863 340230935918733258515081795)
              ·
                refine ⟨510346403878099887772622693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340230935918733258515081795 510346403878099887772622693)
                ·
                  refine ⟨95689950727143728957366755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510346403878099887772622693 95689950727143728957366755)
                  ·
                    refine ⟨143534926090715593436050133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95689950727143728957366755 143534926090715593436050133)
                    ·
                      refine ⟨3364099830251146721157425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143534926090715593436050133 3364099830251146721157425)
                      ·
                        rfl

theorem cell23_6551561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_6551561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551561 prefixEnd_6551561 := by exact prefixLift 6551561
  have htrace : WordTrace (prefixWord ++ tailWord_6551561) baseStart_6551561 baseEnd_6551561 := by
    simpa [prefixWord, tailWord_6551561, baseEnd_6551561] using wordTrace_append hprefix tailTrace_6551561
  have hstable : (prefixWord ++ tailWord_6551561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551561).length < 2 ^ (prefixWord ++ tailWord_6551561).sum := by decide
  have hdescent : baseEnd_6551561 < baseStart_6551561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551585 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_6551585 : Nat := 118140960795 + 6551585 * 2 ^ 59
def prefixEnd_6551585 : Nat := 4983230072969 + 3 ^ 40 * 6551585 * 2
def baseEnd_6551585 : Nat := 1121370717928951542419105

theorem tailTrace_6551585 : CollatzResearch.WordTrace tailWord_6551585 prefixEnd_6551585 1121370717928951542419105 := by
  unfold tailWord_6551585
  simp only [CollatzResearch.WordTrace]
  refine ⟨238955935969733941481208209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159303957313155960987472139 238955935969733941481208209)
  ·
    refine ⟨179216951977300456110906157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238955935969733941481208209 179216951977300456110906157)
    ·
      refine ⟨67206356991487671041589809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179216951977300456110906157 67206356991487671041589809)
      ·
        refine ⟨50404767743615753281192357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67206356991487671041589809 50404767743615753281192357)
        ·
          refine ⟨9450893951927953740223567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50404767743615753281192357 9450893951927953740223567)
          ·
            refine ⟨14176340927891930610335351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9450893951927953740223567 14176340927891930610335351)
            ·
              refine ⟨21264511391837895915503027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14176340927891930610335351 21264511391837895915503027)
              ·
                refine ⟨31896767087756843873254541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21264511391837895915503027 31896767087756843873254541)
                ·
                  refine ⟨11961287657908816452470453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31896767087756843873254541 11961287657908816452470453)
                  ·
                    refine ⟨1121370717928951542419105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11961287657908816452470453 1121370717928951542419105)
                    ·
                      rfl

theorem cell23_6551585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_6551585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551585 prefixEnd_6551585 := by exact prefixLift 6551585
  have htrace : WordTrace (prefixWord ++ tailWord_6551585) baseStart_6551585 baseEnd_6551585 := by
    simpa [prefixWord, tailWord_6551585, baseEnd_6551585] using wordTrace_append hprefix tailTrace_6551585
  have hstable : (prefixWord ++ tailWord_6551585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551585).length < 2 ^ (prefixWord ++ tailWord_6551585).sum := by decide
  have hdescent : baseEnd_6551585 < baseStart_6551585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551602 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_6551602 : Nat := 118140960795 + 6551602 * 2 ^ 59
def prefixEnd_6551602 : Nat := 4983230072969 + 3 ^ 40 * 6551602 * 2
def baseEnd_6551602 : Nat := 1121373627652660353581579

theorem tailTrace_6551602 : CollatzResearch.WordTrace tailWord_6551602 prefixEnd_6551602 1121373627652660353581579 := by
  unfold tailWord_6551602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59739139002668088346144265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159304370673781568923051373 59739139002668088346144265)
  ·
    refine ⟨44804354252001066259608199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59739139002668088346144265 44804354252001066259608199)
    ·
      refine ⟨67206531378001599389412299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44804354252001066259608199 67206531378001599389412299)
      ·
        refine ⟨100809797067002399084118449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67206531378001599389412299 100809797067002399084118449)
        ·
          refine ⟨75607347800251799313088837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100809797067002399084118449 75607347800251799313088837)
          ·
            refine ⟨14176377712547212371204157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75607347800251799313088837 14176377712547212371204157)
            ·
              refine ⟨5316141642205204639201559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14176377712547212371204157 5316141642205204639201559)
              ·
                refine ⟨7974212463307806958802339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316141642205204639201559 7974212463307806958802339)
                ·
                  refine ⟨11961318694961710438203509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974212463307806958802339 11961318694961710438203509)
                  ·
                    refine ⟨1121373627652660353581579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11961318694961710438203509 1121373627652660353581579)
                    ·
                      rfl

theorem cell23_6551602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_6551602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551602 prefixEnd_6551602 := by exact prefixLift 6551602
  have htrace : WordTrace (prefixWord ++ tailWord_6551602) baseStart_6551602 baseEnd_6551602 := by
    simpa [prefixWord, tailWord_6551602, baseEnd_6551602] using wordTrace_append hprefix tailTrace_6551602
  have hstable : (prefixWord ++ tailWord_6551602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551602).length < 2 ^ (prefixWord ++ tailWord_6551602).sum := by decide
  have hdescent : baseEnd_6551602 < baseStart_6551602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551605 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_6551605 : Nat := 118140960795 + 6551605 * 2 ^ 59
def prefixEnd_6551605 : Nat := 4983230072969 + 3 ^ 40 * 6551605 * 2
def baseEnd_6551605 : Nat := 3364122423399944549007223

theorem tailTrace_6551605 : CollatzResearch.WordTrace tailWord_6551605 prefixEnd_6551605 3364122423399944549007223 := by
  unfold tailWord_6551605
  simp only [CollatzResearch.WordTrace]
  refine ⟨238956665429661484896936269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159304443619774323264624179 238956665429661484896936269)
  ·
    refine ⟨89608749536123056836351101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238956665429661484896936269 89608749536123056836351101)
    ·
      refine ⟨33603281076046146313631663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89608749536123056836351101 33603281076046146313631663)
      ·
        refine ⟨50404921614069219470447495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33603281076046146313631663 50404921614069219470447495)
        ·
          refine ⟨75607382421103829205671243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50404921614069219470447495 75607382421103829205671243)
          ·
            refine ⟨113411073631655743808506865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75607382421103829205671243 113411073631655743808506865)
            ·
              refine ⟨85058305223741807856380149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113411073631655743808506865 85058305223741807856380149)
              ·
                refine ⟨7974216114725794486535639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85058305223741807856380149 7974216114725794486535639)
                ·
                  refine ⟨11961324172088691729803459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974216114725794486535639 11961324172088691729803459)
                  ·
                    refine ⟨17941986258133037594705189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11961324172088691729803459 17941986258133037594705189)
                    ·
                      refine ⟨3364122423399944549007223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17941986258133037594705189 3364122423399944549007223)
                      ·
                        rfl

theorem cell23_6551605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_6551605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551605 prefixEnd_6551605 := by exact prefixLift 6551605
  have htrace : WordTrace (prefixWord ++ tailWord_6551605) baseStart_6551605 baseEnd_6551605 := by
    simpa [prefixWord, tailWord_6551605, baseEnd_6551605] using wordTrace_append hprefix tailTrace_6551605
  have hstable : (prefixWord ++ tailWord_6551605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551605).length < 2 ^ (prefixWord ++ tailWord_6551605).sum := by decide
  have hdescent : baseEnd_6551605 < baseStart_6551605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551615 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 2, 4]
def baseStart_6551615 : Nat := 118140960795 + 6551615 * 2 ^ 59
def prefixEnd_6551615 : Nat := 4983230072969 + 3 ^ 40 * 6551615 * 2
def baseEnd_6551615 : Nat := 1121375852735496503294059

theorem tailTrace_6551615 : CollatzResearch.WordTrace tailWord_6551615 prefixEnd_6551615 1121375852735496503294059 := by
  unfold tailWord_6551615
  simp only [CollatzResearch.WordTrace]
  refine ⟨238957030159625256604800299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159304686773083504403200199 238957030159625256604800299)
  ·
    refine ⟨358435545239437884907200449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238957030159625256604800299 358435545239437884907200449)
    ·
      refine ⟨268826658929578413680400337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358435545239437884907200449 268826658929578413680400337)
      ·
        refine ⟨201619994197183810260300253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268826658929578413680400337 201619994197183810260300253)
        ·
          refine ⟨75607497823943928847612595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201619994197183810260300253 75607497823943928847612595)
          ·
            refine ⟨113411246735915893271418893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75607497823943928847612595 113411246735915893271418893)
            ·
              refine ⟨42529217525968459976782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113411246735915893271418893 42529217525968459976782085)
              ·
                refine ⟨7974228286119086245646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42529217525968459976782085 7974228286119086245646641)
                ·
                  refine ⟨5980671214589314684234981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7974228286119086245646641 5980671214589314684234981)
                  ·
                    refine ⟨1121375852735496503294059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980671214589314684234981 1121375852735496503294059)
                    ·
                      rfl

theorem cell23_6551615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_6551615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551615 prefixEnd_6551615 := by exact prefixLift 6551615
  have htrace : WordTrace (prefixWord ++ tailWord_6551615) baseStart_6551615 baseEnd_6551615 := by
    simpa [prefixWord, tailWord_6551615, baseEnd_6551615] using wordTrace_append hprefix tailTrace_6551615
  have hstable : (prefixWord ++ tailWord_6551615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551615).length < 2 ^ (prefixWord ++ tailWord_6551615).sum := by decide
  have hdescent : baseEnd_6551615 < baseStart_6551615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551616 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 1, 1, 3]
def baseStart_6551616 : Nat := 118140960795 + 6551616 * 2 ^ 59
def prefixEnd_6551616 : Nat := 4983230072969 + 3 ^ 40 * 6551616 * 2
def baseEnd_6551616 : Nat := 3364128071687144005969673

theorem tailTrace_6551616 : CollatzResearch.WordTrace tailWord_6551616 prefixEnd_6551616 3364128071687144005969673 := by
  unfold tailWord_6551616
  simp only [CollatzResearch.WordTrace]
  refine ⟨119478533316310816887793351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159304711088414422517057801 119478533316310816887793351)
  ·
    refine ⟨179217799974466225331690027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119478533316310816887793351 179217799974466225331690027)
    ·
      refine ⟨268826699961699337997535041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179217799974466225331690027 268826699961699337997535041)
      ·
        refine ⟨201620024971274503498151281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268826699961699337997535041 201620024971274503498151281)
        ·
          refine ⟨151215018728455877623613461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201620024971274503498151281 151215018728455877623613461)
          ·
            refine ⟨7088204002896369263606881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151215018728455877623613461 7088204002896369263606881)
            ·
              refine ⟨5316153002172276947705161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088204002896369263606881 5316153002172276947705161)
              ·
                refine ⟨3987114751629207710778871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316153002172276947705161 3987114751629207710778871)
                ·
                  refine ⟨5980672127443811566168307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987114751629207710778871 5980672127443811566168307)
                  ·
                    refine ⟨8971008191165717349252461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980672127443811566168307 8971008191165717349252461)
                    ·
                      refine ⟨3364128071687144005969673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971008191165717349252461 3364128071687144005969673)
                      ·
                        rfl

theorem cell23_6551616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_6551616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551616 prefixEnd_6551616 := by exact prefixLift 6551616
  have htrace : WordTrace (prefixWord ++ tailWord_6551616) baseStart_6551616 baseEnd_6551616 := by
    simpa [prefixWord, tailWord_6551616, baseEnd_6551616] using wordTrace_append hprefix tailTrace_6551616
  have hstable : (prefixWord ++ tailWord_6551616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551616).length < 2 ^ (prefixWord ++ tailWord_6551616).sum := by decide
  have hdescent : baseEnd_6551616 < baseStart_6551616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551622 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6551622 : Nat := 118140960795 + 6551622 * 2 ^ 59
def prefixEnd_6551622 : Nat := 4983230072969 + 3 ^ 40 * 6551622 * 2
def baseEnd_6551622 : Nat := 3364131152571070982494645

theorem tailTrace_6551622 : CollatzResearch.WordTrace tailWord_6551622 prefixEnd_6551622 3364131152571070982494645 := by
  unfold tailWord_6551622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467415170956246775009535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159304856980399931200203413 7467415170956246775009535)
  ·
    refine ⟨11201122756434370162514303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7467415170956246775009535 11201122756434370162514303)
    ·
      refine ⟨16801684134651555243771455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11201122756434370162514303 16801684134651555243771455)
      ·
        refine ⟨25202526201977332865657183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16801684134651555243771455 25202526201977332865657183)
        ·
          refine ⟨37803789302965999298485775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25202526201977332865657183 37803789302965999298485775)
          ·
            refine ⟨56705683954448998947728663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37803789302965999298485775 56705683954448998947728663)
            ·
              refine ⟨85058525931673498421592995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56705683954448998947728663 85058525931673498421592995)
              ·
                refine ⟨127587788897510247632389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85058525931673498421592995 127587788897510247632389493)
                ·
                  refine ⟨11961355209141585715536515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127587788897510247632389493 11961355209141585715536515)
                  ·
                    refine ⟨17942032813712378573304773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11961355209141585715536515 17942032813712378573304773)
                    ·
                      refine ⟨3364131152571070982494645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17942032813712378573304773 3364131152571070982494645)
                      ·
                        rfl

theorem cell23_6551622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6551622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551622 prefixEnd_6551622 := by exact prefixLift 6551622
  have htrace : WordTrace (prefixWord ++ tailWord_6551622) baseStart_6551622 baseEnd_6551622 := by
    simpa [prefixWord, tailWord_6551622, baseEnd_6551622] using wordTrace_append hprefix tailTrace_6551622
  have hstable : (prefixWord ++ tailWord_6551622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551622).length < 2 ^ (prefixWord ++ tailWord_6551622).sum := by decide
  have hdescent : baseEnd_6551622 < baseStart_6551622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551628 : List Nat := [2, 2, 1, 3, 1, 1, 5, 8]
def baseStart_6551628 : Nat := 118140960795 + 6551628 * 2 ^ 59
def prefixEnd_6551628 : Nat := 4983230072969 + 3 ^ 40 * 6551628 * 2
def baseEnd_6551628 : Nat := 124597564202036961445171

theorem tailTrace_6551628 : CollatzResearch.WordTrace tailWord_6551628 prefixEnd_6551628 124597564202036961445171 := by
  unfold tailWord_6551628
  simp only [CollatzResearch.WordTrace]
  refine ⟨119478752154289079912511769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159305002872385439883349025 119478752154289079912511769)
  ·
    refine ⟨89609064115716809934383827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119478752154289079912511769 89609064115716809934383827)
    ·
      refine ⟨134413596173575214901575741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89609064115716809934383827 134413596173575214901575741)
      ·
        refine ⟨50405098565090705588090903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134413596173575214901575741 50405098565090705588090903)
        ·
          refine ⟨75607647847636058382136355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50405098565090705588090903 75607647847636058382136355)
          ·
            refine ⟨113411471771454087573204533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75607647847636058382136355 113411471771454087573204533)
            ·
              refine ⟨10632325478573820709987925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113411471771454087573204533 10632325478573820709987925)
              ·
                refine ⟨124597564202036961445171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10632325478573820709987925 124597564202036961445171)
                ·
                  rfl

theorem cell23_6551628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 8].length) (baseStart_6551628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551628 prefixEnd_6551628 := by exact prefixLift 6551628
  have htrace : WordTrace (prefixWord ++ tailWord_6551628) baseStart_6551628 baseEnd_6551628 := by
    simpa [prefixWord, tailWord_6551628, baseEnd_6551628] using wordTrace_append hprefix tailTrace_6551628
  have hstable : (prefixWord ++ tailWord_6551628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551628).length < 2 ^ (prefixWord ++ tailWord_6551628).sum := by decide
  have hdescent : baseEnd_6551628 < baseStart_6551628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551655 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_6551655 : Nat := 118140960795 + 6551655 * 2 ^ 59
def prefixEnd_6551655 : Nat := 4983230072969 + 3 ^ 40 * 6551655 * 2
def baseEnd_6551655 : Nat := 3364148097432669353381993

theorem tailTrace_6551655 : CollatzResearch.WordTrace tailWord_6551655 prefixEnd_6551655 3364148097432669353381993 := by
  unfold tailWord_6551655
  simp only [CollatzResearch.WordTrace]
  refine ⟨238958489079480343436256419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159305659386320228957504279 238958489079480343436256419)
  ·
    refine ⟨358437733619220515154384629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238958489079480343436256419 358437733619220515154384629)
    ·
      refine ⟨33603537526801923295723559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 358437733619220515154384629 33603537526801923295723559)
      ·
        refine ⟨50405306290202884943585339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33603537526801923295723559 50405306290202884943585339)
        ·
          refine ⟨75607959435304327415378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50405306290202884943585339 75607959435304327415378009)
          ·
            refine ⟨56705969576478245561533507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75607959435304327415378009 56705969576478245561533507)
            ·
              refine ⟨85058954364717368342300261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56705969576478245561533507 85058954364717368342300261)
              ·
                refine ⟨15948553943384506564181299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85058954364717368342300261 15948553943384506564181299)
                ·
                  refine ⟨23922830915076759846271949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15948553943384506564181299 23922830915076759846271949)
                  ·
                    refine ⟨8971061593153784942351981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23922830915076759846271949 8971061593153784942351981)
                    ·
                      refine ⟨3364148097432669353381993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971061593153784942351981 3364148097432669353381993)
                      ·
                        rfl

theorem cell23_6551655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_6551655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551655 prefixEnd_6551655 := by exact prefixLift 6551655
  have htrace : WordTrace (prefixWord ++ tailWord_6551655) baseStart_6551655 baseEnd_6551655 := by
    simpa [prefixWord, tailWord_6551655, baseEnd_6551655] using wordTrace_append hprefix tailTrace_6551655
  have hstable : (prefixWord ++ tailWord_6551655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551655).length < 2 ^ (prefixWord ++ tailWord_6551655).sum := by decide
  have hdescent : baseEnd_6551655 < baseStart_6551655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551689 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 2, 1, 3]
def baseStart_6551689 : Nat := 118140960795 + 6551689 * 2 ^ 59
def prefixEnd_6551689 : Nat := 4983230072969 + 3 ^ 40 * 6551689 * 2
def baseEnd_6551689 : Nat := 3364165555774922220356837

theorem tailTrace_6551689 : CollatzResearch.WordTrace tailWord_6551689 prefixEnd_6551689 3364165555774922220356837 := by
  unfold tailWord_6551689
  simp only [CollatzResearch.WordTrace]
  refine ⟨238959729161357167242994121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159306486107571444828662747 238959729161357167242994121)
  ·
    refine ⟨179219796871017875432245591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238959729161357167242994121 179219796871017875432245591)
    ·
      refine ⟨268829695306526813148368387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179219796871017875432245591 268829695306526813148368387)
      ·
        refine ⟨403244542959790219722552581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268829695306526813148368387 403244542959790219722552581)
        ·
          refine ⟨75608351804960666197978609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403244542959790219722552581 75608351804960666197978609)
          ·
            refine ⟨56706263853720499648483957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75608351804960666197978609 56706263853720499648483957)
            ·
              refine ⟨5316212236286296842045371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56706263853720499648483957 5316212236286296842045371)
              ·
                refine ⟨7974318354429445263068057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316212236286296842045371 7974318354429445263068057)
                ·
                  refine ⟨5980738765822083947301043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7974318354429445263068057 5980738765822083947301043)
                  ·
                    refine ⟨8971108148733125920951565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980738765822083947301043 8971108148733125920951565)
                    ·
                      refine ⟨3364165555774922220356837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971108148733125920951565 3364165555774922220356837)
                      ·
                        rfl

theorem cell23_6551689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 1, 3].length) (baseStart_6551689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551689 prefixEnd_6551689 := by exact prefixLift 6551689
  have htrace : WordTrace (prefixWord ++ tailWord_6551689) baseStart_6551689 baseEnd_6551689 := by
    simpa [prefixWord, tailWord_6551689, baseEnd_6551689] using wordTrace_append hprefix tailTrace_6551689
  have hstable : (prefixWord ++ tailWord_6551689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551689).length < 2 ^ (prefixWord ++ tailWord_6551689).sum := by decide
  have hdescent : baseEnd_6551689 < baseStart_6551689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551735 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 7]
def baseStart_6551735 : Nat := 118140960795 + 6551735 * 2 ^ 59
def prefixEnd_6551735 : Nat := 4983230072969 + 3 ^ 40 * 6551735 * 2
def baseEnd_6551735 : Nat := 373798797320558782264625

theorem tailTrace_6551735 : CollatzResearch.WordTrace tailWord_6551735 prefixEnd_6551735 373798797320558782264625 := by
  unfold tailWord_6551735
  simp only [CollatzResearch.WordTrace]
  refine ⟨238961406919190517099168659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159307604612793678066112439 238961406919190517099168659)
  ·
    refine ⟨358442110378785775648752989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238961406919190517099168659 358442110378785775648752989)
    ·
      refine ⟨134415791392044665868282371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358442110378785775648752989 134415791392044665868282371)
      ·
        refine ⟨201623687088066998802423557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134415791392044665868282371 201623687088066998802423557)
        ·
          refine ⟨37804441329012562275454417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201623687088066998802423557 37804441329012562275454417)
          ·
            refine ⟨28353330996759421706590813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37804441329012562275454417 28353330996759421706590813)
            ·
              refine ⟨10632499123784783139971555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28353330996759421706590813 10632499123784783139971555)
              ·
                refine ⟨15948748685677174709957333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10632499123784783139971555 15948748685677174709957333)
                ·
                  refine ⟨373798797320558782264625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15948748685677174709957333 373798797320558782264625)
                  ·
                    rfl

theorem cell23_6551735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 7].length) (baseStart_6551735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551735 prefixEnd_6551735 := by exact prefixLift 6551735
  have htrace : WordTrace (prefixWord ++ tailWord_6551735) baseStart_6551735 baseEnd_6551735 := by
    simpa [prefixWord, tailWord_6551735, baseEnd_6551735] using wordTrace_append hprefix tailTrace_6551735
  have hstable : (prefixWord ++ tailWord_6551735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551735).length < 2 ^ (prefixWord ++ tailWord_6551735).sum := by decide
  have hdescent : baseEnd_6551735 < baseStart_6551735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551802 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_6551802 : Nat := 118140960795 + 6551802 * 2 ^ 59
def prefixEnd_6551802 : Nat := 4983230072969 + 3 ^ 40 * 6551802 * 2
def baseEnd_6551802 : Nat := 3364223579088880278243817

theorem tailTrace_6551802 : CollatzResearch.WordTrace tailWord_6551802 prefixEnd_6551802 3364223579088880278243817 := by
  unfold tailWord_6551802
  simp only [CollatzResearch.WordTrace]
  refine ⟨59740962652486946885464415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159309233739965191694571773 59740962652486946885464415)
  ·
    refine ⟨89611443978730420328196623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59740962652486946885464415 89611443978730420328196623)
    ·
      refine ⟨134417165968095630492294935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89611443978730420328196623 134417165968095630492294935)
      ·
        refine ⟨201625748952143445738442403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134417165968095630492294935 201625748952143445738442403)
        ·
          refine ⟨302438623428215168607663605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201625748952143445738442403 302438623428215168607663605)
          ·
            refine ⟨28353620946395172056968463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302438623428215168607663605 28353620946395172056968463)
            ·
              refine ⟨42530431419592758085452695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28353620946395172056968463 42530431419592758085452695)
              ·
                refine ⟨63795647129389137128179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42530431419592758085452695 63795647129389137128179043)
                ·
                  refine ⟨95693470694083705692268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63795647129389137128179043 95693470694083705692268565)
                  ·
                    refine ⟨4485631438785173704325089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95693470694083705692268565 4485631438785173704325089)
                    ·
                      refine ⟨3364223579088880278243817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485631438785173704325089 3364223579088880278243817)
                      ·
                        rfl

theorem cell23_6551802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_6551802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551802 prefixEnd_6551802 := by exact prefixLift 6551802
  have htrace : WordTrace (prefixWord ++ tailWord_6551802) baseStart_6551802 baseEnd_6551802 := by
    simpa [prefixWord, tailWord_6551802, baseEnd_6551802] using wordTrace_append hprefix tailTrace_6551802
  have hstable : (prefixWord ++ tailWord_6551802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551802).length < 2 ^ (prefixWord ++ tailWord_6551802).sum := by decide
  have hdescent : baseEnd_6551802 < baseStart_6551802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551822 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6551822 : Nat := 118140960795 + 6551822 * 2 ^ 59
def prefixEnd_6551822 : Nat := 4983230072969 + 3 ^ 40 * 6551822 * 2
def baseEnd_6551822 : Nat := 3364233848701970199993725

theorem tailTrace_6551822 : CollatzResearch.WordTrace tailWord_6551822 prefixEnd_6551822 3364233848701970199993725 := by
  unfold tailWord_6551822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870572508734416369698215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159309720046583553971723813 29870572508734416369698215)
  ·
    refine ⟨44805858763101624554547323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29870572508734416369698215 44805858763101624554547323)
    ·
      refine ⟨67208788144652436831820985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44805858763101624554547323 67208788144652436831820985)
      ·
        refine ⟨50406591108489327623865739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67208788144652436831820985 50406591108489327623865739)
        ·
          refine ⟨75609886662733991435798609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50406591108489327623865739 75609886662733991435798609)
          ·
            refine ⟨56707414997050493576848957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75609886662733991435798609 56707414997050493576848957)
            ·
              refine ⟨21265280623893935091318359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56707414997050493576848957 21265280623893935091318359)
              ·
                refine ⟨31897920935840902636977539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21265280623893935091318359 31897920935840902636977539)
                ·
                  refine ⟨47846881403761353955466309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31897920935840902636977539 47846881403761353955466309)
                  ·
                    refine ⟨8971290263205253866649933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47846881403761353955466309 8971290263205253866649933)
                    ·
                      refine ⟨3364233848701970199993725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971290263205253866649933 3364233848701970199993725)
                      ·
                        rfl

theorem cell23_6551822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6551822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551822 prefixEnd_6551822 := by exact prefixLift 6551822
  have htrace : WordTrace (prefixWord ++ tailWord_6551822) baseStart_6551822 baseEnd_6551822 := by
    simpa [prefixWord, tailWord_6551822, baseEnd_6551822] using wordTrace_append hprefix tailTrace_6551822
  have hstable : (prefixWord ++ tailWord_6551822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551822).length < 2 ^ (prefixWord ++ tailWord_6551822).sum := by decide
  have hdescent : baseEnd_6551822 < baseStart_6551822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551829 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_6551829 : Nat := 118140960795 + 6551829 * 2 ^ 59
def prefixEnd_6551829 : Nat := 4983230072969 + 3 ^ 40 * 6551829 * 2
def baseEnd_6551829 : Nat := 1121412481022183890868731

theorem tailTrace_6551829 : CollatzResearch.WordTrace tailWord_6551829 prefixEnd_6551829 1121412481022183890868731 := by
  unfold tailWord_6551829
  simp only [CollatzResearch.WordTrace]
  refine ⟨238964835380849971153090541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159309890253899980768727027 238964835380849971153090541)
  ·
    refine ⟨89611813267818739182408953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238964835380849971153090541 89611813267818739182408953)
    ·
      refine ⟨67208859950864054386806715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89611813267818739182408953 67208859950864054386806715)
      ·
        refine ⟨100813289926296081580210073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67208859950864054386806715 100813289926296081580210073)
        ·
          refine ⟨75609967444722061185157555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100813289926296081580210073 75609967444722061185157555)
          ·
            refine ⟨113414951167083091777736333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75609967444722061185157555 113414951167083091777736333)
            ·
              refine ⟨42530606687656159416651125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113414951167083091777736333 42530606687656159416651125)
              ·
                refine ⟨3987244376967764945311043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42530606687656159416651125 3987244376967764945311043)
                ·
                  refine ⟨5980866565451647417966565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987244376967764945311043 5980866565451647417966565)
                  ·
                    refine ⟨1121412481022183890868731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5980866565451647417966565 1121412481022183890868731)
                    ·
                      rfl

theorem cell23_6551829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_6551829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551829 prefixEnd_6551829 := by exact prefixLift 6551829
  have htrace : WordTrace (prefixWord ++ tailWord_6551829) baseStart_6551829 baseEnd_6551829 := by
    simpa [prefixWord, tailWord_6551829, baseEnd_6551829] using wordTrace_append hprefix tailTrace_6551829
  have hstable : (prefixWord ++ tailWord_6551829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551829).length < 2 ^ (prefixWord ++ tailWord_6551829).sum := by decide
  have hdescent : baseEnd_6551829 < baseStart_6551829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551842 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_6551842 : Nat := 118140960795 + 6551842 * 2 ^ 59
def prefixEnd_6551842 : Nat := 4983230072969 + 3 ^ 40 * 6551842 * 2
def baseEnd_6551842 : Nat := 373804902035006680193737

theorem tailTrace_6551842 : CollatzResearch.WordTrace tailWord_6551842 prefixEnd_6551842 373804902035006680193737 := by
  unfold tailWord_6551842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59741327382450718593328445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159310206353201916248875853 59741327382450718593328445)
  ·
    refine ⟨22402997768419019472498167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59741327382450718593328445 22402997768419019472498167)
    ·
      refine ⟨33604496652628529208747251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22402997768419019472498167 33604496652628529208747251)
      ·
        refine ⟨50406744978942793813120877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33604496652628529208747251 50406744978942793813120877)
        ·
          refine ⟨18902529367103547679920329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50406744978942793813120877 18902529367103547679920329)
          ·
            refine ⟨14176897025327660759940247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18902529367103547679920329 14176897025327660759940247)
            ·
              refine ⟨21265345537991491139910371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14176897025327660759940247 21265345537991491139910371)
              ·
                refine ⟨31898018306987236709865557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21265345537991491139910371 31898018306987236709865557)
                ·
                  refine ⟨373804902035006680193737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31898018306987236709865557 373804902035006680193737)
                  ·
                    rfl

theorem cell23_6551842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_6551842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551842 prefixEnd_6551842 := by exact prefixLift 6551842
  have htrace : WordTrace (prefixWord ++ tailWord_6551842) baseStart_6551842 baseEnd_6551842 := by
    simpa [prefixWord, tailWord_6551842, baseEnd_6551842] using wordTrace_append hprefix tailTrace_6551842
  have hstable : (prefixWord ++ tailWord_6551842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551842).length < 2 ^ (prefixWord ++ tailWord_6551842).sum := by decide
  have hdescent : baseEnd_6551842 < baseStart_6551842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551855 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 5, 5]
def baseStart_6551855 : Nat := 118140960795 + 6551855 * 2 ^ 59
def prefixEnd_6551855 : Nat := 4983230072969 + 3 ^ 40 * 6551855 * 2
def baseEnd_6551855 : Nat := 1121416931187856190293691

theorem tailTrace_6551855 : CollatzResearch.WordTrace tailWord_6551855 prefixEnd_6551855 1121416931187856190293691 := by
  unfold tailWord_6551855
  simp only [CollatzResearch.WordTrace]
  refine ⟨238965783678755777593537019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159310522452503851729024679 238965783678755777593537019)
  ·
    refine ⟨358448675518133666390305529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238965783678755777593537019 358448675518133666390305529)
    ·
      refine ⟨268836506638600249792729147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358448675518133666390305529 268836506638600249792729147)
      ·
        refine ⟨403254759957900374689093721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268836506638600249792729147 403254759957900374689093721)
        ·
          refine ⟨302441069968425281016820291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403254759957900374689093721 302441069968425281016820291)
          ·
            refine ⟨453661604952637921525230437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302441069968425281016820291 453661604952637921525230437)
            ·
              refine ⟨85061550928619610285980707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453661604952637921525230437 85061550928619610285980707)
              ·
                refine ⟨127592326392929415428971061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85061550928619610285980707 127592326392929415428971061)
                ·
                  refine ⟨11961780599337132696466037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127592326392929415428971061 11961780599337132696466037)
                  ·
                    refine ⟨1121416931187856190293691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11961780599337132696466037 1121416931187856190293691)
                    ·
                      rfl

theorem cell23_6551855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_6551855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551855 prefixEnd_6551855 := by exact prefixLift 6551855
  have htrace : WordTrace (prefixWord ++ tailWord_6551855) baseStart_6551855 baseEnd_6551855 := by
    simpa [prefixWord, tailWord_6551855, baseEnd_6551855] using wordTrace_append hprefix tailTrace_6551855
  have hstable : (prefixWord ++ tailWord_6551855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551855).length < 2 ^ (prefixWord ++ tailWord_6551855).sum := by decide
  have hdescent : baseEnd_6551855 < baseStart_6551855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551879 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_6551879 : Nat := 118140960795 + 6551879 * 2 ^ 59
def prefixEnd_6551879 : Nat := 4983230072969 + 3 ^ 40 * 6551879 * 2
def baseEnd_6551879 : Nat := 3364263117099276476980963

theorem tailTrace_6551879 : CollatzResearch.WordTrace tailWord_6551879 prefixEnd_6551879 3364263117099276476980963 := by
  unfold tailWord_6551879
  simp only [CollatzResearch.WordTrace]
  refine ⟨238966659030668829692410691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159311106020445886461607127 238966659030668829692410691)
  ·
    refine ⟨358449988546003244538616037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238966659030668829692410691 358449988546003244538616037)
    ·
      refine ⟨67209372852375608350990507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358449988546003244538616037 67209372852375608350990507)
      ·
        refine ⟨100814059278563412526485761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67209372852375608350990507 100814059278563412526485761)
        ·
          refine ⟨75610544458922559394864321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100814059278563412526485761 75610544458922559394864321)
          ·
            refine ⟨56707908344191919546148241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75610544458922559394864321 56707908344191919546148241)
            ·
              refine ⟨42530931258143939659611181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56707908344191919546148241 42530931258143939659611181)
              ·
                refine ⟨15949099221803977372354193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42530931258143939659611181 15949099221803977372354193)
                ·
                  refine ⟨11961824416352983029265645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15949099221803977372354193 11961824416352983029265645)
                  ·
                    refine ⟨4485684156132368635974617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11961824416352983029265645 4485684156132368635974617)
                    ·
                      refine ⟨3364263117099276476980963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485684156132368635974617 3364263117099276476980963)
                      ·
                        rfl

theorem cell23_6551879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_6551879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551879 prefixEnd_6551879 := by exact prefixLift 6551879
  have htrace : WordTrace (prefixWord ++ tailWord_6551879) baseStart_6551879 baseEnd_6551879 := by
    simpa [prefixWord, tailWord_6551879, baseEnd_6551879] using wordTrace_append hprefix tailTrace_6551879
  have hstable : (prefixWord ++ tailWord_6551879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551879).length < 2 ^ (prefixWord ++ tailWord_6551879).sum := by decide
  have hdescent : baseEnd_6551879 < baseStart_6551879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_6551886 : Nat := 118140960795 + 6551886 * 2 ^ 59
def prefixEnd_6551886 : Nat := 4983230072969 + 3 ^ 40 * 6551886 * 2
def baseEnd_6551886 : Nat := 3364266711463857949593431

theorem tailTrace_6551886 : CollatzResearch.WordTrace tailWord_6551886 prefixEnd_6551886 3364266711463857949593431 := by
  unfold tailWord_6551886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870864292705433735989439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159311276227762313258610341 29870864292705433735989439)
  ·
    refine ⟨44806296439058150603984159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29870864292705433735989439 44806296439058150603984159)
    ·
      refine ⟨67209444658587225905976239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44806296439058150603984159 67209444658587225905976239)
      ·
        refine ⟨100814166987880838858964359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67209444658587225905976239 100814166987880838858964359)
        ·
          refine ⟨151221250481821258288446539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100814166987880838858964359 151221250481821258288446539)
          ·
            refine ⟨226831875722731887432669809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151221250481821258288446539 226831875722731887432669809)
            ·
              refine ⟨170123906792048915574502357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226831875722731887432669809 170123906792048915574502357)
              ·
                refine ⟨3987279065438646458777399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170123906792048915574502357 3987279065438646458777399)
                ·
                  refine ⟨5980918598157969688166099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987279065438646458777399 5980918598157969688166099)
                  ·
                    refine ⟨8971377897236954532249149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980918598157969688166099 8971377897236954532249149)
                    ·
                      refine ⟨3364266711463857949593431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971377897236954532249149 3364266711463857949593431)
                      ·
                        rfl

theorem cell23_6551886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_6551886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551886 prefixEnd_6551886 := by exact prefixLift 6551886
  have htrace : WordTrace (prefixWord ++ tailWord_6551886) baseStart_6551886 baseEnd_6551886 := by
    simpa [prefixWord, tailWord_6551886, baseEnd_6551886] using wordTrace_append hprefix tailTrace_6551886
  have hstable : (prefixWord ++ tailWord_6551886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551886).length < 2 ^ (prefixWord ++ tailWord_6551886).sum := by decide
  have hdescent : baseEnd_6551886 < baseStart_6551886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551922 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6551922 : Nat := 118140960795 + 6551922 * 2 ^ 59
def prefixEnd_6551922 : Nat := 4983230072969 + 3 ^ 40 * 6551922 * 2
def baseEnd_6551922 : Nat := 3364285196767419808743265

theorem tailTrace_6551922 : CollatzResearch.WordTrace tailWord_6551922 prefixEnd_6551922 3364285196767419808743265 := by
  unfold tailWord_6551922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742056842378262009056505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159312151579675365357484013 59742056842378262009056505)
  ·
    refine ⟨44806542631783696506792379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59742056842378262009056505 44806542631783696506792379)
    ·
      refine ⟨67209813947675544760188569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44806542631783696506792379 67209813947675544760188569)
      ·
        refine ⟨50407360460756658570141427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67209813947675544760188569 50407360460756658570141427)
        ·
          refine ⟨75611040691134987855212141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50407360460756658570141427 75611040691134987855212141)
          ·
            refine ⟨28354140259175620445704553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75611040691134987855212141 28354140259175620445704553)
            ·
              refine ⟨21265605194381715334278415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28354140259175620445704553 21265605194381715334278415)
              ·
                refine ⟨31898407791572573001417623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21265605194381715334278415 31898407791572573001417623)
                ·
                  refine ⟨47847611687358859502126435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31898407791572573001417623 47847611687358859502126435)
                  ·
                    refine ⟨71771417531038289253189653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47847611687358859502126435 71771417531038289253189653)
                    ·
                      refine ⟨3364285196767419808743265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71771417531038289253189653 3364285196767419808743265)
                      ·
                        rfl

theorem cell23_6551922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6551922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551922 prefixEnd_6551922 := by exact prefixLift 6551922
  have htrace : WordTrace (prefixWord ++ tailWord_6551922) baseStart_6551922 baseEnd_6551922 := by
    simpa [prefixWord, tailWord_6551922, baseEnd_6551922] using wordTrace_append hprefix tailTrace_6551922
  have hstable : (prefixWord ++ tailWord_6551922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551922).length < 2 ^ (prefixWord ++ tailWord_6551922).sum := by decide
  have hdescent : baseEnd_6551922 < baseStart_6551922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_6551935 : Nat := 118140960795 + 6551935 * 2 ^ 59
def prefixEnd_6551935 : Nat := 4983230072969 + 3 ^ 40 * 6551935 * 2
def baseEnd_6551935 : Nat := 3364291872015928257880705

theorem tailTrace_6551935 : CollatzResearch.WordTrace tailWord_6551935 prefixEnd_6551935 3364291872015928257880705 := by
  unfold tailWord_6551935
  simp only [CollatzResearch.WordTrace]
  refine ⟨238968701518465951256449259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159312467678977300837632839 238968701518465951256449259)
  ·
    refine ⟨358453052277698926884673889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238968701518465951256449259 358453052277698926884673889)
    ·
      refine ⟨268839789208274195163505417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358453052277698926884673889 268839789208274195163505417)
      ·
        refine ⟨201629841906205646372629063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268839789208274195163505417 201629841906205646372629063)
        ·
          refine ⟨302444762859308469558943595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201629841906205646372629063 302444762859308469558943595)
          ·
            refine ⟨453667144288962704338415393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302444762859308469558943595 453667144288962704338415393)
            ·
              refine ⟨340250358216722028253811545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453667144288962704338415393 340250358216722028253811545)
              ·
                refine ⟨255187768662541521190358659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340250358216722028253811545 255187768662541521190358659)
                ·
                  refine ⟨382781652993812281785537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255187768662541521190358659 382781652993812281785537989)
                  ·
                    refine ⟨71771559936339802834788373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382781652993812281785537989 71771559936339802834788373)
                    ·
                      refine ⟨3364291872015928257880705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71771559936339802834788373 3364291872015928257880705)
                      ·
                        rfl

theorem cell23_6551935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_6551935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551935 prefixEnd_6551935 := by exact prefixLift 6551935
  have htrace : WordTrace (prefixWord ++ tailWord_6551935) baseStart_6551935 baseEnd_6551935 := by
    simpa [prefixWord, tailWord_6551935, baseEnd_6551935] using wordTrace_append hprefix tailTrace_6551935
  have hstable : (prefixWord ++ tailWord_6551935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551935).length < 2 ^ (prefixWord ++ tailWord_6551935).sum := by decide
  have hdescent : baseEnd_6551935 < baseStart_6551935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551939 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4]
def baseStart_6551939 : Nat := 118140960795 + 6551939 * 2 ^ 59
def prefixEnd_6551939 : Nat := 4983230072969 + 3 ^ 40 * 6551939 * 2
def baseEnd_6551939 : Nat := 3364293925938546242230687

theorem tailTrace_6551939 : CollatzResearch.WordTrace tailWord_6551939 prefixEnd_6551939 3364293925938546242230687 := by
  unfold tailWord_6551939
  simp only [CollatzResearch.WordTrace]
  refine ⟨238968847410451459939594871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159312564940300973293063247 238968847410451459939594871)
  ·
    refine ⟨358453271115677189909392307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238968847410451459939594871 358453271115677189909392307)
    ·
      refine ⟨537679906673515784864088461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358453271115677189909392307 537679906673515784864088461)
      ·
        refine ⟨201629965002568419324033173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537679906673515784864088461 201629965002568419324033173)
        ·
          refine ⟨9451404609495394655814055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201629965002568419324033173 9451404609495394655814055)
          ·
            refine ⟨14177106914243091983721083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451404609495394655814055 14177106914243091983721083)
            ·
              refine ⟨21265660371364637975581625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177106914243091983721083 21265660371364637975581625)
              ·
                refine ⟨15949245278523478481686219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21265660371364637975581625 15949245278523478481686219)
                ·
                  refine ⟨23923867917785217722529329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15949245278523478481686219 23923867917785217722529329)
                  ·
                    refine ⟨17942900938338913291896997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23923867917785217722529329 17942900938338913291896997)
                    ·
                      refine ⟨3364293925938546242230687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17942900938338913291896997 3364293925938546242230687)
                      ·
                        rfl

theorem cell23_6551939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_6551939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551939 prefixEnd_6551939 := by exact prefixLift 6551939
  have htrace : WordTrace (prefixWord ++ tailWord_6551939) baseStart_6551939 baseEnd_6551939 := by
    simpa [prefixWord, tailWord_6551939, baseEnd_6551939] using wordTrace_append hprefix tailTrace_6551939
  have hstable : (prefixWord ++ tailWord_6551939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551939).length < 2 ^ (prefixWord ++ tailWord_6551939).sum := by decide
  have hdescent : baseEnd_6551939 < baseStart_6551939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551943 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_6551943 : Nat := 118140960795 + 6551943 * 2 ^ 59
def prefixEnd_6551943 : Nat := 4983230072969 + 3 ^ 40 * 6551943 * 2
def baseEnd_6551943 : Nat := 3364295979861164226580669

theorem tailTrace_6551943 : CollatzResearch.WordTrace tailWord_6551943 prefixEnd_6551943 3364295979861164226580669 := by
  unfold tailWord_6551943
  simp only [CollatzResearch.WordTrace]
  refine ⟨238968993302436968622740483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159312662201624645748493655 238968993302436968622740483)
  ·
    refine ⟨358453489953655452934110725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238968993302436968622740483 358453489953655452934110725)
    ·
      refine ⟨67210029366310397425145761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358453489953655452934110725 67210029366310397425145761)
      ·
        refine ⟨50407522024732798068859321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67210029366310397425145761 50407522024732798068859321)
        ·
          refine ⟨37805641518549598551644491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50407522024732798068859321 37805641518549598551644491)
          ·
            refine ⟨56708462277824397827466737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37805641518549598551644491 56708462277824397827466737)
            ·
              refine ⟨42531346708368298370600053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56708462277824397827466737 42531346708368298370600053)
              ·
                refine ⟨3987313753909527972243755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42531346708368298370600053 3987313753909527972243755)
                ·
                  refine ⟨5980970630864291958365633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987313753909527972243755 5980970630864291958365633)
                  ·
                    refine ⟨4485727973148218968774225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980970630864291958365633 4485727973148218968774225)
                    ·
                      refine ⟨3364295979861164226580669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485727973148218968774225 3364295979861164226580669)
                      ·
                        rfl

theorem cell23_6551943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_6551943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551943 prefixEnd_6551943 := by exact prefixLift 6551943
  have htrace : WordTrace (prefixWord ++ tailWord_6551943) baseStart_6551943 baseEnd_6551943 := by
    simpa [prefixWord, tailWord_6551943, baseEnd_6551943] using wordTrace_append hprefix tailTrace_6551943
  have hstable : (prefixWord ++ tailWord_6551943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551943).length < 2 ^ (prefixWord ++ tailWord_6551943).sum := by decide
  have hdescent : baseEnd_6551943 < baseStart_6551943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551955 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_6551955 : Nat := 118140960795 + 6551955 * 2 ^ 59
def prefixEnd_6551955 : Nat := 4983230072969 + 3 ^ 40 * 6551955 * 2
def baseEnd_6551955 : Nat := 3364302141629018179630613

theorem tailTrace_6551955 : CollatzResearch.WordTrace tailWord_6551955 prefixEnd_6551955 3364302141629018179630613 := by
  unfold tailWord_6551955
  simp only [CollatzResearch.WordTrace]
  refine ⟨238969430978393494672177319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159312953985595663114784879 238969430978393494672177319)
  ·
    refine ⟨358454146467590242008265979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238969430978393494672177319 358454146467590242008265979)
    ·
      refine ⟨537681219701385363012398969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358454146467590242008265979 537681219701385363012398969)
      ·
        refine ⟨403260914776039022259299227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537681219701385363012398969 403260914776039022259299227)
        ·
          refine ⟨604891372164058533388948841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403260914776039022259299227 604891372164058533388948841)
          ·
            refine ⟨453668529123043900041711631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604891372164058533388948841 453668529123043900041711631)
            ·
              refine ⟨680502793684565850062567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453668529123043900041711631 680502793684565850062567447)
              ·
                refine ⟨1020754190526848775093851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680502793684565850062567447 1020754190526848775093851171)
                ·
                  refine ⟨1531131285790273162640776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020754190526848775093851171 1531131285790273162640776757)
                  ·
                    refine ⟨143543558042838108997572821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1531131285790273162640776757 143543558042838108997572821)
                    ·
                      refine ⟨3364302141629018179630613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143543558042838108997572821 3364302141629018179630613)
                      ·
                        rfl

theorem cell23_6551955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_6551955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551955 prefixEnd_6551955 := by exact prefixLift 6551955
  have htrace : WordTrace (prefixWord ++ tailWord_6551955) baseStart_6551955 baseEnd_6551955 := by
    simpa [prefixWord, tailWord_6551955, baseEnd_6551955] using wordTrace_append hprefix tailTrace_6551955
  have hstable : (prefixWord ++ tailWord_6551955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551955).length < 2 ^ (prefixWord ++ tailWord_6551955).sum := by decide
  have hdescent : baseEnd_6551955 < baseStart_6551955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551959 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_6551959 : Nat := 118140960795 + 6551959 * 2 ^ 59
def prefixEnd_6551959 : Nat := 4983230072969 + 3 ^ 40 * 6551959 * 2
def baseEnd_6551959 : Nat := 3364304195551636163980595

theorem tailTrace_6551959 : CollatzResearch.WordTrace tailWord_6551959 prefixEnd_6551959 3364304195551636163980595 := by
  unfold tailWord_6551959
  simp only [CollatzResearch.WordTrace]
  refine ⟨238969576870379003355322931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159313051246919335570215287 238969576870379003355322931)
  ·
    refine ⟨358454365305568505032984397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238969576870379003355322931 358454365305568505032984397)
    ·
      refine ⟨134420386989588189387369149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358454365305568505032984397 134420386989588189387369149)
      ·
        refine ⟨50407645121095571020263431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134420386989588189387369149 50407645121095571020263431)
        ·
          refine ⟨75611467681643356530395147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50407645121095571020263431 75611467681643356530395147)
          ·
            refine ⟨113417201522465034795592721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75611467681643356530395147 113417201522465034795592721)
            ·
              refine ⟨85062901141848776096694541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113417201522465034795592721 85062901141848776096694541)
              ·
                refine ⟨31898587928193291036260453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85062901141848776096694541 31898587928193291036260453)
                ·
                  refine ⟨5980985236536242069298835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31898587928193291036260453 5980985236536242069298835)
                  ·
                    refine ⟨8971477854804363103948253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980985236536242069298835 8971477854804363103948253)
                    ·
                      refine ⟨3364304195551636163980595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971477854804363103948253 3364304195551636163980595)
                      ·
                        rfl

theorem cell23_6551959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_6551959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551959 prefixEnd_6551959 := by exact prefixLift 6551959
  have htrace : WordTrace (prefixWord ++ tailWord_6551959) baseStart_6551959 baseEnd_6551959 := by
    simpa [prefixWord, tailWord_6551959, baseEnd_6551959] using wordTrace_append hprefix tailTrace_6551959
  have hstable : (prefixWord ++ tailWord_6551959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551959).length < 2 ^ (prefixWord ++ tailWord_6551959).sum := by decide
  have hdescent : baseEnd_6551959 < baseStart_6551959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551960 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6551960 : Nat := 118140960795 + 6551960 * 2 ^ 59
def prefixEnd_6551960 : Nat := 4983230072969 + 3 ^ 40 * 6551960 * 2
def baseEnd_6551960 : Nat := 3364304709032290660068091

theorem tailTrace_6551960 : CollatzResearch.WordTrace tailWord_6551960 prefixEnd_6551960 3364304709032290660068091 := by
  unfold tailWord_6551960
  simp only [CollatzResearch.WordTrace]
  refine ⟨119484806671687690263054667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159313075562250253684072889 119484806671687690263054667)
  ·
    refine ⟨179227210007531535394582001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119484806671687690263054667 179227210007531535394582001)
    ·
      refine ⟨134420407505648651545936501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179227210007531535394582001 134420407505648651545936501)
      ·
        refine ⟨12601913203654561082431547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134420407505648651545936501 12601913203654561082431547)
        ·
          refine ⟨18902869805481841623647321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12601913203654561082431547 18902869805481841623647321)
          ·
            refine ⟨14177152354111381217735491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18902869805481841623647321 14177152354111381217735491)
            ·
              refine ⟨21265728531167071826603237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177152354111381217735491 21265728531167071826603237)
              ·
                refine ⟨3987324099593825967488107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21265728531167071826603237 3987324099593825967488107)
                ·
                  refine ⟨5980986149390738951232161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987324099593825967488107 5980986149390738951232161)
                  ·
                    refine ⟨4485739612043054213424121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980986149390738951232161 4485739612043054213424121)
                    ·
                      refine ⟨3364304709032290660068091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485739612043054213424121 3364304709032290660068091)
                      ·
                        rfl

theorem cell23_6551960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6551960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551960 prefixEnd_6551960 := by exact prefixLift 6551960
  have htrace : WordTrace (prefixWord ++ tailWord_6551960) baseStart_6551960 baseEnd_6551960 := by
    simpa [prefixWord, tailWord_6551960, baseEnd_6551960] using wordTrace_append hprefix tailTrace_6551960
  have hstable : (prefixWord ++ tailWord_6551960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551960).length < 2 ^ (prefixWord ++ tailWord_6551960).sum := by decide
  have hdescent : baseEnd_6551960 < baseStart_6551960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551962 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_6551962 : Nat := 118140960795 + 6551962 * 2 ^ 59
def prefixEnd_6551962 : Nat := 4983230072969 + 3 ^ 40 * 6551962 * 2
def baseEnd_6551962 : Nat := 1121435245331199884081027

theorem tailTrace_6551962 : CollatzResearch.WordTrace tailWord_6551962 prefixEnd_6551962 1121435245331199884081027 := by
  unfold tailWord_6551962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742421572342033716920535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159313124192912089911788093 59742421572342033716920535)
  ·
    refine ⟨89613632358513050575380803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59742421572342033716920535 89613632358513050575380803)
    ·
      refine ⟨134420448537769575863071205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89613632358513050575380803 134420448537769575863071205)
      ·
        refine ⟨25203834100831795474325851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134420448537769575863071205 25203834100831795474325851)
        ·
          refine ⟨37805751151247693211488777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25203834100831795474325851 37805751151247693211488777)
          ·
            refine ⟨28354313363435769908616583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37805751151247693211488777 28354313363435769908616583)
            ·
              refine ⟨42531470045153654862924875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28354313363435769908616583 42531470045153654862924875)
              ·
                refine ⟨63797205067730482294387313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42531470045153654862924875 63797205067730482294387313)
                ·
                  refine ⟨47847903800797861720790485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63797205067730482294387313 47847903800797861720790485)
                  ·
                    refine ⟨1121435245331199884081027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47847903800797861720790485 1121435245331199884081027)
                    ·
                      rfl

theorem cell23_6551962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_6551962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551962 prefixEnd_6551962 := by exact prefixLift 6551962
  have htrace : WordTrace (prefixWord ++ tailWord_6551962) baseStart_6551962 baseEnd_6551962 := by
    simpa [prefixWord, tailWord_6551962, baseEnd_6551962] using wordTrace_append hprefix tailTrace_6551962
  have hstable : (prefixWord ++ tailWord_6551962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551962).length < 2 ^ (prefixWord ++ tailWord_6551962).sum := by decide
  have hdescent : baseEnd_6551962 < baseStart_6551962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551966 : List Nat := [4, 3, 1, 2, 1, 3, 1, 8]
def baseStart_6551966 : Nat := 118140960795 + 6551966 * 2 ^ 59
def prefixEnd_6551966 : Nat := 4983230072969 + 3 ^ 40 * 6551966 * 2
def baseEnd_6551966 : Nat := 124603992219119171725669

theorem tailTrace_6551966 : CollatzResearch.WordTrace tailWord_6551966 prefixEnd_6551966 124603992219119171725669 := by
  unfold tailWord_6551966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29871229022669205443853469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159313221454235762367218501 29871229022669205443853469)
  ·
    refine ⟨11201710883500952041445051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29871229022669205443853469 11201710883500952041445051)
    ·
      refine ⟨16802566325251428062167577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11201710883500952041445051 16802566325251428062167577)
      ·
        refine ⟨12601924743938571046625683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16802566325251428062167577 12601924743938571046625683)
        ·
          refine ⟨18902887115907856569938525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12601924743938571046625683 18902887115907856569938525)
          ·
            refine ⟨7088582668465446213726947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18902887115907856569938525 7088582668465446213726947)
            ·
              refine ⟨10632874002698169320590421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088582668465446213726947 10632874002698169320590421)
              ·
                refine ⟨124603992219119171725669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10632874002698169320590421 124603992219119171725669)
                ·
                  rfl

theorem cell23_6551966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_6551966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551966 prefixEnd_6551966 := by exact prefixLift 6551966
  have htrace : WordTrace (prefixWord ++ tailWord_6551966) baseStart_6551966 baseEnd_6551966 := by
    simpa [prefixWord, tailWord_6551966, baseEnd_6551966] using wordTrace_append hprefix tailTrace_6551966
  have hstable : (prefixWord ++ tailWord_6551966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551966).length < 2 ^ (prefixWord ++ tailWord_6551966).sum := by decide
  have hdescent : baseEnd_6551966 < baseStart_6551966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551976 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6551976 : Nat := 118140960795 + 6551976 * 2 ^ 59
def prefixEnd_6551976 : Nat := 4983230072969 + 3 ^ 40 * 6551976 * 2
def baseEnd_6551976 : Nat := 3364312924722762597468017

theorem tailTrace_6551976 : CollatzResearch.WordTrace tailWord_6551976 prefixEnd_6551976 3364312924722762597468017 := by
  unfold tailWord_6551976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119485098455658707629345891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159313464607544943505794521 119485098455658707629345891)
  ·
    refine ⟨179227647683488061444018837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119485098455658707629345891 179227647683488061444018837)
    ·
      refine ⟨8401295985163502880188383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179227647683488061444018837 8401295985163502880188383)
      ·
        refine ⟨12601943977745254320282575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401295985163502880188383 12601943977745254320282575)
        ·
          refine ⟨18902915966617881480423863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12601943977745254320282575 18902915966617881480423863)
          ·
            refine ⟨28354373949926822220635795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18902915966617881480423863 28354373949926822220635795)
            ·
              refine ⟨42531560924890233330953693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28354373949926822220635795 42531560924890233330953693)
              ·
                refine ⟨15949335346833837499107635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42531560924890233330953693 15949335346833837499107635)
                ·
                  refine ⟨23924003020250756248661453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15949335346833837499107635 23924003020250756248661453)
                  ·
                    refine ⟨8971501132594033593248045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23924003020250756248661453 8971501132594033593248045)
                    ·
                      refine ⟨3364312924722762597468017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971501132594033593248045 3364312924722762597468017)
                      ·
                        rfl

theorem cell23_6551976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6551976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551976 prefixEnd_6551976 := by exact prefixLift 6551976
  have htrace : WordTrace (prefixWord ++ tailWord_6551976) baseStart_6551976 baseEnd_6551976 := by
    simpa [prefixWord, tailWord_6551976, baseEnd_6551976] using wordTrace_append hprefix tailTrace_6551976
  have hstable : (prefixWord ++ tailWord_6551976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551976).length < 2 ^ (prefixWord ++ tailWord_6551976).sum := by decide
  have hdescent : baseEnd_6551976 < baseStart_6551976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6551986 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_6551986 : Nat := 118140960795 + 6551986 * 2 ^ 59
def prefixEnd_6551986 : Nat := 4983230072969 + 3 ^ 40 * 6551986 * 2
def baseEnd_6551986 : Nat := 3364318059529307558342971

theorem tailTrace_6551986 : CollatzResearch.WordTrace tailWord_6551986 prefixEnd_6551986 3364318059529307558342971 := by
  unfold tailWord_6551986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742640410320296741638953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159313707760854124644370541 59742640410320296741638953)
  ·
    refine ⟨44806980307740222556229215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59742640410320296741638953 44806980307740222556229215)
    ·
      refine ⟨67210470461610333834343823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44806980307740222556229215 67210470461610333834343823)
      ·
        refine ⟨100815705692415500751515735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67210470461610333834343823 100815705692415500751515735)
        ·
          refine ⟨151223558538623251127273603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100815705692415500751515735 151223558538623251127273603)
          ·
            refine ⟨226835337807934876690910405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151223558538623251127273603 226835337807934876690910405)
            ·
              refine ⟨42531625838987789379545701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226835337807934876690910405 42531625838987789379545701)
              ·
                refine ⟨7974679844810210508664819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42531625838987789379545701 7974679844810210508664819)
                ·
                  refine ⟨11962019767215315762997229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974679844810210508664819 11962019767215315762997229)
                  ·
                    refine ⟨4485757412705743411123961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11962019767215315762997229 4485757412705743411123961)
                    ·
                      refine ⟨3364318059529307558342971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485757412705743411123961 3364318059529307558342971)
                      ·
                        rfl

theorem cell23_6551986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_6551986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6551986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6551986 prefixEnd_6551986 := by exact prefixLift 6551986
  have htrace : WordTrace (prefixWord ++ tailWord_6551986) baseStart_6551986 baseEnd_6551986 := by
    simpa [prefixWord, tailWord_6551986, baseEnd_6551986] using wordTrace_append hprefix tailTrace_6551986
  have hstable : (prefixWord ++ tailWord_6551986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6551986).length < 2 ^ (prefixWord ++ tailWord_6551986).sum := by decide
  have hdescent : baseEnd_6551986 < baseStart_6551986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6551986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552029 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6552029 : Nat := 118140960795 + 6552029 * 2 ^ 59
def prefixEnd_6552029 : Nat := 4983230072969 + 3 ^ 40 * 6552029 * 2
def baseEnd_6552029 : Nat := 3364340139197450890105273

theorem tailTrace_6552029 : CollatzResearch.WordTrace tailWord_6552029 prefixEnd_6552029 3364340139197450890105273 := by
  unfold tailWord_6552029
  simp only [CollatzResearch.WordTrace]
  refine ⟨238972129980125405310371141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159314753320083603540247427 238972129980125405310371141)
  ·
    refine ⟨44807274371273513495694589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238972129980125405310371141 44807274371273513495694589)
    ·
      refine ⟨16802727889227567560885471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44807274371273513495694589 16802727889227567560885471)
      ·
        refine ⟨25204091833841351341328207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16802727889227567560885471 25204091833841351341328207)
        ·
          refine ⟨37806137750762027011992311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25204091833841351341328207 37806137750762027011992311)
          ·
            refine ⟨56709206626143040517988467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37806137750762027011992311 56709206626143040517988467)
            ·
              refine ⟨85063809939214560776982701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56709206626143040517988467 85063809939214560776982701)
              ·
                refine ⟨31898928727205460291368513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85063809939214560776982701 31898928727205460291368513)
                ·
                  refine ⟨23924196545404095218526385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31898928727205460291368513 23924196545404095218526385)
                  ·
                    refine ⟨17943147409053071413894789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23924196545404095218526385 17943147409053071413894789)
                    ·
                      refine ⟨3364340139197450890105273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17943147409053071413894789 3364340139197450890105273)
                      ·
                        rfl

theorem cell23_6552029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6552029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552029 prefixEnd_6552029 := by exact prefixLift 6552029
  have htrace : WordTrace (prefixWord ++ tailWord_6552029) baseStart_6552029 baseEnd_6552029 := by
    simpa [prefixWord, tailWord_6552029, baseEnd_6552029] using wordTrace_append hprefix tailTrace_6552029
  have hstable : (prefixWord ++ tailWord_6552029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552029).length < 2 ^ (prefixWord ++ tailWord_6552029).sum := by decide
  have hdescent : baseEnd_6552029 < baseStart_6552029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552084 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6552084 : Nat := 118140960795 + 6552084 * 2 ^ 59
def prefixEnd_6552084 : Nat := 4983230072969 + 3 ^ 40 * 6552084 * 2
def baseEnd_6552084 : Nat := 3364368380633448174917521

theorem tailTrace_6552084 : CollatzResearch.WordTrace tailWord_6552084 prefixEnd_6552084 3364368380633448174917521 := by
  unfold tailWord_6552084
  simp only [CollatzResearch.WordTrace]
  refine ⟨119487067997463074851811653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159316090663284099802415537 119487067997463074851811653)
  ·
    refine ⟨22403825249524326534714685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119487067997463074851811653 22403825249524326534714685)
    ·
      refine ⟨8401434468571622450518007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22403825249524326534714685 8401434468571622450518007)
      ·
        refine ⟨12602151702857433675777011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401434468571622450518007 12602151702857433675777011)
        ·
          refine ⟨18903227554286150513665517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12602151702857433675777011 18903227554286150513665517)
          ·
            refine ⟨7088710332857306442624569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18903227554286150513665517 7088710332857306442624569)
            ·
              refine ⟨5316532749642979831968427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088710332857306442624569 5316532749642979831968427)
              ·
                refine ⟨7974799124464469747952641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316532749642979831968427 7974799124464469747952641)
                ·
                  refine ⟨5981099343348352310964481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7974799124464469747952641 5981099343348352310964481)
                  ·
                    refine ⟨4485824507511264233223361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5981099343348352310964481 4485824507511264233223361)
                    ·
                      refine ⟨3364368380633448174917521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485824507511264233223361 3364368380633448174917521)
                      ·
                        rfl

theorem cell23_6552084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6552084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552084 prefixEnd_6552084 := by exact prefixLift 6552084
  have htrace : WordTrace (prefixWord ++ tailWord_6552084) baseStart_6552084 baseEnd_6552084 := by
    simpa [prefixWord, tailWord_6552084, baseEnd_6552084] using wordTrace_append hprefix tailTrace_6552084
  have hstable : (prefixWord ++ tailWord_6552084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552084).length < 2 ^ (prefixWord ++ tailWord_6552084).sum := by decide
  have hdescent : baseEnd_6552084 < baseStart_6552084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552106 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6552106 : Nat := 118140960795 + 6552106 * 2 ^ 59
def prefixEnd_6552106 : Nat := 4983230072969 + 3 ^ 40 * 6552106 * 2
def baseEnd_6552106 : Nat := 3364379677207847088842419

theorem tailTrace_6552106 : CollatzResearch.WordTrace tailWord_6552106 prefixEnd_6552106 3364379677207847088842419 := by
  unfold tailWord_6552106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743734600211611865231043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159316625600564298307282781 59743734600211611865231043)
  ·
    refine ⟨89615601900317417797846565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59743734600211611865231043 89615601900317417797846565)
    ·
      refine ⟨16802925356309515837096231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89615601900317417797846565 16802925356309515837096231)
      ·
        refine ⟨25204388034464273755644347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16802925356309515837096231 25204388034464273755644347)
        ·
          refine ⟨37806582051696410633466521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25204388034464273755644347 37806582051696410633466521)
          ·
            refine ⟨28354936538772307975099891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37806582051696410633466521 28354936538772307975099891)
            ·
              refine ⟨42532404808158461962649837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28354936538772307975099891 42532404808158461962649837)
              ·
                refine ⟨15949651803059423235993689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42532404808158461962649837 15949651803059423235993689)
                ·
                  refine ⟨11962238852294567426995267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15949651803059423235993689 11962238852294567426995267)
                  ·
                    refine ⟨17943358278441851140492901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11962238852294567426995267 17943358278441851140492901)
                    ·
                      refine ⟨3364379677207847088842419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17943358278441851140492901 3364379677207847088842419)
                      ·
                        rfl

theorem cell23_6552106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6552106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552106 prefixEnd_6552106 := by exact prefixLift 6552106
  have htrace : WordTrace (prefixWord ++ tailWord_6552106) baseStart_6552106 baseEnd_6552106 := by
    simpa [prefixWord, tailWord_6552106, baseEnd_6552106] using wordTrace_append hprefix tailTrace_6552106
  have hstable : (prefixWord ++ tailWord_6552106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552106).length < 2 ^ (prefixWord ++ tailWord_6552106).sum := by decide
  have hdescent : baseEnd_6552106 < baseStart_6552106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552112 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 10]
def baseStart_6552112 : Nat := 118140960795 + 6552112 * 2 ^ 59
def prefixEnd_6552112 : Nat := 4983230072969 + 3 ^ 40 * 6552112 * 2
def baseEnd_6552112 : Nat := 373820306454641562818599

theorem tailTrace_6552112 : CollatzResearch.WordTrace tailWord_6552112 prefixEnd_6552112 373820306454641562818599 := by
  unfold tailWord_6552112
  simp only [CollatzResearch.WordTrace]
  refine ⟨119487578619412355242821295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159316771492549806990428393 119487578619412355242821295)
  ·
    refine ⟨179231367929118532864231943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119487578619412355242821295 179231367929118532864231943)
    ·
      refine ⟨268847051893677799296347915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179231367929118532864231943 268847051893677799296347915)
      ·
        refine ⟨403270577840516698944521873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268847051893677799296347915 403270577840516698944521873)
        ·
          refine ⟨302452933380387524208391405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403270577840516698944521873 302452933380387524208391405)
          ·
            refine ⟨113419850017645321578146777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302452933380387524208391405 113419850017645321578146777)
            ·
              refine ⟨85064887513233991183610083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113419850017645321578146777 85064887513233991183610083)
              ·
                refine ⟨127597331269850986775415125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85064887513233991183610083 127597331269850986775415125)
                ·
                  refine ⟨373820306454641562818599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127597331269850986775415125 373820306454641562818599)
                  ·
                    rfl

theorem cell23_6552112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_6552112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552112 prefixEnd_6552112 := by exact prefixLift 6552112
  have htrace : WordTrace (prefixWord ++ tailWord_6552112) baseStart_6552112 baseEnd_6552112 := by
    simpa [prefixWord, tailWord_6552112, baseEnd_6552112] using wordTrace_append hprefix tailTrace_6552112
  have hstable : (prefixWord ++ tailWord_6552112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552112).length < 2 ^ (prefixWord ++ tailWord_6552112).sum := by decide
  have hdescent : baseEnd_6552112 < baseStart_6552112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552133 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_6552133 : Nat := 118140960795 + 6552133 * 2 ^ 59
def prefixEnd_6552133 : Nat := 4983230072969 + 3 ^ 40 * 6552133 * 2
def baseEnd_6552133 : Nat := 1121464513728506161068265

theorem tailTrace_6552133 : CollatzResearch.WordTrace tailWord_6552133 prefixEnd_6552133 1121464513728506161068265 := by
  unfold tailWord_6552133
  simp only [CollatzResearch.WordTrace]
  refine ⟨238975923171748631072157053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159317282114499087381438035 238975923171748631072157053)
  ·
    refine ⟨89615971189405736652058895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238975923171748631072157053 89615971189405736652058895)
    ·
      refine ⟨134423956784108604978088343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89615971189405736652058895 134423956784108604978088343)
      ·
        refine ⟨201635935176162907467132515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134423956784108604978088343 201635935176162907467132515)
        ·
          refine ⟨302453902764244361200698773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201635935176162907467132515 302453902764244361200698773)
          ·
            refine ⟨14177526692073954431282755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 302453902764244361200698773 14177526692073954431282755)
            ·
              refine ⟨21266290038110931646924133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177526692073954431282755 21266290038110931646924133)
              ·
                refine ⟨3987429382145799683798275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21266290038110931646924133 3987429382145799683798275)
                ·
                  refine ⟨5981144073218699525697413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987429382145799683798275 5981144073218699525697413)
                  ·
                    refine ⟨1121464513728506161068265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981144073218699525697413 1121464513728506161068265)
                    ·
                      rfl

theorem cell23_6552133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_6552133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552133 prefixEnd_6552133 := by exact prefixLift 6552133
  have htrace : WordTrace (prefixWord ++ tailWord_6552133) baseStart_6552133 baseEnd_6552133 := by
    simpa [prefixWord, tailWord_6552133, baseEnd_6552133] using wordTrace_append hprefix tailTrace_6552133
  have hstable : (prefixWord ++ tailWord_6552133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552133).length < 2 ^ (prefixWord ++ tailWord_6552133).sum := by decide
  have hdescent : baseEnd_6552133 < baseStart_6552133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552179 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4]
def baseStart_6552179 : Nat := 118140960795 + 6552179 * 2 ^ 59
def prefixEnd_6552179 : Nat := 4983230072969 + 3 ^ 40 * 6552179 * 2
def baseEnd_6552179 : Nat := 3364417161295625303229583

theorem tailTrace_6552179 : CollatzResearch.WordTrace tailWord_6552179 prefixEnd_6552179 3364417161295625303229583 := by
  unfold tailWord_6552179
  simp only [CollatzResearch.WordTrace]
  refine ⟨238977600929581980928331591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159318400619721320618887727 238977600929581980928331591)
  ·
    refine ⟨358466401394372971392497387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238977600929581980928331591 358466401394372971392497387)
    ·
      refine ⟨537699602091559457088746081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358466401394372971392497387 537699602091559457088746081)
      ·
        refine ⟨403274701568669592816559561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537699602091559457088746081 403274701568669592816559561)
        ·
          refine ⟨302456026176502194612419671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403274701568669592816559561 302456026176502194612419671)
          ·
            refine ⟨453684039264753291918629507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302456026176502194612419671 453684039264753291918629507)
            ·
              refine ⟨680526058897129937877944261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453684039264753291918629507 680526058897129937877944261)
              ·
                refine ⟨127598636043211863352114549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680526058897129937877944261 127598636043211863352114549)
                ·
                  refine ⟨11962372129051112189260739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127598636043211863352114549 11962372129051112189260739)
                  ·
                    refine ⟨17943558193576668283891109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11962372129051112189260739 17943558193576668283891109)
                    ·
                      refine ⟨3364417161295625303229583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17943558193576668283891109 3364417161295625303229583)
                      ·
                        rfl

theorem cell23_6552179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_6552179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552179 prefixEnd_6552179 := by exact prefixLift 6552179
  have htrace : WordTrace (prefixWord ++ tailWord_6552179) baseStart_6552179 baseEnd_6552179 := by
    simpa [prefixWord, tailWord_6552179, baseEnd_6552179] using wordTrace_append hprefix tailTrace_6552179
  have hstable : (prefixWord ++ tailWord_6552179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552179).length < 2 ^ (prefixWord ++ tailWord_6552179).sum := by decide
  have hdescent : baseEnd_6552179 < baseStart_6552179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552224 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 1, 1, 3]
def baseStart_6552224 : Nat := 118140960795 + 6552224 * 2 ^ 59
def prefixEnd_6552224 : Nat := 4983230072969 + 3 ^ 40 * 6552224 * 2
def baseEnd_6552224 : Nat := 3364440267925077627166877

theorem tailTrace_6552224 : CollatzResearch.WordTrace tailWord_6552224 prefixEnd_6552224 3364440267925077627166877 := by
  unfold tailWord_6552224
  simp only [CollatzResearch.WordTrace]
  refine ⟨119489621107209476806859863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159319494809612635742479817 119489621107209476806859863)
  ·
    refine ⟨179234431660814215210289795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119489621107209476806859863 179234431660814215210289795)
    ·
      refine ⟨268851647491221322815434693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179234431660814215210289795 268851647491221322815434693)
      ·
        refine ⟨50409683904603998027894005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268851647491221322815434693 50409683904603998027894005)
        ·
          refine ⟨4725907866056624815115063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50409683904603998027894005 4725907866056624815115063)
          ·
            refine ⟨7088861799084937222672595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725907866056624815115063 7088861799084937222672595)
            ·
              refine ⟨10633292698627405834008893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088861799084937222672595 10633292698627405834008893)
              ·
                refine ⟨3987484761985277187753335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10633292698627405834008893 3987484761985277187753335)
                ·
                  refine ⟨5981227142977915781630003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987484761985277187753335 5981227142977915781630003)
                  ·
                    refine ⟨8971840714466873672445005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5981227142977915781630003 8971840714466873672445005)
                    ·
                      refine ⟨3364440267925077627166877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8971840714466873672445005 3364440267925077627166877)
                      ·
                        rfl

theorem cell23_6552224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_6552224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552224 prefixEnd_6552224 := by exact prefixLift 6552224
  have htrace : WordTrace (prefixWord ++ tailWord_6552224) baseStart_6552224 baseEnd_6552224 := by
    simpa [prefixWord, tailWord_6552224, baseEnd_6552224] using wordTrace_append hprefix tailTrace_6552224
  have hstable : (prefixWord ++ tailWord_6552224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552224).length < 2 ^ (prefixWord ++ tailWord_6552224).sum := by decide
  have hdescent : baseEnd_6552224 < baseStart_6552224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552247 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_6552247 : Nat := 118140960795 + 6552247 * 2 ^ 59
def prefixEnd_6552247 : Nat := 4983230072969 + 3 ^ 40 * 6552247 * 2
def baseEnd_6552247 : Nat := 3364452077980131037179271

theorem tailTrace_6552247 : CollatzResearch.WordTrace tailWord_6552247 prefixEnd_6552247 3364452077980131037179271 := by
  unfold tailWord_6552247
  simp only [CollatzResearch.WordTrace]
  refine ⟨238980081093335628541806995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159320054062223752361204663 238980081093335628541806995)
  ·
    refine ⟨358470121640003442812710493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238980081093335628541806995 358470121640003442812710493)
    ·
      refine ⟨134426295615001291054766435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358470121640003442812710493 134426295615001291054766435)
      ·
        refine ⟨201639443422501936582149653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134426295615001291054766435 201639443422501936582149653)
        ·
          refine ⟨9451848910429778277288265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201639443422501936582149653 9451848910429778277288265)
          ·
            refine ⟨7088886682822333707966199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9451848910429778277288265 7088886682822333707966199)
            ·
              refine ⟨10633330024233500561949299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088886682822333707966199 10633330024233500561949299)
              ·
                refine ⟨15949995036350250842923949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10633330024233500561949299 15949995036350250842923949)
                ·
                  refine ⟨5981248138631344066096481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15949995036350250842923949 5981248138631344066096481)
                  ·
                    refine ⟨4485936103973508049572361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5981248138631344066096481 4485936103973508049572361)
                    ·
                      refine ⟨3364452077980131037179271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485936103973508049572361 3364452077980131037179271)
                      ·
                        rfl

theorem cell23_6552247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_6552247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552247 prefixEnd_6552247 := by exact prefixLift 6552247
  have htrace : WordTrace (prefixWord ++ tailWord_6552247) baseStart_6552247 baseEnd_6552247 := by
    simpa [prefixWord, tailWord_6552247, baseEnd_6552247] using wordTrace_append hprefix tailTrace_6552247
  have hstable : (prefixWord ++ tailWord_6552247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552247).length < 2 ^ (prefixWord ++ tailWord_6552247).sum := by decide
  have hdescent : baseEnd_6552247 < baseStart_6552247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552249 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_6552249 : Nat := 118140960795 + 6552249 * 2 ^ 59
def prefixEnd_6552249 : Nat := 4983230072969 + 3 ^ 40 * 6552249 * 2
def baseEnd_6552249 : Nat := 1121484368313813343118087

theorem tailTrace_6552249 : CollatzResearch.WordTrace tailWord_6552249 prefixEnd_6552249 1121484368313813343118087 := by
  unfold tailWord_6552249
  simp only [CollatzResearch.WordTrace]
  refine ⟨238980154039328382883379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159320102692885588588919867 238980154039328382883379801)
  ·
    refine ⟨179235115529496287162534851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238980154039328382883379801 179235115529496287162534851)
    ·
      refine ⟨268852673294244430743802277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179235115529496287162534851 268852673294244430743802277)
      ·
        refine ⟨50409876242670830764462927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268852673294244430743802277 50409876242670830764462927)
        ·
          refine ⟨75614814364006246146694391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50409876242670830764462927 75614814364006246146694391)
          ·
            refine ⟨113422221546009369220041587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75614814364006246146694391 113422221546009369220041587)
            ·
              refine ⟨170133332319014053830062381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113422221546009369220041587 170133332319014053830062381)
              ·
                refine ⟨63799999619630270186273393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170133332319014053830062381 63799999619630270186273393)
                ·
                  refine ⟨47849999714722702639705045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63799999619630270186273393 47849999714722702639705045)
                  ·
                    refine ⟨1121484368313813343118087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47849999714722702639705045 1121484368313813343118087)
                    ·
                      rfl

theorem cell23_6552249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_6552249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552249 prefixEnd_6552249 := by exact prefixLift 6552249
  have htrace : WordTrace (prefixWord ++ tailWord_6552249) baseStart_6552249 baseEnd_6552249 := by
    simpa [prefixWord, tailWord_6552249, baseEnd_6552249] using wordTrace_append hprefix tailTrace_6552249
  have hstable : (prefixWord ++ tailWord_6552249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552249).length < 2 ^ (prefixWord ++ tailWord_6552249).sum := by decide
  have hdescent : baseEnd_6552249 < baseStart_6552249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552257 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6552257 : Nat := 118140960795 + 6552257 * 2 ^ 59
def prefixEnd_6552257 : Nat := 4983230072969 + 3 ^ 40 * 6552257 * 2
def baseEnd_6552257 : Nat := 1121485737595558666018075

theorem tailTrace_6552257 : CollatzResearch.WordTrace tailWord_6552257 prefixEnd_6552257 1121485737595558666018075 := by
  unfold tailWord_6552257
  simp only [CollatzResearch.WordTrace]
  refine ⟨238980445823299400249671025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159320297215532933499780683 238980445823299400249671025)
  ·
    refine ⟨179235334367474550187253269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238980445823299400249671025 179235334367474550187253269)
    ·
      refine ⟨8401656298475369540027497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179235334367474550187253269 8401656298475369540027497)
      ·
        refine ⟨6301242223856527155020623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8401656298475369540027497 6301242223856527155020623)
        ·
          refine ⟨9451863335784790732530935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301242223856527155020623 9451863335784790732530935)
          ·
            refine ⟨14177795003677186098796403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451863335784790732530935 14177795003677186098796403)
            ·
              refine ⟨21266692505515779148194605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177795003677186098796403 21266692505515779148194605)
              ·
                refine ⟨7975009689568417180572977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21266692505515779148194605 7975009689568417180572977)
                ·
                  refine ⟨5981257267176312885429733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7975009689568417180572977 5981257267176312885429733)
                  ·
                    refine ⟨1121485737595558666018075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981257267176312885429733 1121485737595558666018075)
                    ·
                      rfl

theorem cell23_6552257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6552257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552257 prefixEnd_6552257 := by exact prefixLift 6552257
  have htrace : WordTrace (prefixWord ++ tailWord_6552257) baseStart_6552257 baseEnd_6552257 := by
    simpa [prefixWord, tailWord_6552257, baseEnd_6552257] using wordTrace_append hprefix tailTrace_6552257
  have hstable : (prefixWord ++ tailWord_6552257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552257).length < 2 ^ (prefixWord ++ tailWord_6552257).sum := by decide
  have hdescent : baseEnd_6552257 < baseStart_6552257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552273 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_6552273 : Nat := 118140960795 + 6552273 * 2 ^ 59
def prefixEnd_6552273 : Nat := 4983230072969 + 3 ^ 40 * 6552273 * 2
def baseEnd_6552273 : Nat := 3364465428477147935454151

theorem tailTrace_6552273 : CollatzResearch.WordTrace tailWord_6552273 prefixEnd_6552273 3364465428477147935454151 := by
  unfold tailWord_6552273
  simp only [CollatzResearch.WordTrace]
  refine ⟨238981029391241434982253473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159320686260827623321502315 238981029391241434982253473)
  ·
    refine ⟨179235772043431076236690105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238981029391241434982253473 179235772043431076236690105)
    ·
      refine ⟨134426829032573307177517579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179235772043431076236690105 134426829032573307177517579)
      ·
        refine ⟨201640243548859960766276369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134426829032573307177517579 201640243548859960766276369)
        ·
          refine ⟨151230182661644970574707277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201640243548859960766276369 151230182661644970574707277)
          ·
            refine ⟨56711318498116863965515229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151230182661644970574707277 56711318498116863965515229)
            ·
              refine ⟨21266744436793823987068211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56711318498116863965515229 21266744436793823987068211)
              ·
                refine ⟨31900116655190735980602317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21266744436793823987068211 31900116655190735980602317)
                ·
                  refine ⟨11962543745696525992725869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31900116655190735980602317 11962543745696525992725869)
                  ·
                    refine ⟨4485953904636197247272201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11962543745696525992725869 4485953904636197247272201)
                    ·
                      refine ⟨3364465428477147935454151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4485953904636197247272201 3364465428477147935454151)
                      ·
                        rfl

theorem cell23_6552273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_6552273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552273 prefixEnd_6552273 := by exact prefixLift 6552273
  have htrace : WordTrace (prefixWord ++ tailWord_6552273) baseStart_6552273 baseEnd_6552273 := by
    simpa [prefixWord, tailWord_6552273, baseEnd_6552273] using wordTrace_append hprefix tailTrace_6552273
  have hstable : (prefixWord ++ tailWord_6552273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552273).length < 2 ^ (prefixWord ++ tailWord_6552273).sum := by decide
  have hdescent : baseEnd_6552273 < baseStart_6552273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552299 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_6552299 : Nat := 118140960795 + 6552299 * 2 ^ 59
def prefixEnd_6552299 : Nat := 4983230072969 + 3 ^ 40 * 6552299 * 2
def baseEnd_6552299 : Nat := 3364478778974164833729031

theorem tailTrace_6552299 : CollatzResearch.WordTrace tailWord_6552299 prefixEnd_6552299 3364478778974164833729031 := by
  unfold tailWord_6552299
  simp only [CollatzResearch.WordTrace]
  refine ⟨238981977689147241422699951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159321318459431494281799967 238981977689147241422699951)
  ·
    refine ⟨358472966533720862134049927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238981977689147241422699951 358472966533720862134049927)
    ·
      refine ⟨537709449800581293201074891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358472966533720862134049927 537709449800581293201074891)
      ·
        refine ⟨806564174700871939801612337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537709449800581293201074891 806564174700871939801612337)
        ·
          refine ⟨604923131025653954851209253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806564174700871939801612337 604923131025653954851209253)
          ·
            refine ⟨113423087067310116534601735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 604923131025653954851209253 113423087067310116534601735)
            ·
              refine ⟨170134630600965174801902603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113423087067310116534601735 170134630600965174801902603)
              ·
                refine ⟨255201945901447762202853905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170134630600965174801902603 255201945901447762202853905)
                ·
                  refine ⟨191401459426085821652140429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255201945901447762202853905 191401459426085821652140429)
                  ·
                    refine ⟨71775547284782183119552661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191401459426085821652140429 71775547284782183119552661)
                    ·
                      refine ⟨3364478778974164833729031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71775547284782183119552661 3364478778974164833729031)
                      ·
                        rfl

theorem cell23_6552299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_6552299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552299 prefixEnd_6552299 := by exact prefixLift 6552299
  have htrace : WordTrace (prefixWord ++ tailWord_6552299) baseStart_6552299 baseEnd_6552299 := by
    simpa [prefixWord, tailWord_6552299, baseEnd_6552299] using wordTrace_append hprefix tailTrace_6552299
  have hstable : (prefixWord ++ tailWord_6552299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552299).length < 2 ^ (prefixWord ++ tailWord_6552299).sum := by decide
  have hdescent : baseEnd_6552299 < baseStart_6552299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552316 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_6552316 : Nat := 118140960795 + 6552316 * 2 ^ 59
def prefixEnd_6552316 : Nat := 4983230072969 + 3 ^ 40 * 6552316 * 2
def baseEnd_6552316 : Nat := 3364487508145291267216453

theorem tailTrace_6552316 : CollatzResearch.WordTrace tailWord_6552316 prefixEnd_6552316 3364487508145291267216453 := by
  unfold tailWord_6552316
  simp only [CollatzResearch.WordTrace]
  refine ⟨119491298865042826663034401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159321731820057102217379201 119491298865042826663034401)
  ·
    refine ⟨89618474148782119997275801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119491298865042826663034401 89618474148782119997275801)
    ·
      refine ⟨67213855611586589997956851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89618474148782119997275801 67213855611586589997956851)
      ·
        refine ⟨100820783417379884996935277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67213855611586589997956851 100820783417379884996935277)
        ·
          refine ⟨37807793781517456873850729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100820783417379884996935277 37807793781517456873850729)
          ·
            refine ⟨28355845336138092655388047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37807793781517456873850729 28355845336138092655388047)
            ·
              refine ⟨42533768004207138983082071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28355845336138092655388047 42533768004207138983082071)
              ·
                refine ⟨63800652006310708474623107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42533768004207138983082071 63800652006310708474623107)
                ·
                  refine ⟨95700978009466062711934661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63800652006310708474623107 95700978009466062711934661)
                  ·
                    refine ⟨17943933376774886758487749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95700978009466062711934661 17943933376774886758487749)
                    ·
                      refine ⟨3364487508145291267216453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17943933376774886758487749 3364487508145291267216453)
                      ·
                        rfl

theorem cell23_6552316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_6552316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552316 prefixEnd_6552316 := by exact prefixLift 6552316
  have htrace : WordTrace (prefixWord ++ tailWord_6552316) baseStart_6552316 baseEnd_6552316 := by
    simpa [prefixWord, tailWord_6552316, baseEnd_6552316] using wordTrace_append hprefix tailTrace_6552316
  have hstable : (prefixWord ++ tailWord_6552316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552316).length < 2 ^ (prefixWord ++ tailWord_6552316).sum := by decide
  have hdescent : baseEnd_6552316 < baseStart_6552316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552354 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_6552354 : Nat := 118140960795 + 6552354 * 2 ^ 59
def prefixEnd_6552354 : Nat := 4983230072969 + 3 ^ 40 * 6552354 * 2
def baseEnd_6552354 : Nat := 3364507020410162118541279

theorem tailTrace_6552354 : CollatzResearch.WordTrace tailWord_6552354 prefixEnd_6552354 3364507020410162118541279 := by
  unfold tailWord_6552354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59745995925986996453988029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159322655802631990543968077 59745995925986996453988029)
  ·
    refine ⟨22404748472245123670245511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59745995925986996453988029 22404748472245123670245511)
    ·
      refine ⟨33607122708367685505368267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22404748472245123670245511 33607122708367685505368267)
      ·
        refine ⟨50410684062551528258052401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33607122708367685505368267 50410684062551528258052401)
        ·
          refine ⟨37808013046913646193539301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50410684062551528258052401 37808013046913646193539301)
          ·
            refine ⟨7089002446296308661288619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37808013046913646193539301 7089002446296308661288619)
            ·
              refine ⟨10633503669444462991932929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089002446296308661288619 10633503669444462991932929)
              ·
                refine ⟨7975127752083347243949697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10633503669444462991932929 7975127752083347243949697)
                ·
                  refine ⟨5981345814062510432962273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7975127752083347243949697 5981345814062510432962273)
                  ·
                    refine ⟨4486009360546882824721705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5981345814062510432962273 4486009360546882824721705)
                    ·
                      refine ⟨3364507020410162118541279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486009360546882824721705 3364507020410162118541279)
                      ·
                        rfl

theorem cell23_6552354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_6552354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552354 prefixEnd_6552354 := by exact prefixLift 6552354
  have htrace : WordTrace (prefixWord ++ tailWord_6552354) baseStart_6552354 baseEnd_6552354 := by
    simpa [prefixWord, tailWord_6552354, baseEnd_6552354] using wordTrace_append hprefix tailTrace_6552354
  have hstable : (prefixWord ++ tailWord_6552354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552354).length < 2 ^ (prefixWord ++ tailWord_6552354).sum := by decide
  have hdescent : baseEnd_6552354 < baseStart_6552354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552376 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6552376 : Nat := 118140960795 + 6552376 * 2 ^ 59
def prefixEnd_6552376 : Nat := 4983230072969 + 3 ^ 40 * 6552376 * 2
def baseEnd_6552376 : Nat := 3364518316984561032466177

theorem tailTrace_6552376 : CollatzResearch.WordTrace tailWord_6552376 prefixEnd_6552376 3364518316984561032466177 := by
  unfold tailWord_6552376
  simp only [CollatzResearch.WordTrace]
  refine ⟨119492393054934141786626491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159323190739912189048835321 119492393054934141786626491)
  ·
    refine ⟨179238589582401212679939737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119492393054934141786626491 179238589582401212679939737)
    ·
      refine ⟨134428942186800909509954803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179238589582401212679939737 134428942186800909509954803)
      ·
        refine ⟨201643413280201364264932205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134428942186800909509954803 201643413280201364264932205)
        ·
          refine ⟨75616279980075511599349577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201643413280201364264932205 75616279980075511599349577)
          ·
            refine ⟨56712209985056633699512183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75616279980075511599349577 56712209985056633699512183)
            ·
              refine ⟨85068314977584950549268275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56712209985056633699512183 85068314977584950549268275)
              ·
                refine ⟨127602472466377425823902413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85068314977584950549268275 127602472466377425823902413)
                ·
                  refine ⟨47850927174891534683963405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127602472466377425823902413 47850927174891534683963405)
                  ·
                    refine ⟨17944097690584325506486277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47850927174891534683963405 17944097690584325506486277)
                    ·
                      refine ⟨3364518316984561032466177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17944097690584325506486277 3364518316984561032466177)
                      ·
                        rfl

theorem cell23_6552376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6552376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552376 prefixEnd_6552376 := by exact prefixLift 6552376
  have htrace : WordTrace (prefixWord ++ tailWord_6552376) baseStart_6552376 baseEnd_6552376 := by
    simpa [prefixWord, tailWord_6552376, baseEnd_6552376] using wordTrace_append hprefix tailTrace_6552376
  have hstable : (prefixWord ++ tailWord_6552376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552376).length < 2 ^ (prefixWord ++ tailWord_6552376).sum := by decide
  have hdescent : baseEnd_6552376 < baseStart_6552376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552416 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 8]
def baseStart_6552416 : Nat := 118140960795 + 6552416 * 2 ^ 59
def prefixEnd_6552416 : Nat := 4983230072969 + 3 ^ 40 * 6552416 * 2
def baseEnd_6552416 : Nat := 373837650690082319551777

theorem tailTrace_6552416 : CollatzResearch.WordTrace tailWord_6552416 prefixEnd_6552416 373837650690082319551777 := by
  unfold tailWord_6552416
  simp only [CollatzResearch.WordTrace]
  refine ⟨119493122514861685202354551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159324163353148913603139401 119493122514861685202354551)
  ·
    refine ⟨179239683772292527803531827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119493122514861685202354551 179239683772292527803531827)
    ·
      refine ⟨268859525658438791705297741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179239683772292527803531827 268859525658438791705297741)
      ·
        refine ⟨100822322121914546889486653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268859525658438791705297741 100822322121914546889486653)
        ·
          refine ⟨37808370795717955083557495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100822322121914546889486653 37808370795717955083557495)
          ·
            refine ⟨56712556193576932625336243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37808370795717955083557495 56712556193576932625336243)
            ·
              refine ⟨85068834290365398938004365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56712556193576932625336243 85068834290365398938004365)
              ·
                refine ⟨31900812858887024601751637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85068834290365398938004365 31900812858887024601751637)
                ·
                  refine ⟨373837650690082319551777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31900812858887024601751637 373837650690082319551777)
                  ·
                    rfl

theorem cell23_6552416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_6552416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552416 prefixEnd_6552416 := by exact prefixLift 6552416
  have htrace : WordTrace (prefixWord ++ tailWord_6552416) baseStart_6552416 baseEnd_6552416 := by
    simpa [prefixWord, tailWord_6552416, baseEnd_6552416] using wordTrace_append hprefix tailTrace_6552416
  have hstable : (prefixWord ++ tailWord_6552416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552416).length < 2 ^ (prefixWord ++ tailWord_6552416).sum := by decide
  have hdescent : baseEnd_6552416 < baseStart_6552416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552420 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_6552420 : Nat := 118140960795 + 6552420 * 2 ^ 59
def prefixEnd_6552420 : Nat := 4983230072969 + 3 ^ 40 * 6552420 * 2
def baseEnd_6552420 : Nat := 1121513636711119620105325

theorem tailTrace_6552420 : CollatzResearch.WordTrace tailWord_6552420 prefixEnd_6552420 1121513636711119620105325 := by
  unfold tailWord_6552420
  simp only [CollatzResearch.WordTrace]
  refine ⟨119493195460854439543927357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159324260614472586058569809 119493195460854439543927357)
  ·
    refine ⟨44809948297820414828972759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119493195460854439543927357 44809948297820414828972759)
    ·
      refine ⟨67214922446730622243459139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44809948297820414828972759 67214922446730622243459139)
      ·
        refine ⟨100822383670095933365188709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67214922446730622243459139 100822383670095933365188709)
        ·
          refine ⟨18904196938142987505972883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100822383670095933365188709 18904196938142987505972883)
          ·
            refine ⟨28356295407214481258959325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18904196938142987505972883 28356295407214481258959325)
            ·
              refine ⟨10633610777705430472109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28356295407214481258959325 10633610777705430472109747)
              ·
                refine ⟨15950416166558145708164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10633610777705430472109747 15950416166558145708164621)
                ·
                  refine ⟨5981406062459304640561733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15950416166558145708164621 5981406062459304640561733)
                  ·
                    refine ⟨1121513636711119620105325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981406062459304640561733 1121513636711119620105325)
                    ·
                      rfl

theorem cell23_6552420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_6552420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552420 prefixEnd_6552420 := by exact prefixLift 6552420
  have htrace : WordTrace (prefixWord ++ tailWord_6552420) baseStart_6552420 baseEnd_6552420 := by
    simpa [prefixWord, tailWord_6552420, baseEnd_6552420] using wordTrace_append hprefix tailTrace_6552420
  have hstable : (prefixWord ++ tailWord_6552420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552420).length < 2 ^ (prefixWord ++ tailWord_6552420).sum := by decide
  have hdescent : baseEnd_6552420 < baseStart_6552420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552433 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 6]
def baseStart_6552433 : Nat := 118140960795 + 6552433 * 2 ^ 59
def prefixEnd_6552433 : Nat := 4983230072969 + 3 ^ 40 * 6552433 * 2
def baseEnd_6552433 : Nat := 373838620597985256605935

theorem tailTrace_6552433 : CollatzResearch.WordTrace tailWord_6552433 prefixEnd_6552433 373838620597985256605935 := by
  unfold tailWord_6552433
  simp only [CollatzResearch.WordTrace]
  refine ⟨238986865070661782308077953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159324576713774521538718635 238986865070661782308077953)
  ·
    refine ⟨179240148802996336731058465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238986865070661782308077953 179240148802996336731058465)
    ·
      refine ⟨134430111602247252548293849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179240148802996336731058465 134430111602247252548293849)
      ·
        refine ⟨100822583701685439411220387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134430111602247252548293849 100822583701685439411220387)
        ·
          refine ⟨151233875552528159116830581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100822583701685439411220387 151233875552528159116830581)
          ·
            refine ⟨14178175833049514917202867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151233875552528159116830581 14178175833049514917202867)
            ·
              refine ⟨21267263749574272375804301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178175833049514917202867 21267263749574272375804301)
              ·
                refine ⟨7975223906090352140926613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21267263749574272375804301 7975223906090352140926613)
                ·
                  refine ⟨373838620597985256605935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7975223906090352140926613 373838620597985256605935)
                  ·
                    rfl

theorem cell23_6552433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_6552433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552433 prefixEnd_6552433 := by exact prefixLift 6552433
  have htrace : WordTrace (prefixWord ++ tailWord_6552433) baseStart_6552433 baseEnd_6552433 := by
    simpa [prefixWord, tailWord_6552433, baseEnd_6552433] using wordTrace_append hprefix tailTrace_6552433
  have hstable : (prefixWord ++ tailWord_6552433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552433).length < 2 ^ (prefixWord ++ tailWord_6552433).sum := by decide
  have hdescent : baseEnd_6552433 < baseStart_6552433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552483 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4]
def baseStart_6552483 : Nat := 118140960795 + 6552483 * 2 ^ 59
def prefixEnd_6552483 : Nat := 4983230072969 + 3 ^ 40 * 6552483 * 2
def baseEnd_6552483 : Nat := 3364573259414592113828185

theorem tailTrace_6552483 : CollatzResearch.WordTrace tailWord_6552483 prefixEnd_6552483 3364573259414592113828185 := by
  unfold tailWord_6552483
  simp only [CollatzResearch.WordTrace]
  refine ⟨238988688720480640847398103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159325792480320427231598735 238988688720480640847398103)
  ·
    refine ⟨358483033080720961271097155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238988688720480640847398103 358483033080720961271097155)
    ·
      refine ⟨537724549621081441906645733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358483033080720961271097155 537724549621081441906645733)
      ·
        refine ⟨100823353053952770357496075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537724549621081441906645733 100823353053952770357496075)
        ·
          refine ⟨151235029580929155536244113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100823353053952770357496075 151235029580929155536244113)
          ·
            refine ⟨113426272185696866652183085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151235029580929155536244113 113426272185696866652183085)
            ·
              refine ⟨42534852069636324994568657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113426272185696866652183085 42534852069636324994568657)
              ·
                refine ⟨31901139052227243745926493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42534852069636324994568657 31901139052227243745926493)
                ·
                  refine ⟨11962927144585216404722435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31901139052227243745926493 11962927144585216404722435)
                  ·
                    refine ⟨17944390716877824607083653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11962927144585216404722435 17944390716877824607083653)
                    ·
                      refine ⟨3364573259414592113828185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17944390716877824607083653 3364573259414592113828185)
                      ·
                        rfl

theorem cell23_6552483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_6552483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552483 prefixEnd_6552483 := by exact prefixLift 6552483
  have htrace : WordTrace (prefixWord ++ tailWord_6552483) baseStart_6552483 baseEnd_6552483 := by
    simpa [prefixWord, tailWord_6552483, baseEnd_6552483] using wordTrace_append hprefix tailTrace_6552483
  have hstable : (prefixWord ++ tailWord_6552483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552483).length < 2 ^ (prefixWord ++ tailWord_6552483).sum := by decide
  have hdescent : baseEnd_6552483 < baseStart_6552483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552510 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_6552510 : Nat := 118140960795 + 6552510 * 2 ^ 59
def prefixEnd_6552510 : Nat := 4983230072969 + 3 ^ 40 * 6552510 * 2
def baseEnd_6552510 : Nat := 1121529041130754502730187

theorem tailTrace_6552510 : CollatzResearch.WordTrace tailWord_6552510 prefixEnd_6552510 1121529041130754502730187 := by
  unfold tailWord_6552510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873709186422853057328873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159326448994255216305753989 29873709186422853057328873)
  ·
    refine ⟨22405281889817139792996655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873709186422853057328873 22405281889817139792996655)
    ·
      refine ⟨33607922834725709689494983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22405281889817139792996655 33607922834725709689494983)
      ·
        refine ⟨50411884252088564534242475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33607922834725709689494983 50411884252088564534242475)
        ·
          refine ⟨75617826378132846801363713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50411884252088564534242475 75617826378132846801363713)
          ·
            refine ⟨56713369783599635101022785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75617826378132846801363713 56713369783599635101022785)
            ·
              refine ⟨42535027337699726325767089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56713369783599635101022785 42535027337699726325767089)
              ·
                refine ⟨31901270503274794744325317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42535027337699726325767089 31901270503274794744325317)
                ·
                  refine ⟨5981488219364024014560997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31901270503274794744325317 5981488219364024014560997)
                  ·
                    refine ⟨1121529041130754502730187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981488219364024014560997 1121529041130754502730187)
                    ·
                      rfl

theorem cell23_6552510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_6552510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552510 prefixEnd_6552510 := by exact prefixLift 6552510
  have htrace : WordTrace (prefixWord ++ tailWord_6552510) baseStart_6552510 baseEnd_6552510 := by
    simpa [prefixWord, tailWord_6552510, baseEnd_6552510] using wordTrace_append hprefix tailTrace_6552510
  have hstable : (prefixWord ++ tailWord_6552510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552510).length < 2 ^ (prefixWord ++ tailWord_6552510).sum := by decide
  have hdescent : baseEnd_6552510 < baseStart_6552510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552518 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6552518 : Nat := 118140960795 + 6552518 * 2 ^ 59
def prefixEnd_6552518 : Nat := 4983230072969 + 3 ^ 40 * 6552518 * 2
def baseEnd_6552518 : Nat := 373843470137499941876725

theorem tailTrace_6552518 : CollatzResearch.WordTrace tailWord_6552518 prefixEnd_6552518 373843470137499941876725 := by
  unfold tailWord_6552518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468436414854807557028819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159326643516902561216614805 7468436414854807557028819)
  ·
    refine ⟨11202654622282211335543229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468436414854807557028819 11202654622282211335543229)
    ·
      refine ⟨4200995483355829250828711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11202654622282211335543229 4200995483355829250828711)
      ·
        refine ⟨6301493225033743876243067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200995483355829250828711 6301493225033743876243067)
        ·
          refine ⟨9452239837550615814364601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301493225033743876243067 9452239837550615814364601)
          ·
            refine ⟨7089179878162961860773451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9452239837550615814364601 7089179878162961860773451)
            ·
              refine ⟨10633769817244442791160177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089179878162961860773451 10633769817244442791160177)
              ·
                refine ⟨7975327362933332093370133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10633769817244442791160177 7975327362933332093370133)
                ·
                  refine ⟨373843470137499941876725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7975327362933332093370133 373843470137499941876725)
                  ·
                    rfl

theorem cell23_6552518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6552518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552518 prefixEnd_6552518 := by exact prefixLift 6552518
  have htrace : WordTrace (prefixWord ++ tailWord_6552518) baseStart_6552518 baseEnd_6552518 := by
    simpa [prefixWord, tailWord_6552518, baseEnd_6552518] using wordTrace_append hprefix tailTrace_6552518
  have hstable : (prefixWord ++ tailWord_6552518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552518).length < 2 ^ (prefixWord ++ tailWord_6552518).sum := by decide
  have hdescent : baseEnd_6552518 < baseStart_6552518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552527 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 2, 4]
def baseStart_6552527 : Nat := 118140960795 + 6552527 * 2 ^ 59
def prefixEnd_6552527 : Nat := 4983230072969 + 3 ^ 40 * 6552527 * 2
def baseEnd_6552527 : Nat := 1121531950854463313892661

theorem tailTrace_6552527 : CollatzResearch.WordTrace tailWord_6552527 prefixEnd_6552527 1121531950854463313892661 := by
  unfold tailWord_6552527
  simp only [CollatzResearch.WordTrace]
  refine ⟨238990293532321236361999835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159326862354880824241333223 238990293532321236361999835)
  ·
    refine ⟨358485440298481854542999753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238990293532321236361999835 358485440298481854542999753)
    ·
      refine ⟨268864080223861390907249815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358485440298481854542999753 268864080223861390907249815)
      ·
        refine ⟨403296120335792086360874723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268864080223861390907249815 403296120335792086360874723)
        ·
          refine ⟨604944180503688129541312085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403296120335792086360874723 604944180503688129541312085)
          ·
            refine ⟨7089189615277595268062251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 604944180503688129541312085 7089189615277595268062251)
            ·
              refine ⟨10633784422916392902093377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089189615277595268062251 10633784422916392902093377)
              ·
                refine ⟨7975338317187294676570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10633784422916392902093377 7975338317187294676570033)
                ·
                  refine ⟨5981503737890471007427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7975338317187294676570033 5981503737890471007427525)
                  ·
                    refine ⟨1121531950854463313892661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981503737890471007427525 1121531950854463313892661)
                    ·
                      rfl

theorem cell23_6552527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_6552527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552527 prefixEnd_6552527 := by exact prefixLift 6552527
  have htrace : WordTrace (prefixWord ++ tailWord_6552527) baseStart_6552527 baseEnd_6552527 := by
    simpa [prefixWord, tailWord_6552527, baseEnd_6552527] using wordTrace_append hprefix tailTrace_6552527
  have hstable : (prefixWord ++ tailWord_6552527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552527).length < 2 ^ (prefixWord ++ tailWord_6552527).sum := by decide
  have hdescent : baseEnd_6552527 < baseStart_6552527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552573 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_6552573 : Nat := 118140960795 + 6552573 * 2 ^ 59
def prefixEnd_6552573 : Nat := 4983230072969 + 3 ^ 40 * 6552573 * 2
def baseEnd_6552573 : Nat := 3364619472673496761702771

theorem tailTrace_6552573 : CollatzResearch.WordTrace tailWord_6552573 prefixEnd_6552573 3364619472673496761702771 := by
  unfold tailWord_6552573
  simp only [CollatzResearch.WordTrace]
  refine ⟨238991971290154586218174373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159327980860103057478782915 238991971290154586218174373)
  ·
    refine ⟨44810994616903984915907695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238991971290154586218174373 44810994616903984915907695)
    ·
      refine ⟨67216491925355977373861543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44810994616903984915907695 67216491925355977373861543)
      ·
        refine ⟨100824737888033966060792315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67216491925355977373861543 100824737888033966060792315)
        ·
          refine ⟨151237106832050949091188473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100824737888033966060792315 151237106832050949091188473)
          ·
            refine ⟨113427830124038211818391355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151237106832050949091188473 113427830124038211818391355)
            ·
              refine ⟨170141745186057317727587033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113427830124038211818391355 170141745186057317727587033)
              ·
                refine ⟨127606308889542988295690275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170141745186057317727587033 127606308889542988295690275)
                ·
                  refine ⟨191409463334314482443535413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127606308889542988295690275 191409463334314482443535413)
                  ·
                    refine ⟨17944637187591982729081445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 191409463334314482443535413 17944637187591982729081445)
                    ·
                      refine ⟨3364619472673496761702771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17944637187591982729081445 3364619472673496761702771)
                      ·
                        rfl

theorem cell23_6552573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_6552573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552573 prefixEnd_6552573 := by exact prefixLift 6552573
  have htrace : WordTrace (prefixWord ++ tailWord_6552573) baseStart_6552573 baseEnd_6552573 := by
    simpa [prefixWord, tailWord_6552573, baseEnd_6552573] using wordTrace_append hprefix tailTrace_6552573
  have hstable : (prefixWord ++ tailWord_6552573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552573).length < 2 ^ (prefixWord ++ tailWord_6552573).sum := by decide
  have hdescent : baseEnd_6552573 < baseStart_6552573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552603 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_6552603 : Nat := 118140960795 + 6552603 * 2 ^ 59
def prefixEnd_6552603 : Nat := 4983230072969 + 3 ^ 40 * 6552603 * 2
def baseEnd_6552603 : Nat := 3364634877093131644327633

theorem tailTrace_6552603 : CollatzResearch.WordTrace tailWord_6552603 prefixEnd_6552603 3364634877093131644327633 := by
  unfold tailWord_6552603
  simp only [CollatzResearch.WordTrace]
  refine ⟨238993065480045901341766463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159328710320030600894510975 238993065480045901341766463)
  ·
    refine ⟨358489598220068852012649695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238993065480045901341766463 358489598220068852012649695)
    ·
      refine ⟨537734397330103278018974543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358489598220068852012649695 537734397330103278018974543)
      ·
        refine ⟨806601595995154917028461815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537734397330103278018974543 806601595995154917028461815)
        ·
          refine ⟨1209902393992732375542692723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806601595995154917028461815 1209902393992732375542692723)
          ·
            refine ⟨1814853590989098563314039085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209902393992732375542692723 1814853590989098563314039085)
            ·
              refine ⟨680570096620911961242764657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1814853590989098563314039085 680570096620911961242764657)
              ·
                refine ⟨510427572465683970932073493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680570096620911961242764657 510427572465683970932073493)
                ·
                  refine ⟨23926292459328936137440945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 510427572465683970932073493 23926292459328936137440945)
                  ·
                    refine ⟨17944719344496702103080709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23926292459328936137440945 17944719344496702103080709)
                    ·
                      refine ⟨3364634877093131644327633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17944719344496702103080709 3364634877093131644327633)
                      ·
                        rfl

theorem cell23_6552603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_6552603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552603 prefixEnd_6552603 := by exact prefixLift 6552603
  have htrace : WordTrace (prefixWord ++ tailWord_6552603) baseStart_6552603 baseEnd_6552603 := by
    simpa [prefixWord, tailWord_6552603, baseEnd_6552603] using wordTrace_append hprefix tailTrace_6552603
  have hstable : (prefixWord ++ tailWord_6552603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552603).length < 2 ^ (prefixWord ++ tailWord_6552603).sum := by decide
  have hdescent : baseEnd_6552603 < baseStart_6552603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552610 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_6552610 : Nat := 118140960795 + 6552610 * 2 ^ 59
def prefixEnd_6552610 : Nat := 4983230072969 + 3 ^ 40 * 6552610 * 2
def baseEnd_6552610 : Nat := 3364638471457713116940101

theorem tailTrace_6552610 : CollatzResearch.WordTrace tailWord_6552610 prefixEnd_6552610 3364638471457713116940101 := by
  unfold tailWord_6552610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59748330197755135384317821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159328880527347027691514189 59748330197755135384317821)
  ·
    refine ⟨22405623824158175769119183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59748330197755135384317821 22405623824158175769119183)
    ·
      refine ⟨33608435736237263653678775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22405623824158175769119183 33608435736237263653678775)
      ·
        refine ⟨50412653604355895480518163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33608435736237263653678775 50412653604355895480518163)
        ·
          refine ⟨75618980406533843220777245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50412653604355895480518163 75618980406533843220777245)
          ·
            refine ⟨28357117652450191207791467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75618980406533843220777245 28357117652450191207791467)
            ·
              refine ⟨42535676478675286811687201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28357117652450191207791467 42535676478675286811687201)
              ·
                refine ⟨31901757359006465108765401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42535676478675286811687201 31901757359006465108765401)
                ·
                  refine ⟨23926318019254848831574051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31901757359006465108765401 23926318019254848831574051)
                  ·
                    refine ⟨35889477028882273247361077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23926318019254848831574051 35889477028882273247361077)
                    ·
                      refine ⟨3364638471457713116940101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35889477028882273247361077 3364638471457713116940101)
                      ·
                        rfl

theorem cell23_6552610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_6552610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552610 prefixEnd_6552610 := by exact prefixLift 6552610
  have htrace : WordTrace (prefixWord ++ tailWord_6552610) baseStart_6552610 baseEnd_6552610 := by
    simpa [prefixWord, tailWord_6552610, baseEnd_6552610] using wordTrace_append hprefix tailTrace_6552610
  have hstable : (prefixWord ++ tailWord_6552610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552610).length < 2 ^ (prefixWord ++ tailWord_6552610).sum := by decide
  have hdescent : baseEnd_6552610 < baseStart_6552610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552613 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 9]
def baseStart_6552613 : Nat := 118140960795 + 6552613 * 2 ^ 59
def prefixEnd_6552613 : Nat := 4983230072969 + 3 ^ 40 * 6552613 * 2
def baseEnd_6552613 : Nat := 373848890211075178355843

theorem tailTrace_6552613 : CollatzResearch.WordTrace tailWord_6552613 prefixEnd_6552613 373848890211075178355843 := by
  unfold tailWord_6552613
  simp only [CollatzResearch.WordTrace]
  refine ⟨238993430210009673049630493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159328953473339782033086995 238993430210009673049630493)
  ·
    refine ⟨89622536328753627393611435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238993430210009673049630493 89622536328753627393611435)
    ·
      refine ⟨134433804493130441090417153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89622536328753627393611435 134433804493130441090417153)
      ·
        refine ⟨100825353369847830817812865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134433804493130441090417153 100825353369847830817812865)
        ·
          refine ⟨75619015027385873113359649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100825353369847830817812865 75619015027385873113359649)
          ·
            refine ⟨56714261270539404835019737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75619015027385873113359649 56714261270539404835019737)
            ·
              refine ⟨42535695952904553626264803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56714261270539404835019737 42535695952904553626264803)
              ·
                refine ⟨63803543929356830439397205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42535695952904553626264803 63803543929356830439397205)
                ·
                  refine ⟨373848890211075178355843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63803543929356830439397205 373848890211075178355843)
                  ·
                    rfl

theorem cell23_6552613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_6552613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552613 prefixEnd_6552613 := by exact prefixLift 6552613
  have htrace : WordTrace (prefixWord ++ tailWord_6552613) baseStart_6552613 baseEnd_6552613 := by
    simpa [prefixWord, tailWord_6552613, baseEnd_6552613] using wordTrace_append hprefix tailTrace_6552613
  have hstable : (prefixWord ++ tailWord_6552613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552613).length < 2 ^ (prefixWord ++ tailWord_6552613).sum := by decide
  have hdescent : baseEnd_6552613 < baseStart_6552613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552628 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_6552628 : Nat := 118140960795 + 6552628 * 2 ^ 59
def prefixEnd_6552628 : Nat := 4983230072969 + 3 ^ 40 * 6552628 * 2
def baseEnd_6552628 : Nat := 3364647714109494046515019

theorem tailTrace_6552628 : CollatzResearch.WordTrace tailWord_6552628 prefixEnd_6552628 3364647714109494046515019 := by
  unfold tailWord_6552628
  simp only [CollatzResearch.WordTrace]
  refine ⟨119496988652477665305713269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159329318203303553740951025 119496988652477665305713269)
  ·
    refine ⟨11202842686169781122410619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119496988652477665305713269 11202842686169781122410619)
    ·
      refine ⟨16804264029254671683615929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11202842686169781122410619 16804264029254671683615929)
      ·
        refine ⟨12603198021941003762711947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16804264029254671683615929 12603198021941003762711947)
        ·
          refine ⟨18904797032911505644067921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12603198021941003762711947 18904797032911505644067921)
          ·
            refine ⟨14178597774683629233050941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18904797032911505644067921 14178597774683629233050941)
            ·
              refine ⟨5316974165506360962394103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14178597774683629233050941 5316974165506360962394103)
              ·
                refine ⟨7975461248259541443591155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316974165506360962394103 7975461248259541443591155)
                ·
                  refine ⟨11963191872389312165386733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7975461248259541443591155 11963191872389312165386733)
                  ·
                    refine ⟨4486196952145992062020025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11963191872389312165386733 4486196952145992062020025)
                    ·
                      refine ⟨3364647714109494046515019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486196952145992062020025 3364647714109494046515019)
                      ·
                        rfl

theorem cell23_6552628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_6552628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552628 prefixEnd_6552628 := by exact prefixLift 6552628
  have htrace : WordTrace (prefixWord ++ tailWord_6552628) baseStart_6552628 baseEnd_6552628 := by
    simpa [prefixWord, tailWord_6552628, baseEnd_6552628] using wordTrace_append hprefix tailTrace_6552628
  have hstable : (prefixWord ++ tailWord_6552628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552628).length < 2 ^ (prefixWord ++ tailWord_6552628).sum := by decide
  have hdescent : baseEnd_6552628 < baseStart_6552628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552640 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_6552640 : Nat := 118140960795 + 6552640 * 2 ^ 59
def prefixEnd_6552640 : Nat := 4983230072969 + 3 ^ 40 * 6552640 * 2
def baseEnd_6552640 : Nat := 3364653875877347999564963

theorem tailTrace_6552640 : CollatzResearch.WordTrace tailWord_6552640 prefixEnd_6552640 3364653875877347999564963 := by
  unfold tailWord_6552640
  simp only [CollatzResearch.WordTrace]
  refine ⟨119497207490455928330431687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159329609987274571107242249 119497207490455928330431687)
  ·
    refine ⟨179245811235683892495647531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119497207490455928330431687 179245811235683892495647531)
    ·
      refine ⟨268868716853525838743471297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179245811235683892495647531 268868716853525838743471297)
      ·
        refine ⟨201651537640144379057603473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268868716853525838743471297 201651537640144379057603473)
        ·
          refine ⟨151238653230108284293202605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201651537640144379057603473 151238653230108284293202605)
          ·
            refine ⟨56714494961290606609950977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151238653230108284293202605 56714494961290606609950977)
            ·
              refine ⟨42535871220967954957463233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56714494961290606609950977 42535871220967954957463233)
              ·
                refine ⟨31901903415725966218097425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42535871220967954957463233 31901903415725966218097425)
                ·
                  refine ⟨23926427561794474663573069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31901903415725966218097425 23926427561794474663573069)
                  ·
                    refine ⟨8972410335672927998839901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23926427561794474663573069 8972410335672927998839901)
                    ·
                      refine ⟨3364653875877347999564963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8972410335672927998839901 3364653875877347999564963)
                      ·
                        rfl

theorem cell23_6552640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_6552640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552640 prefixEnd_6552640 := by exact prefixLift 6552640
  have htrace : WordTrace (prefixWord ++ tailWord_6552640) baseStart_6552640 baseEnd_6552640 := by
    simpa [prefixWord, tailWord_6552640, baseEnd_6552640] using wordTrace_append hprefix tailTrace_6552640
  have hstable : (prefixWord ++ tailWord_6552640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552640).length < 2 ^ (prefixWord ++ tailWord_6552640).sum := by decide
  have hdescent : baseEnd_6552640 < baseStart_6552640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552647 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 5]
def baseStart_6552647 : Nat := 118140960795 + 6552647 * 2 ^ 59
def prefixEnd_6552647 : Nat := 4983230072969 + 3 ^ 40 * 6552647 * 2
def baseEnd_6552647 : Nat := 373850830026881052464159

theorem tailTrace_6552647 : CollatzResearch.WordTrace tailWord_6552647 prefixEnd_6552647 373850830026881052464159 := by
  unfold tailWord_6552647
  simp only [CollatzResearch.WordTrace]
  refine ⟨238994670291886496856368195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159329780194590997904245463 238994670291886496856368195)
  ·
    refine ⟨358492005437829745284552293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238994670291886496856368195 358492005437829745284552293)
    ·
      refine ⟨67217251019593077240853555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358492005437829745284552293 67217251019593077240853555)
      ·
        refine ⟨100825876529389615861280333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67217251019593077240853555 100825876529389615861280333)
        ·
          refine ⟨37809703698521105947980125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100825876529389615861280333 37809703698521105947980125)
          ·
            refine ⟨14178638886945414730492547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37809703698521105947980125 14178638886945414730492547)
            ·
              refine ⟨21267958330418122095738821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178638886945414730492547 21267958330418122095738821)
              ·
                refine ⟨3987742186953397892951029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21267958330418122095738821 3987742186953397892951029)
                ·
                  refine ⟨373850830026881052464159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3987742186953397892951029 373850830026881052464159)
                  ·
                    rfl

theorem cell23_6552647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 5].length) (baseStart_6552647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552647 prefixEnd_6552647 := by exact prefixLift 6552647
  have htrace : WordTrace (prefixWord ++ tailWord_6552647) baseStart_6552647 baseEnd_6552647 := by
    simpa [prefixWord, tailWord_6552647, baseEnd_6552647] using wordTrace_append hprefix tailTrace_6552647
  have hstable : (prefixWord ++ tailWord_6552647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552647).length < 2 ^ (prefixWord ++ tailWord_6552647).sum := by decide
  have hdescent : baseEnd_6552647 < baseStart_6552647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552660 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6552660 : Nat := 118140960795 + 6552660 * 2 ^ 59
def prefixEnd_6552660 : Nat := 4983230072969 + 3 ^ 40 * 6552660 * 2
def baseEnd_6552660 : Nat := 1121554715163479307104957

theorem tailTrace_6552660 : CollatzResearch.WordTrace tailWord_6552660 prefixEnd_6552660 1121554715163479307104957 := by
  unfold tailWord_6552660
  simp only [CollatzResearch.WordTrace]
  refine ⟨119497572220419700038295717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159330096293892933384394289 119497572220419700038295717)
  ·
    refine ⟨22405794791328693757180447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119497572220419700038295717 22405794791328693757180447)
    ·
      refine ⟨33608692186993040635770671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22405794791328693757180447 33608692186993040635770671)
      ·
        refine ⟨50413038280489560953656007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33608692186993040635770671 50413038280489560953656007)
        ·
          refine ⟨75619557420734341430484011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50413038280489560953656007 75619557420734341430484011)
          ·
            refine ⟨113429336131101512145726017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75619557420734341430484011 113429336131101512145726017)
            ·
              refine ⟨85072002098326134109294513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113429336131101512145726017 85072002098326134109294513)
              ·
                refine ⟨63804001573744600581970885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85072002098326134109294513 63804001573744600581970885)
                ·
                  refine ⟨11963250295077112609119541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63804001573744600581970885 11963250295077112609119541)
                  ·
                    refine ⟨1121554715163479307104957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11963250295077112609119541 1121554715163479307104957)
                    ·
                      rfl

theorem cell23_6552660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6552660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552660 prefixEnd_6552660 := by exact prefixLift 6552660
  have htrace : WordTrace (prefixWord ++ tailWord_6552660) baseStart_6552660 baseEnd_6552660 := by
    simpa [prefixWord, tailWord_6552660, baseEnd_6552660] using wordTrace_append hprefix tailTrace_6552660
  have hstable : (prefixWord ++ tailWord_6552660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552660).length < 2 ^ (prefixWord ++ tailWord_6552660).sum := by decide
  have hdescent : baseEnd_6552660 < baseStart_6552660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552707 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 3, 4]
def baseStart_6552707 : Nat := 118140960795 + 6552707 * 2 ^ 59
def prefixEnd_6552707 : Nat := 4983230072969 + 3 ^ 40 * 6552707 * 2
def baseEnd_6552707 : Nat := 1121562759693733079142385

theorem tailTrace_6552707 : CollatzResearch.WordTrace tailWord_6552707 prefixEnd_6552707 1121562759693733079142385 := by
  unfold tailWord_6552707
  simp only [CollatzResearch.WordTrace]
  refine ⟨238996858671669127103552375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159331239114446084735701583 238996858671669127103552375)
  ·
    refine ⟨358495288007503690655328563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238996858671669127103552375 358495288007503690655328563)
    ·
      refine ⟨537742932011255535982992845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358495288007503690655328563 537742932011255535982992845)
      ·
        refine ⟨201653599504220825993622317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537742932011255535982992845 201653599504220825993622317)
        ·
          refine ⟨75620099814082809747608369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201653599504220825993622317 75620099814082809747608369)
          ·
            refine ⟨56715074860562107310706277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75620099814082809747608369 56715074860562107310706277)
            ·
              refine ⟨10634076536355395120757427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56715074860562107310706277 10634076536355395120757427)
              ·
                refine ⟨15951114804533092681136141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634076536355395120757427 15951114804533092681136141)
                ·
                  refine ⟨5981668051699909755426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15951114804533092681136141 5981668051699909755426053)
                  ·
                    refine ⟨1121562759693733079142385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981668051699909755426053 1121562759693733079142385)
                    ·
                      rfl

theorem cell23_6552707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 4].length) (baseStart_6552707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552707 prefixEnd_6552707 := by exact prefixLift 6552707
  have htrace : WordTrace (prefixWord ++ tailWord_6552707) baseStart_6552707 baseEnd_6552707 := by
    simpa [prefixWord, tailWord_6552707, baseEnd_6552707] using wordTrace_append hprefix tailTrace_6552707
  have hstable : (prefixWord ++ tailWord_6552707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552707).length < 2 ^ (prefixWord ++ tailWord_6552707).sum := by decide
  have hdescent : baseEnd_6552707 < baseStart_6552707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552734 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6552734 : Nat := 118140960795 + 6552734 * 2 ^ 59
def prefixEnd_6552734 : Nat := 4983230072969 + 3 ^ 40 * 6552734 * 2
def baseEnd_6552734 : Nat := 3364702143058870631789531

theorem tailTrace_6552734 : CollatzResearch.WordTrace tailWord_6552734 prefixEnd_6552734 3364702143058870631789531 := by
  unfold tailWord_6552734
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874730430321413839348157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159331895628380873809856837 29874730430321413839348157)
  ·
    refine ⟨11203023911370530189755559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29874730430321413839348157 11203023911370530189755559)
    ·
      refine ⟨16804535867055795284633339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203023911370530189755559 16804535867055795284633339)
      ·
        refine ⟨25206803800583692926950009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16804535867055795284633339 25206803800583692926950009)
        ·
          refine ⟨18905102850437769695212507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25206803800583692926950009 18905102850437769695212507)
          ·
            refine ⟨28357654275656654542818761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18905102850437769695212507 28357654275656654542818761)
            ·
              refine ⟨21268240706742490907114071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28357654275656654542818761 21268240706742490907114071)
              ·
                refine ⟨31902361060113736360671107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21268240706742490907114071 31902361060113736360671107)
                ·
                  refine ⟨47853541590170604541006661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31902361060113736360671107 47853541590170604541006661)
                  ·
                    refine ⟨8972539048156988351438749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47853541590170604541006661 8972539048156988351438749)
                    ·
                      refine ⟨3364702143058870631789531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8972539048156988351438749 3364702143058870631789531)
                      ·
                        rfl

theorem cell23_6552734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6552734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552734 prefixEnd_6552734 := by exact prefixLift 6552734
  have htrace : WordTrace (prefixWord ++ tailWord_6552734) baseStart_6552734 baseEnd_6552734 := by
    simpa [prefixWord, tailWord_6552734, baseEnd_6552734] using wordTrace_append hprefix tailTrace_6552734
  have hstable : (prefixWord ++ tailWord_6552734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552734).length < 2 ^ (prefixWord ++ tailWord_6552734).sum := by decide
  have hdescent : baseEnd_6552734 < baseStart_6552734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552741 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_6552741 : Nat := 118140960795 + 6552741 * 2 ^ 59
def prefixEnd_6552741 : Nat := 4983230072969 + 3 ^ 40 * 6552741 * 2
def baseEnd_6552741 : Nat := 1121568579141150701467333

theorem tailTrace_6552741 : CollatzResearch.WordTrace tailWord_6552741 prefixEnd_6552741 1121568579141150701467333 := by
  unfold tailWord_6552741
  simp only [CollatzResearch.WordTrace]
  refine ⟨238998098753545950910290077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159332065835697300606860051 238998098753545950910290077)
  ·
    refine ⟨89624287032579731591358779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238998098753545950910290077 89624287032579731591358779)
    ·
      refine ⟨134436430548869597387038169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89624287032579731591358779 134436430548869597387038169)
      ·
        refine ⟨100827322911652198040278627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134436430548869597387038169 100827322911652198040278627)
        ·
          refine ⟨151240984367478297060417941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100827322911652198040278627 151240984367478297060417941)
          ·
            refine ⟨7089421142225545174707091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151240984367478297060417941 7089421142225545174707091)
            ·
              refine ⟨10634131713338317762060637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089421142225545174707091 10634131713338317762060637)
              ·
                refine ⟨3987799392501869160772739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10634131713338317762060637 3987799392501869160772739)
                ·
                  refine ⟨5981699088752803741159109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987799392501869160772739 5981699088752803741159109)
                  ·
                    refine ⟨1121568579141150701467333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981699088752803741159109 1121568579141150701467333)
                    ·
                      rfl

theorem cell23_6552741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_6552741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552741 prefixEnd_6552741 := by exact prefixLift 6552741
  have htrace : WordTrace (prefixWord ++ tailWord_6552741) baseStart_6552741 baseEnd_6552741 := by
    simpa [prefixWord, tailWord_6552741, baseEnd_6552741] using wordTrace_append hprefix tailTrace_6552741
  have hstable : (prefixWord ++ tailWord_6552741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552741).length < 2 ^ (prefixWord ++ tailWord_6552741).sum := by decide
  have hdescent : baseEnd_6552741 < baseStart_6552741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552810 : List Nat := [3, 1, 3, 1, 1, 14]
def baseStart_6552810 : Nat := 118140960795 + 6552810 * 2 ^ 59
def prefixEnd_6552810 : Nat := 4983230072969 + 3 ^ 40 * 6552810 * 2
def baseEnd_6552810 : Nat := 13846671471558075450367

theorem tailTrace_6552810 : CollatzResearch.WordTrace tailWord_6552810 prefixEnd_6552810 13846671471558075450367 := by
  unfold tailWord_6552810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59750153847573993923637971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159333743593530650463034589 59750153847573993923637971)
  ·
    refine ⟨89625230771360990885456957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59750153847573993923637971 89625230771360990885456957)
    ·
      refine ⟨33609461539260371582046359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89625230771360990885456957 33609461539260371582046359)
      ·
        refine ⟨50414192308890557373069539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33609461539260371582046359 50414192308890557373069539)
        ·
          refine ⟨75621288463335836059604309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50414192308890557373069539 75621288463335836059604309)
          ·
            refine ⟨13846671471558075450367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 75621288463335836059604309 13846671471558075450367)
            ·
              rfl

theorem cell23_6552810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 14].length) (baseStart_6552810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552810 prefixEnd_6552810 := by exact prefixLift 6552810
  have htrace : WordTrace (prefixWord ++ tailWord_6552810) baseStart_6552810 baseEnd_6552810 := by
    simpa [prefixWord, tailWord_6552810, baseEnd_6552810] using wordTrace_append hprefix tailTrace_6552810
  have hstable : (prefixWord ++ tailWord_6552810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552810).length < 2 ^ (prefixWord ++ tailWord_6552810).sum := by decide
  have hdescent : baseEnd_6552810 < baseStart_6552810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552814 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6552814 : Nat := 118140960795 + 6552814 * 2 ^ 59
def prefixEnd_6552814 : Nat := 4983230072969 + 3 ^ 40 * 6552814 * 2
def baseEnd_6552814 : Nat := 1121581073837076772929721

theorem tailTrace_6552814 : CollatzResearch.WordTrace tailWord_6552814 prefixEnd_6552814 1121581073837076772929721 := by
  unfold tailWord_6552814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29875095160285185547212187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159333840854854322918464997 29875095160285185547212187)
  ·
    refine ⟨44812642740427778320818281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29875095160285185547212187 44812642740427778320818281)
    ·
      refine ⟨33609482055320833740613711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44812642740427778320818281 33609482055320833740613711)
      ·
        refine ⟨50414223082981250610920567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33609482055320833740613711 50414223082981250610920567)
        ·
          refine ⟨75621334624471875916380851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50414223082981250610920567 75621334624471875916380851)
          ·
            refine ⟨113432001936707813874571277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75621334624471875916380851 113432001936707813874571277)
            ·
              refine ⟨42537000726265430202964229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113432001936707813874571277 42537000726265430202964229)
              ·
                refine ⟨7975687636174768163055793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42537000726265430202964229 7975687636174768163055793)
                ·
                  refine ⟨5981765727131076122291845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7975687636174768163055793 5981765727131076122291845)
                  ·
                    refine ⟨1121581073837076772929721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5981765727131076122291845 1121581073837076772929721)
                    ·
                      rfl

theorem cell23_6552814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6552814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552814 prefixEnd_6552814 := by exact prefixLift 6552814
  have htrace : WordTrace (prefixWord ++ tailWord_6552814) baseStart_6552814 baseEnd_6552814 := by
    simpa [prefixWord, tailWord_6552814, baseEnd_6552814] using wordTrace_append hprefix tailTrace_6552814
  have hstable : (prefixWord ++ tailWord_6552814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552814).length < 2 ^ (prefixWord ++ tailWord_6552814).sum := by decide
  have hdescent : baseEnd_6552814 < baseStart_6552814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552815 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 1, 1, 3]
def baseStart_6552815 : Nat := 118140960795 + 6552815 * 2 ^ 59
def prefixEnd_6552815 : Nat := 4983230072969 + 3 ^ 40 * 6552815 * 2
def baseEnd_6552815 : Nat := 3364743734991884814876659

theorem tailTrace_6552815 : CollatzResearch.WordTrace tailWord_6552815 prefixEnd_6552815 3364743734991884814876659 := by
  unfold tailWord_6552815
  simp only [CollatzResearch.WordTrace]
  refine ⟨239000797755277861548483899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159333865170185241032322599 239000797755277861548483899)
  ·
    refine ⟨358501196632916792322725849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239000797755277861548483899 358501196632916792322725849)
    ·
      refine ⟨268875897474687594242044387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358501196632916792322725849 268875897474687594242044387)
      ·
        refine ⟨403313846212031391363066581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268875897474687594242044387 403313846212031391363066581)
        ·
          refine ⟨9452668270594485735071873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 403313846212031391363066581 9452668270594485735071873)
          ·
            refine ⟨7089501202945864301303905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9452668270594485735071873 7089501202945864301303905)
            ·
              refine ⟨5317125902209398225977929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089501202945864301303905 5317125902209398225977929)
              ·
                refine ⟨3987844426657048669483447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5317125902209398225977929 3987844426657048669483447)
                ·
                  refine ⟨5981766639985573004225171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987844426657048669483447 5981766639985573004225171)
                  ·
                    refine ⟨8972649959978359506337757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5981766639985573004225171 8972649959978359506337757)
                    ·
                      refine ⟨3364743734991884814876659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8972649959978359506337757 3364743734991884814876659)
                      ·
                        rfl

theorem cell23_6552815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 1, 3].length) (baseStart_6552815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552815 prefixEnd_6552815 := by exact prefixLift 6552815
  have htrace : WordTrace (prefixWord ++ tailWord_6552815) baseStart_6552815 baseEnd_6552815 := by
    simpa [prefixWord, tailWord_6552815, baseEnd_6552815] using wordTrace_append hprefix tailTrace_6552815
  have hstable : (prefixWord ++ tailWord_6552815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552815).length < 2 ^ (prefixWord ++ tailWord_6552815).sum := by decide
  have hdescent : baseEnd_6552815 < baseStart_6552815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552858 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_6552858 : Nat := 118140960795 + 6552858 * 2 ^ 59
def prefixEnd_6552858 : Nat := 4983230072969 + 3 ^ 40 * 6552858 * 2
def baseEnd_6552858 : Nat := 3364765814660028146638961

theorem tailTrace_6552858 : CollatzResearch.WordTrace tailWord_6552858 prefixEnd_6552858 3364765814660028146638961 := by
  unfold tailWord_6552858
  simp only [CollatzResearch.WordTrace]
  refine ⟨59750591523530519973074807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159334910729414719928199485 59750591523530519973074807)
  ·
    refine ⟨89625887285295779959612211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59750591523530519973074807 89625887285295779959612211)
    ·
      refine ⟨134438830927943669939418317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89625887285295779959612211 134438830927943669939418317)
      ·
        refine ⟨50414561597978876227281869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134438830927943669939418317 50414561597978876227281869)
        ·
          refine ⟨18905460599242078585230701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50414561597978876227281869 18905460599242078585230701)
          ·
            refine ⟨7089547724715779469461513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18905460599242078585230701 7089547724715779469461513)
            ·
              refine ⟨5317160793536834602096135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7089547724715779469461513 5317160793536834602096135)
              ·
                refine ⟨7975741190305251903144203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317160793536834602096135 7975741190305251903144203)
                ·
                  refine ⟨11963611785457877854716305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7975741190305251903144203 11963611785457877854716305)
                  ·
                    refine ⟨8972708839093408391037229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11963611785457877854716305 8972708839093408391037229)
                    ·
                      refine ⟨3364765814660028146638961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8972708839093408391037229 3364765814660028146638961)
                      ·
                        rfl

theorem cell23_6552858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_6552858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552858 prefixEnd_6552858 := by exact prefixLift 6552858
  have htrace : WordTrace (prefixWord ++ tailWord_6552858) baseStart_6552858 baseEnd_6552858 := by
    simpa [prefixWord, tailWord_6552858, baseEnd_6552858] using wordTrace_append hprefix tailTrace_6552858
  have hstable : (prefixWord ++ tailWord_6552858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552858).length < 2 ^ (prefixWord ++ tailWord_6552858).sum := by decide
  have hdescent : baseEnd_6552858 < baseStart_6552858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552954 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_6552954 : Nat := 118140960795 + 6552954 * 2 ^ 59
def prefixEnd_6552954 : Nat := 4983230072969 + 3 ^ 40 * 6552954 * 2
def baseEnd_6552954 : Nat := 3364815108802859771038519

theorem tailTrace_6552954 : CollatzResearch.WordTrace tailWord_6552954 prefixEnd_6552954 3364815108802859771038519 := by
  unfold tailWord_6552954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59751466875443572071948479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159337245001182858858529277 59751466875443572071948479)
  ·
    refine ⟨89627200313165358107922719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59751466875443572071948479 89627200313165358107922719)
    ·
      refine ⟨134440800469748037161884079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627200313165358107922719 134440800469748037161884079)
      ·
        refine ⟨201661200704622055742826119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134440800469748037161884079 201661200704622055742826119)
        ·
          refine ⟨302491801056933083614239179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201661200704622055742826119 302491801056933083614239179)
          ·
            refine ⟨453737701585399625421358769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302491801056933083614239179 453737701585399625421358769)
            ·
              refine ⟨340303276189049719066019077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453737701585399625421358769 340303276189049719066019077)
              ·
                refine ⟨63806864285446822324878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340303276189049719066019077 63806864285446822324878577)
                ·
                  refine ⟨47855148214085116743658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63806864285446822324878577 47855148214085116743658933)
                  ·
                    refine ⟨4486420145070479694718025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47855148214085116743658933 4486420145070479694718025)
                    ·
                      refine ⟨3364815108802859771038519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486420145070479694718025 3364815108802859771038519)
                      ·
                        rfl

theorem cell23_6552954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_6552954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552954 prefixEnd_6552954 := by exact prefixLift 6552954
  have htrace : WordTrace (prefixWord ++ tailWord_6552954) baseStart_6552954 baseEnd_6552954 := by
    simpa [prefixWord, tailWord_6552954, baseEnd_6552954] using wordTrace_append hprefix tailTrace_6552954
  have hstable : (prefixWord ++ tailWord_6552954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552954).length < 2 ^ (prefixWord ++ tailWord_6552954).sum := by decide
  have hdescent : baseEnd_6552954 < baseStart_6552954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552957 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_6552957 : Nat := 118140960795 + 6552957 * 2 ^ 59
def prefixEnd_6552957 : Nat := 4983230072969 + 3 ^ 40 * 6552957 * 2
def baseEnd_6552957 : Nat := 3364816649244823259301005

theorem tailTrace_6552957 : CollatzResearch.WordTrace tailWord_6552957 prefixEnd_6552957 3364816649244823259301005 := by
  unfold tailWord_6552957
  simp only [CollatzResearch.WordTrace]
  refine ⟨239005976920763419800153125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159337317947175613200102083 239005976920763419800153125)
  ·
    refine ⟨44813620672643141212528711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239005976920763419800153125 44813620672643141212528711)
    ·
      refine ⟨67220431008964711818793067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44813620672643141212528711 67220431008964711818793067)
      ·
        refine ⟨100830646513447067728189601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67220431008964711818793067 100830646513447067728189601)
        ·
          refine ⟨75622984885085300796142201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100830646513447067728189601 75622984885085300796142201)
          ·
            refine ⟨56717238663813975597106651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75622984885085300796142201 56717238663813975597106651)
            ·
              refine ⟨85075857995720963395659977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56717238663813975597106651 85075857995720963395659977)
              ·
                refine ⟨63806893496790722546744983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85075857995720963395659977 63806893496790722546744983)
                ·
                  refine ⟨95710340245186083820117475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63806893496790722546744983 95710340245186083820117475)
                  ·
                    refine ⟨143565510367779125730176213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95710340245186083820117475 143565510367779125730176213)
                    ·
                      refine ⟨3364816649244823259301005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143565510367779125730176213 3364816649244823259301005)
                      ·
                        rfl

theorem cell23_6552957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_6552957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552957 prefixEnd_6552957 := by exact prefixLift 6552957
  have htrace : WordTrace (prefixWord ++ tailWord_6552957) baseStart_6552957 baseEnd_6552957 := by
    simpa [prefixWord, tailWord_6552957, baseEnd_6552957] using wordTrace_append hprefix tailTrace_6552957
  have hstable : (prefixWord ++ tailWord_6552957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552957).length < 2 ^ (prefixWord ++ tailWord_6552957).sum := by decide
  have hdescent : baseEnd_6552957 < baseStart_6552957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552964 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_6552964 : Nat := 118140960795 + 6552964 * 2 ^ 59
def prefixEnd_6552964 : Nat := 4983230072969 + 3 ^ 40 * 6552964 * 2
def baseEnd_6552964 : Nat := 1121606747869801577304491

theorem tailTrace_6552964 : CollatzResearch.WordTrace tailWord_6552964 prefixEnd_6552964 1121606747869801577304491 := by
  unfold tailWord_6552964
  simp only [CollatzResearch.WordTrace]
  refine ⟨119503116115869029997828973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159337488154492039997105297 119503116115869029997828973)
  ·
    refine ⟨44813668543450886249185865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119503116115869029997828973 44813668543450886249185865)
    ·
      refine ⟨33610251407588164686889399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44813668543450886249185865 33610251407588164686889399)
      ·
        refine ⟨50415377111382247030334099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33610251407588164686889399 50415377111382247030334099)
        ·
          refine ⟨75623065667073370545501149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50415377111382247030334099 75623065667073370545501149)
          ·
            refine ⟨28358649625152513954562931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75623065667073370545501149 28358649625152513954562931)
            ·
              refine ⟨42537974437728770931844397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28358649625152513954562931 42537974437728770931844397)
              ·
                refine ⟨15951740414148289099441649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42537974437728770931844397 15951740414148289099441649)
                ·
                  refine ⟨11963805310611216824581237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15951740414148289099441649 11963805310611216824581237)
                  ·
                    refine ⟨1121606747869801577304491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11963805310611216824581237 1121606747869801577304491)
                    ·
                      rfl

theorem cell23_6552964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_6552964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552964 prefixEnd_6552964 := by exact prefixLift 6552964
  have htrace : WordTrace (prefixWord ++ tailWord_6552964) baseStart_6552964 baseEnd_6552964 := by
    simpa [prefixWord, tailWord_6552964, baseEnd_6552964] using wordTrace_append hprefix tailTrace_6552964
  have hstable : (prefixWord ++ tailWord_6552964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552964).length < 2 ^ (prefixWord ++ tailWord_6552964).sum := by decide
  have hdescent : baseEnd_6552964 < baseStart_6552964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6552997 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6552997 : Nat := 118140960795 + 6552997 * 2 ^ 59
def prefixEnd_6552997 : Nat := 4983230072969 + 3 ^ 40 * 6552997 * 2
def baseEnd_6552997 : Nat := 3364837188471003102800821

theorem tailTrace_6552997 : CollatzResearch.WordTrace tailWord_6552997 prefixEnd_6552997 3364837188471003102800821 := by
  unfold tailWord_6552997
  simp only [CollatzResearch.WordTrace]
  refine ⟨239007435840618506631609245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159338290560412337754406163 239007435840618506631609245)
  ·
    refine ⟨89627788440231939986853467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239007435840618506631609245 89627788440231939986853467)
    ·
      refine ⟨134441682660347909980280201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627788440231939986853467 134441682660347909980280201)
      ·
        refine ⟨100831261995260932485210151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134441682660347909980280201 100831261995260932485210151)
        ·
          refine ⟨151246892992891398727815227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100831261995260932485210151 151246892992891398727815227)
          ·
            refine ⟨226870339489337098091722841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151246892992891398727815227 226870339489337098091722841)
            ·
              refine ⟨170152754617002823568792131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226870339489337098091722841 170152754617002823568792131)
              ·
                refine ⟨255229131925504235353188197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170152754617002823568792131 255229131925504235353188197)
                ·
                  refine ⟨47855462236032044128722787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255229131925504235353188197 47855462236032044128722787)
                  ·
                    refine ⟨71783193354048066193084181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47855462236032044128722787 71783193354048066193084181)
                    ·
                      refine ⟨3364837188471003102800821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71783193354048066193084181 3364837188471003102800821)
                      ·
                        rfl

theorem cell23_6552997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6552997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6552997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6552997 prefixEnd_6552997 := by exact prefixLift 6552997
  have htrace : WordTrace (prefixWord ++ tailWord_6552997) baseStart_6552997 baseEnd_6552997 := by
    simpa [prefixWord, tailWord_6552997, baseEnd_6552997] using wordTrace_append hprefix tailTrace_6552997
  have hstable : (prefixWord ++ tailWord_6552997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6552997).length < 2 ^ (prefixWord ++ tailWord_6552997).sum := by decide
  have hdescent : baseEnd_6552997 < baseStart_6552997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6552997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553004 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_6553004 : Nat := 118140960795 + 6553004 * 2 ^ 59
def prefixEnd_6553004 : Nat := 4983230072969 + 3 ^ 40 * 6553004 * 2
def baseEnd_6553004 : Nat := 3364840782835584575413289

theorem tailTrace_6553004 : CollatzResearch.WordTrace tailWord_6553004 prefixEnd_6553004 3364840782835584575413289 := by
  unfold tailWord_6553004
  simp only [CollatzResearch.WordTrace]
  refine ⟨119503845575796573413557033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159338460767728764551409377 119503845575796573413557033)
  ·
    refine ⟨89627884181847430060167775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119503845575796573413557033 89627884181847430060167775)
    ·
      refine ⟨134441826272771145090251663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627884181847430060167775 134441826272771145090251663)
      ·
        refine ⟨201662739409156717635377495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134441826272771145090251663 201662739409156717635377495)
        ·
          refine ⟨302494109113735076453066243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201662739409156717635377495 302494109113735076453066243)
          ·
            refine ⟨453741163670602614679599365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302494109113735076453066243 453741163670602614679599365)
            ·
              refine ⟨85076468188237990252424881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453741163670602614679599365 85076468188237990252424881)
              ·
                refine ⟨63807351141178492689318661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85076468188237990252424881 63807351141178492689318661)
                ·
                  refine ⟨11963878338970967379247249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63807351141178492689318661 11963878338970967379247249)
                  ·
                    refine ⟨8972908754228225534435437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11963878338970967379247249 8972908754228225534435437)
                    ·
                      refine ⟨3364840782835584575413289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8972908754228225534435437 3364840782835584575413289)
                      ·
                        rfl

theorem cell23_6553004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_6553004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553004 prefixEnd_6553004 := by exact prefixLift 6553004
  have htrace : WordTrace (prefixWord ++ tailWord_6553004) baseStart_6553004 baseEnd_6553004 := by
    simpa [prefixWord, tailWord_6553004, baseEnd_6553004] using wordTrace_append hprefix tailTrace_6553004
  have hstable : (prefixWord ++ tailWord_6553004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553004).length < 2 ^ (prefixWord ++ tailWord_6553004).sum := by decide
  have hdescent : baseEnd_6553004 < baseStart_6553004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553078 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6553078 : Nat := 118140960795 + 6553078 * 2 ^ 59
def prefixEnd_6553078 : Nat := 4983230072969 + 3 ^ 40 * 6553078 * 2
def baseEnd_6553078 : Nat := 3364878780404017285887949

theorem tailTrace_6553078 : CollatzResearch.WordTrace tailWord_6553078 prefixEnd_6553078 3364878780404017285887949 := by
  unfold tailWord_6553078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938149384582816091581743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159340260102216704976871925 14938149384582816091581743)
  ·
    refine ⟨22407224076874224137372615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938149384582816091581743 22407224076874224137372615)
    ·
      refine ⟨33610836115311336206058923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407224076874224137372615 33610836115311336206058923)
      ·
        refine ⟨50416254172967004309088385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33610836115311336206058923 50416254172967004309088385)
        ·
          refine ⟨37812190629725253231816289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50416254172967004309088385 37812190629725253231816289)
          ·
            refine ⟨28359142972293939923862217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37812190629725253231816289 28359142972293939923862217)
            ·
              refine ⟨21269357229220454942896663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28359142972293939923862217 21269357229220454942896663)
              ·
                refine ⟨31904035843830682414344995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21269357229220454942896663 31904035843830682414344995)
                ·
                  refine ⟨47856053765746023621517493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31904035843830682414344995 47856053765746023621517493)
                  ·
                    refine ⟨4486505040538689714517265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47856053765746023621517493 4486505040538689714517265)
                    ·
                      refine ⟨3364878780404017285887949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486505040538689714517265 3364878780404017285887949)
                      ·
                        rfl

theorem cell23_6553078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6553078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553078 prefixEnd_6553078 := by exact prefixLift 6553078
  have htrace : WordTrace (prefixWord ++ tailWord_6553078) baseStart_6553078 baseEnd_6553078 := by
    simpa [prefixWord, tailWord_6553078, baseEnd_6553078] using wordTrace_append hprefix tailTrace_6553078
  have hstable : (prefixWord ++ tailWord_6553078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553078).length < 2 ^ (prefixWord ++ tailWord_6553078).sum := by decide
  have hdescent : baseEnd_6553078 < baseStart_6553078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553084 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6553084 : Nat := 118140960795 + 6553084 * 2 ^ 59
def prefixEnd_6553084 : Nat := 4983230072969 + 3 ^ 40 * 6553084 * 2
def baseEnd_6553084 : Nat := 1121627287095981420804307

theorem tailTrace_6553084 : CollatzResearch.WordTrace tailWord_6553084 prefixEnd_6553084 1121627287095981420804307 := by
  unfold tailWord_6553084
  simp only [CollatzResearch.WordTrace]
  refine ⟨119505304495651660245013153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159340405994202213660017537 119505304495651660245013153)
  ·
    refine ⟨89628978371738745183759865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119505304495651660245013153 89628978371738745183759865)
    ·
      refine ⟨67221733778804058887819899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89628978371738745183759865 67221733778804058887819899)
      ·
        refine ⟨100832600668206088331729849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67221733778804058887819899 100832600668206088331729849)
        ·
          refine ⟨75624450501154566248797387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100832600668206088331729849 75624450501154566248797387)
          ·
            refine ⟨113436675751731849373196081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75624450501154566248797387 113436675751731849373196081)
            ·
              refine ⟨85077506813798887029897061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113436675751731849373196081 85077506813798887029897061)
              ·
                refine ⟨15952032527587291318105699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85077506813798887029897061 15952032527587291318105699)
                ·
                  refine ⟨23928048791380936977158549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15952032527587291318105699 23928048791380936977158549)
                  ·
                    refine ⟨1121627287095981420804307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23928048791380936977158549 1121627287095981420804307)
                    ·
                      rfl

theorem cell23_6553084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6553084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553084 prefixEnd_6553084 := by exact prefixLift 6553084
  have htrace : WordTrace (prefixWord ++ tailWord_6553084) baseStart_6553084 baseEnd_6553084 := by
    simpa [prefixWord, tailWord_6553084, baseEnd_6553084] using wordTrace_append hprefix tailTrace_6553084
  have hstable : (prefixWord ++ tailWord_6553084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553084).length < 2 ^ (prefixWord ++ tailWord_6553084).sum := by decide
  have hdescent : baseEnd_6553084 < baseStart_6553084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553085 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_6553085 : Nat := 118140960795 + 6553085 * 2 ^ 59
def prefixEnd_6553085 : Nat := 4983230072969 + 3 ^ 40 * 6553085 * 2
def baseEnd_6553085 : Nat := 3364882374768598758500417

theorem tailTrace_6553085 : CollatzResearch.WordTrace tailWord_6553085 prefixEnd_6553085 3364882374768598758500417 := by
  unfold tailWord_6553085
  simp only [CollatzResearch.WordTrace]
  refine ⟨239010645464299697660812709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159340430309533131773875139 239010645464299697660812709)
  ·
    refine ⟨44814496024556193311402383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239010645464299697660812709 44814496024556193311402383)
    ·
      refine ⟨67221744036834289967103575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44814496024556193311402383 67221744036834289967103575)
      ·
        refine ⟨100832616055251434950655363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67221744036834289967103575 100832616055251434950655363)
        ·
          refine ⟨151248924082877152425983045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100832616055251434950655363 151248924082877152425983045)
          ·
            refine ⟨28359173265539466079871821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151248924082877152425983045 28359173265539466079871821)
            ·
              refine ⟨10634689974577299779951933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28359173265539466079871821 10634689974577299779951933)
              ·
                refine ⟨3988008740466487417481975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10634689974577299779951933 3988008740466487417481975)
                ·
                  refine ⟨5982013110699731126222963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988008740466487417481975 5982013110699731126222963)
                  ·
                    refine ⟨8973019666049596689334445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982013110699731126222963 8973019666049596689334445)
                    ·
                      refine ⟨3364882374768598758500417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973019666049596689334445 3364882374768598758500417)
                      ·
                        rfl

theorem cell23_6553085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_6553085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553085 prefixEnd_6553085 := by exact prefixLift 6553085
  have htrace : WordTrace (prefixWord ++ tailWord_6553085) baseStart_6553085 baseEnd_6553085 := by
    simpa [prefixWord, tailWord_6553085, baseEnd_6553085] using wordTrace_append hprefix tailTrace_6553085
  have hstable : (prefixWord ++ tailWord_6553085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553085).length < 2 ^ (prefixWord ++ tailWord_6553085).sum := by decide
  have hdescent : baseEnd_6553085 < baseStart_6553085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553102 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6553102 : Nat := 118140960795 + 6553102 * 2 ^ 59
def prefixEnd_6553102 : Nat := 4983230072969 + 3 ^ 40 * 6553102 * 2
def baseEnd_6553102 : Nat := 3364891103939725191987839

theorem tailTrace_6553102 : CollatzResearch.WordTrace tailWord_6553102 prefixEnd_6553102 3364891103939725191987839 := by
  unfold tailWord_6553102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29876408188154763695522695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159340843670158739709454373 29876408188154763695522695)
  ·
    refine ⟨44814612282232145543284043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29876408188154763695522695 44814612282232145543284043)
    ·
      refine ⟨67221918423348218314926065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44814612282232145543284043 67221918423348218314926065)
      ·
        refine ⟨50416438817511163736194549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67221918423348218314926065 50416438817511163736194549)
        ·
          refine ⟨4726541139141671600268239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50416438817511163736194549 4726541139141671600268239)
          ·
            refine ⟨7089811708712507400402359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726541139141671600268239 7089811708712507400402359)
            ·
              refine ⟨10634717563068761100603539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089811708712507400402359 10634717563068761100603539)
              ·
                refine ⟨15952076344603141650905309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634717563068761100603539 15952076344603141650905309)
                ·
                  refine ⟨5982028629226178119089491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15952076344603141650905309 5982028629226178119089491)
                  ·
                    refine ⟨8973042943839267178634237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982028629226178119089491 8973042943839267178634237)
                    ·
                      refine ⟨3364891103939725191987839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973042943839267178634237 3364891103939725191987839)
                      ·
                        rfl

theorem cell23_6553102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6553102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553102 prefixEnd_6553102 := by exact prefixLift 6553102
  have htrace : WordTrace (prefixWord ++ tailWord_6553102) baseStart_6553102 baseEnd_6553102 := by
    simpa [prefixWord, tailWord_6553102, baseEnd_6553102] using wordTrace_append hprefix tailTrace_6553102
  have hstable : (prefixWord ++ tailWord_6553102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553102).length < 2 ^ (prefixWord ++ tailWord_6553102).sum := by decide
  have hdescent : baseEnd_6553102 < baseStart_6553102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553141 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6553141 : Nat := 118140960795 + 6553141 * 2 ^ 59
def prefixEnd_6553141 : Nat := 4983230072969 + 3 ^ 40 * 6553141 * 2
def baseEnd_6553141 : Nat := 3364911129685250539400159

theorem tailTrace_6553141 : CollatzResearch.WordTrace tailWord_6553141 prefixEnd_6553141 3364911129685250539400159 := by
  unfold tailWord_6553141
  simp only [CollatzResearch.WordTrace]
  refine ⟨239012687952096819224851277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159341791968064546149900851 239012687952096819224851277)
  ·
    refine ⟨89629757982036307209319229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239012687952096819224851277 89629757982036307209319229)
    ·
      refine ⟨33611159243263615203494711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89629757982036307209319229 33611159243263615203494711)
      ·
        refine ⟨50416738864895422805242067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33611159243263615203494711 50416738864895422805242067)
        ·
          refine ⟨75625108297343134207863101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50416738864895422805242067 75625108297343134207863101)
          ·
            refine ⟨28359415611503675327948663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75625108297343134207863101 28359415611503675327948663)
            ·
              refine ⟨42539123417255512991922995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359415611503675327948663 42539123417255512991922995)
              ·
                refine ⟨63808685125883269487884493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42539123417255512991922995 63808685125883269487884493)
                ·
                  refine ⟨23928256922206226057956685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63808685125883269487884493 23928256922206226057956685)
                  ·
                    refine ⟨8973096345827334771733757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23928256922206226057956685 8973096345827334771733757)
                    ·
                      refine ⟨3364911129685250539400159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973096345827334771733757 3364911129685250539400159)
                      ·
                        rfl

theorem cell23_6553141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6553141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553141 prefixEnd_6553141 := by exact prefixLift 6553141
  have htrace : WordTrace (prefixWord ++ tailWord_6553141) baseStart_6553141 baseEnd_6553141 := by
    simpa [prefixWord, tailWord_6553141, baseEnd_6553141] using wordTrace_append hprefix tailTrace_6553141
  have hstable : (prefixWord ++ tailWord_6553141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553141).length < 2 ^ (prefixWord ++ tailWord_6553141).sum := by decide
  have hdescent : baseEnd_6553141 < baseStart_6553141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553142 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6553142 : Nat := 118140960795 + 6553142 * 2 ^ 59
def prefixEnd_6553142 : Nat := 4983230072969 + 3 ^ 40 * 6553142 * 2
def baseEnd_6553142 : Nat := 3364911643165905035487655

theorem tailTrace_6553142 : CollatzResearch.WordTrace tailWord_6553142 prefixEnd_6553142 3364911643165905035487655 := by
  unfold tailWord_6553142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938295276568324774727355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159341816283395464263758453 14938295276568324774727355)
  ·
    refine ⟨22407442914852487162091033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938295276568324774727355 22407442914852487162091033)
    ·
      refine ⟨16805582186139365371568275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22407442914852487162091033 16805582186139365371568275)
      ·
        refine ⟨25208373279209048057352413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16805582186139365371568275 25208373279209048057352413)
        ·
          refine ⟨9453139979703393021507155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25208373279209048057352413 9453139979703393021507155)
          ·
            refine ⟨14179709969555089532260733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9453139979703393021507155 14179709969555089532260733)
            ·
              refine ⟨5317391238583158574597775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14179709969555089532260733 5317391238583158574597775)
              ·
                refine ⟨7976086857874737861896663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317391238583158574597775 7976086857874737861896663)
                ·
                  refine ⟨11964130286812106792844995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976086857874737861896663 11964130286812106792844995)
                  ·
                    refine ⟨17946195430218160189267493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11964130286812106792844995 17946195430218160189267493)
                    ·
                      refine ⟨3364911643165905035487655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17946195430218160189267493 3364911643165905035487655)
                      ·
                        rfl

theorem cell23_6553142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6553142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553142 prefixEnd_6553142 := by exact prefixLift 6553142
  have htrace : WordTrace (prefixWord ++ tailWord_6553142) baseStart_6553142 baseEnd_6553142 := by
    simpa [prefixWord, tailWord_6553142, baseEnd_6553142] using wordTrace_append hprefix tailTrace_6553142
  have hstable : (prefixWord ++ tailWord_6553142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553142).length < 2 ^ (prefixWord ++ tailWord_6553142).sum := by decide
  have hdescent : baseEnd_6553142 < baseStart_6553142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553145 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6553145 : Nat := 118140960795 + 6553145 * 2 ^ 59
def prefixEnd_6553145 : Nat := 4983230072969 + 3 ^ 40 * 6553145 * 2
def baseEnd_6553145 : Nat := 3364913183607868523750141

theorem tailTrace_6553145 : CollatzResearch.WordTrace tailWord_6553145 prefixEnd_6553145 3364913183607868523750141 := by
  unfold tailWord_6553145
  simp only [CollatzResearch.WordTrace]
  refine ⟨239012833844082327907996889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159341889229388218605331259 239012833844082327907996889)
  ·
    refine ⟨179259625383061745930997667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239012833844082327907996889 179259625383061745930997667)
    ·
      refine ⟨268889438074592618896496501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179259625383061745930997667 268889438074592618896496501)
      ·
        refine ⟨25208384819493058021546547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268889438074592618896496501 25208384819493058021546547)
        ·
          refine ⟨37812577229239587032319821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25208384819493058021546547 37812577229239587032319821)
          ·
            refine ⟨14179716460964845137119933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37812577229239587032319821 14179716460964845137119933)
            ·
              refine ⟨5317393672861816926419975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14179716460964845137119933 5317393672861816926419975)
              ·
                refine ⟨7976090509292725389629963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317393672861816926419975 7976090509292725389629963)
                ·
                  refine ⟨11964135763939088084444945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976090509292725389629963 11964135763939088084444945)
                  ·
                    refine ⟨8973101822954316063333709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11964135763939088084444945 8973101822954316063333709)
                    ·
                      refine ⟨3364913183607868523750141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973101822954316063333709 3364913183607868523750141)
                      ·
                        rfl

theorem cell23_6553145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6553145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553145 prefixEnd_6553145 := by exact prefixLift 6553145
  have htrace : WordTrace (prefixWord ++ tailWord_6553145) baseStart_6553145 baseEnd_6553145 := by
    simpa [prefixWord, tailWord_6553145, baseEnd_6553145] using wordTrace_append hprefix tailTrace_6553145
  have hstable : (prefixWord ++ tailWord_6553145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553145).length < 2 ^ (prefixWord ++ tailWord_6553145).sum := by decide
  have hdescent : baseEnd_6553145 < baseStart_6553145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553165 : List Nat := [1, 6, 1, 1, 4, 1, 1, 8]
def baseStart_6553165 : Nat := 118140960795 + 6553165 * 2 ^ 59
def prefixEnd_6553165 : Nat := 4983230072969 + 3 ^ 40 * 6553165 * 2
def baseEnd_6553165 : Nat := 124626794563739201685187

theorem tailTrace_6553165 : CollatzResearch.WordTrace tailWord_6553165 prefixEnd_6553165 124626794563739201685187 := by
  unfold tailWord_6553165
  simp only [CollatzResearch.WordTrace]
  refine ⟨239013563304009871323724949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159342375536006580882483299 239013563304009871323724949)
  ·
    refine ⟨11203760779875462718299607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239013563304009871323724949 11203760779875462718299607)
    ·
      refine ⟨16805641169813194077449411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203760779875462718299607 16805641169813194077449411)
      ·
        refine ⟨25208461754719791116174117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16805641169813194077449411 25208461754719791116174117)
        ·
          refine ⟨4726586579009960834282647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25208461754719791116174117 4726586579009960834282647)
          ·
            refine ⟨7089879868514941251423971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726586579009960834282647 7089879868514941251423971)
            ·
              refine ⟨10634819802772411877135957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7089879868514941251423971 10634819802772411877135957)
              ·
                refine ⟨124626794563739201685187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10634819802772411877135957 124626794563739201685187)
                ·
                  rfl

theorem cell23_6553165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 8].length) (baseStart_6553165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553165 prefixEnd_6553165 := by exact prefixLift 6553165
  have htrace : WordTrace (prefixWord ++ tailWord_6553165) baseStart_6553165 baseEnd_6553165 := by
    simpa [prefixWord, tailWord_6553165, baseEnd_6553165] using wordTrace_append hprefix tailTrace_6553165
  have hstable : (prefixWord ++ tailWord_6553165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553165).length < 2 ^ (prefixWord ++ tailWord_6553165).sum := by decide
  have hdescent : baseEnd_6553165 < baseStart_6553165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553202 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_6553202 : Nat := 118140960795 + 6553202 * 2 ^ 59
def prefixEnd_6553202 : Nat := 4983230072969 + 3 ^ 40 * 6553202 * 2
def baseEnd_6553202 : Nat := 3364942452005174800737379

theorem tailTrace_6553202 : CollatzResearch.WordTrace tailWord_6553202 prefixEnd_6553202 3364942452005174800737379 := by
  unfold tailWord_6553202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59753728201218956660705465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159343275203250551095214573 59753728201218956660705465)
  ·
    refine ⟨44815296150914217495529099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59753728201218956660705465 44815296150914217495529099)
    ·
      refine ⟨67222944226371326243293649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44815296150914217495529099 67222944226371326243293649)
      ·
        refine ⟨50417208169778494682470237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67222944226371326243293649 50417208169778494682470237)
        ·
          refine ⟨18906453063666935505926339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50417208169778494682470237 18906453063666935505926339)
          ·
            refine ⟨28359679595500403258889509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18906453063666935505926339 28359679595500403258889509)
            ·
              refine ⟨5317439924156325611041783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28359679595500403258889509 5317439924156325611041783)
              ·
                refine ⟨7976159886234488416562675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317439924156325611041783 7976159886234488416562675)
                ·
                  refine ⟨11964239829351732624844013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976159886234488416562675 11964239829351732624844013)
                  ·
                    refine ⟨4486589936006899734316505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11964239829351732624844013 4486589936006899734316505)
                    ·
                      refine ⟨3364942452005174800737379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486589936006899734316505 3364942452005174800737379)
                      ·
                        rfl

theorem cell23_6553202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_6553202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553202 prefixEnd_6553202 := by exact prefixLift 6553202
  have htrace : WordTrace (prefixWord ++ tailWord_6553202) baseStart_6553202 baseEnd_6553202 := by
    simpa [prefixWord, tailWord_6553202, baseEnd_6553202] using wordTrace_append hprefix tailTrace_6553202
  have hstable : (prefixWord ++ tailWord_6553202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553202).length < 2 ^ (prefixWord ++ tailWord_6553202).sum := by decide
  have hdescent : baseEnd_6553202 < baseStart_6553202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553221 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 7]
def baseStart_6553221 : Nat := 118140960795 + 6553221 * 2 ^ 59
def prefixEnd_6553221 : Nat := 4983230072969 + 3 ^ 40 * 6553221 * 2
def baseEnd_6553221 : Nat := 373883578681956691822199

theorem tailTrace_6553221 : CollatzResearch.WordTrace tailWord_6553221 prefixEnd_6553221 373883578681956691822199 := by
  unfold tailWord_6553221
  simp only [CollatzResearch.WordTrace]
  refine ⟨239015605791806992887763517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159343737194537995258509011 239015605791806992887763517)
  ·
    refine ⟨89630852171927622332911319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239015605791806992887763517 89630852171927622332911319)
    ·
      refine ⟨134446278257891433499366979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89630852171927622332911319 134446278257891433499366979)
      ·
        refine ⟨201669417386837150249050469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134446278257891433499366979 201669417386837150249050469)
        ·
          refine ⟨37813015760031965671696963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201669417386837150249050469 37813015760031965671696963)
          ·
            refine ⟨56719523640047948507545445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37813015760031965671696963 56719523640047948507545445)
            ·
              refine ⟨10634910682508990345164771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56719523640047948507545445 10634910682508990345164771)
              ·
                refine ⟨15952366023763485517747157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634910682508990345164771 15952366023763485517747157)
                ·
                  refine ⟨373883578681956691822199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15952366023763485517747157 373883578681956691822199)
                  ·
                    rfl

theorem cell23_6553221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_6553221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553221 prefixEnd_6553221 := by exact prefixLift 6553221
  have htrace : WordTrace (prefixWord ++ tailWord_6553221) baseStart_6553221 baseEnd_6553221 := by
    simpa [prefixWord, tailWord_6553221, baseEnd_6553221] using wordTrace_append hprefix tailTrace_6553221
  have hstable : (prefixWord ++ tailWord_6553221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553221).length < 2 ^ (prefixWord ++ tailWord_6553221).sum := by decide
  have hdescent : baseEnd_6553221 < baseStart_6553221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553251 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 2, 5]
def baseStart_6553251 : Nat := 118140960795 + 6553251 * 2 ^ 59
def prefixEnd_6553251 : Nat := 4983230072969 + 3 ^ 40 * 6553251 * 2
def baseEnd_6553251 : Nat := 1121655870852415036341551

theorem tailTrace_6553251 : CollatzResearch.WordTrace tailWord_6553251 prefixEnd_6553251 1121655870852415036341551 := by
  unfold tailWord_6553251
  simp only [CollatzResearch.WordTrace]
  refine ⟨239016699981698308011355607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159344466654465538674237071 239016699981698308011355607)
  ·
    refine ⟨358525049972547462017033411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239016699981698308011355607 358525049972547462017033411)
    ·
      refine ⟨537787574958821193025550117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358525049972547462017033411 537787574958821193025550117)
      ·
        refine ⟨100835170304778973692290647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537787574958821193025550117 100835170304778973692290647)
        ·
          refine ⟨151252755457168460538435971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100835170304778973692290647 151252755457168460538435971)
          ·
            refine ⟨226879133185752690807653957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151252755457168460538435971 226879133185752690807653957)
            ·
              refine ⟨42539837472328629526435117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226879133185752690807653957 42539837472328629526435117)
              ·
                refine ⟨15952439052123236072413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42539837472328629526435117 15952439052123236072413169)
                ·
                  refine ⟨11964329289092427054309877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15952439052123236072413169 11964329289092427054309877)
                  ·
                    refine ⟨1121655870852415036341551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11964329289092427054309877 1121655870852415036341551)
                    ·
                      rfl

theorem cell23_6553251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 5].length) (baseStart_6553251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553251 prefixEnd_6553251 := by exact prefixLift 6553251
  have htrace : WordTrace (prefixWord ++ tailWord_6553251) baseStart_6553251 baseEnd_6553251 := by
    simpa [prefixWord, tailWord_6553251, baseEnd_6553251] using wordTrace_append hprefix tailTrace_6553251
  have hstable : (prefixWord ++ tailWord_6553251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553251).length < 2 ^ (prefixWord ++ tailWord_6553251).sum := by decide
  have hdescent : baseEnd_6553251 < baseStart_6553251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553278 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_6553278 : Nat := 118140960795 + 6553278 * 2 ^ 59
def prefixEnd_6553278 : Nat := 4983230072969 + 3 ^ 40 * 6553278 * 2
def baseEnd_6553278 : Nat := 3364981476534916503387029

theorem tailTrace_6553278 : CollatzResearch.WordTrace tailWord_6553278 prefixEnd_6553278 3364981476534916503387029 := by
  unfold tailWord_6553278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29877210594075061452823561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159345123168400327748392325 29877210594075061452823561)
  ·
    refine ⟨22407907945556296089617671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29877210594075061452823561 22407907945556296089617671)
    ·
      refine ⟨33611861918334444134426507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407907945556296089617671 33611861918334444134426507)
      ·
        refine ⟨50417792877501666201639761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33611861918334444134426507 50417792877501666201639761)
        ·
          refine ⟨37813344658126249651229821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50417792877501666201639761 37813344658126249651229821)
          ·
            refine ⟨14180004246797343619211183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37813344658126249651229821 14180004246797343619211183)
            ·
              refine ⟨21270006370196015428816775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180004246797343619211183 21270006370196015428816775)
              ·
                refine ⟨31905009555294023143225163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21270006370196015428816775 31905009555294023143225163)
                ·
                  refine ⟨47857514332941034714837745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31905009555294023143225163 47857514332941034714837745)
                  ·
                    refine ⟨35893135749705776036128309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47857514332941034714837745 35893135749705776036128309)
                    ·
                      refine ⟨3364981476534916503387029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35893135749705776036128309 3364981476534916503387029)
                      ·
                        rfl

theorem cell23_6553278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_6553278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553278 prefixEnd_6553278 := by exact prefixLift 6553278
  have htrace : WordTrace (prefixWord ++ tailWord_6553278) baseStart_6553278 baseEnd_6553278 := by
    simpa [prefixWord, tailWord_6553278, baseEnd_6553278] using wordTrace_append hprefix tailTrace_6553278
  have hstable : (prefixWord ++ tailWord_6553278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553278).length < 2 ^ (prefixWord ++ tailWord_6553278).sum := by decide
  have hdescent : baseEnd_6553278 < baseStart_6553278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553288 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_6553288 : Nat := 118140960795 + 6553288 * 2 ^ 59
def prefixEnd_6553288 : Nat := 4983230072969 + 3 ^ 40 * 6553288 * 2
def baseEnd_6553288 : Nat := 3364986611341461464261983

theorem tailTrace_6553288 : CollatzResearch.WordTrace tailWord_6553288 prefixEnd_6553288 3364986611341461464261983 := by
  unfold tailWord_6553288
  simp only [CollatzResearch.WordTrace]
  refine ⟨119509024741282131665226259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159345366321709508886968345 119509024741282131665226259)
  ·
    refine ⟨179263537111923197497839389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119509024741282131665226259 179263537111923197497839389)
    ·
      refine ⟨67223826416971199061689771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179263537111923197497839389 67223826416971199061689771)
      ·
        refine ⟨100835739625456798592534657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67223826416971199061689771 100835739625456798592534657)
        ·
          refine ⟨75626804719092598944400993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100835739625456798592534657 75626804719092598944400993)
          ·
            refine ⟨56720103539319449208300745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75626804719092598944400993 56720103539319449208300745)
            ·
              refine ⟨42540077654489586906225559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56720103539319449208300745 42540077654489586906225559)
              ·
                refine ⟨63810116481734380359338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42540077654489586906225559 63810116481734380359338339)
                ·
                  refine ⟨95715174722601570539007509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63810116481734380359338339 95715174722601570539007509)
                  ·
                    refine ⟨4486648815121948619015977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95715174722601570539007509 4486648815121948619015977)
                    ·
                      refine ⟨3364986611341461464261983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486648815121948619015977 3364986611341461464261983)
                      ·
                        rfl

theorem cell23_6553288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_6553288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553288 prefixEnd_6553288 := by exact prefixLift 6553288
  have htrace : WordTrace (prefixWord ++ tailWord_6553288) baseStart_6553288 baseEnd_6553288 := by
    simpa [prefixWord, tailWord_6553288, baseEnd_6553288] using wordTrace_append hprefix tailTrace_6553288
  have hstable : (prefixWord ++ tailWord_6553288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553288).length < 2 ^ (prefixWord ++ tailWord_6553288).sum := by decide
  have hdescent : baseEnd_6553288 < baseStart_6553288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553291 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3]
def baseStart_6553291 : Nat := 118140960795 + 6553291 * 2 ^ 59
def prefixEnd_6553291 : Nat := 4983230072969 + 3 ^ 40 * 6553291 * 2
def baseEnd_6553291 : Nat := 3364988151783424952524469

theorem tailTrace_6553291 : CollatzResearch.WordTrace tailWord_6553291 prefixEnd_6553291 3364988151783424952524469 := by
  unfold tailWord_6553291
  simp only [CollatzResearch.WordTrace]
  refine ⟨239018158901553394842811727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159345439267702263228541151 239018158901553394842811727)
  ·
    refine ⟨358527238352330092264217591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239018158901553394842811727 358527238352330092264217591)
    ·
      refine ⟨537790857528495138396326387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358527238352330092264217591 537790857528495138396326387)
      ·
        refine ⟨806686286292742707594489581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537790857528495138396326387 806686286292742707594489581)
        ·
          refine ⟨302507357359778515347933593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806686286292742707594489581 302507357359778515347933593)
          ·
            refine ⟨226880518019833886510950195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302507357359778515347933593 226880518019833886510950195)
            ·
              refine ⟨340320777029750829766425293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226880518019833886510950195 340320777029750829766425293)
              ·
                refine ⟨127620291386156561162409485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340320777029750829766425293 127620291386156561162409485)
                ·
                  refine ⟨47857609269808710435903557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127620291386156561162409485 47857609269808710435903557)
                  ·
                    refine ⟨8973301738089133206731917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47857609269808710435903557 8973301738089133206731917)
                    ·
                      refine ⟨3364988151783424952524469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973301738089133206731917 3364988151783424952524469)
                      ·
                        rfl

theorem cell23_6553291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 3].length) (baseStart_6553291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553291 prefixEnd_6553291 := by exact prefixLift 6553291
  have htrace : WordTrace (prefixWord ++ tailWord_6553291) baseStart_6553291 baseEnd_6553291 := by
    simpa [prefixWord, tailWord_6553291, baseEnd_6553291] using wordTrace_append hprefix tailTrace_6553291
  have hstable : (prefixWord ++ tailWord_6553291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553291).length < 2 ^ (prefixWord ++ tailWord_6553291).sum := by decide
  have hdescent : baseEnd_6553291 < baseStart_6553291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553325 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6553325 : Nat := 118140960795 + 6553325 * 2 ^ 59
def prefixEnd_6553325 : Nat := 4983230072969 + 3 ^ 40 * 6553325 * 2
def baseEnd_6553325 : Nat := 3365005610125677819499313

theorem tailTrace_6553325 : CollatzResearch.WordTrace tailWord_6553325 prefixEnd_6553325 3365005610125677819499313 := by
  unfold tailWord_6553325
  simp only [CollatzResearch.WordTrace]
  refine ⟨239019398983430218649549429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159346265988953479099699619 239019398983430218649549429)
  ·
    refine ⟨22408068654696582998395259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239019398983430218649549429 22408068654696582998395259)
    ·
      refine ⟨33612102982044874497592889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22408068654696582998395259 33612102982044874497592889)
      ·
        refine ⟨25209077236533655873194667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33612102982044874497592889 25209077236533655873194667)
        ·
          refine ⟨37813615854800483809792001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209077236533655873194667 37813615854800483809792001)
          ·
            refine ⟨28360211891100362857344001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37813615854800483809792001 28360211891100362857344001)
            ·
              refine ⟨21270158918325272143008001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28360211891100362857344001 21270158918325272143008001)
              ·
                refine ⟨15952619188743954107256001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21270158918325272143008001 15952619188743954107256001)
                ·
                  refine ⟨11964464391557965580442001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15952619188743954107256001 11964464391557965580442001)
                  ·
                    refine ⟨8973348293668474185331501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11964464391557965580442001 8973348293668474185331501)
                    ·
                      refine ⟨3365005610125677819499313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973348293668474185331501 3365005610125677819499313)
                      ·
                        rfl

theorem cell23_6553325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6553325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553325 prefixEnd_6553325 := by exact prefixLift 6553325
  have htrace : WordTrace (prefixWord ++ tailWord_6553325) baseStart_6553325 baseEnd_6553325 := by
    simpa [prefixWord, tailWord_6553325, baseEnd_6553325] using wordTrace_append hprefix tailTrace_6553325
  have hstable : (prefixWord ++ tailWord_6553325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553325).length < 2 ^ (prefixWord ++ tailWord_6553325).sum := by decide
  have hdescent : baseEnd_6553325 < baseStart_6553325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553358 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_6553358 : Nat := 118140960795 + 6553358 * 2 ^ 59
def prefixEnd_6553358 : Nat := 4983230072969 + 3 ^ 40 * 6553358 * 2
def baseEnd_6553358 : Nat := 1121674184995758730128887

theorem tailTrace_6553358 : CollatzResearch.WordTrace tailWord_6553358 prefixEnd_6553358 1121674184995758730128887 := by
  unfold tailWord_6553358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29877575324038833160687591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159347068394873776857000485 29877575324038833160687591)
  ·
    refine ⟨44816362986058249741031387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29877575324038833160687591 44816362986058249741031387)
    ·
      refine ⟨67224544479087374611547081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44816362986058249741031387 67224544479087374611547081)
      ·
        refine ⟨50418408359315530958660311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67224544479087374611547081 50418408359315530958660311)
        ·
          refine ⟨75627612538973296437990467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50418408359315530958660311 75627612538973296437990467)
          ·
            refine ⟨113441418808459944656985701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75627612538973296437990467 113441418808459944656985701)
            ·
              refine ⟨21270266026586239623184819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113441418808459944656985701 21270266026586239623184819)
              ·
                refine ⟨31905399039879359434777229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21270266026586239623184819 31905399039879359434777229)
                ·
                  refine ⟨11964524639954759788041461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31905399039879359434777229 11964524639954759788041461)
                  ·
                    refine ⟨1121674184995758730128887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11964524639954759788041461 1121674184995758730128887)
                    ·
                      rfl

theorem cell23_6553358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_6553358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553358 prefixEnd_6553358 := by exact prefixLift 6553358
  have htrace : WordTrace (prefixWord ++ tailWord_6553358) baseStart_6553358 baseEnd_6553358 := by
    simpa [prefixWord, tailWord_6553358, baseEnd_6553358] using wordTrace_append hprefix tailTrace_6553358
  have hstable : (prefixWord ++ tailWord_6553358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553358).length < 2 ^ (prefixWord ++ tailWord_6553358).sum := by decide
  have hdescent : baseEnd_6553358 < baseStart_6553358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553365 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_6553365 : Nat := 118140960795 + 6553365 * 2 ^ 59
def prefixEnd_6553365 : Nat := 4983230072969 + 3 ^ 40 * 6553365 * 2
def baseEnd_6553365 : Nat := 3365026149351857662999129

theorem tailTrace_6553365 : CollatzResearch.WordTrace tailWord_6553365 prefixEnd_6553365 3365026149351857662999129 := by
  unfold tailWord_6553365
  simp only [CollatzResearch.WordTrace]
  refine ⟨239020857903285305481005549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159347238602190203654003699 239020857903285305481005549)
  ·
    refine ⟨89632821713731989555377081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239020857903285305481005549 89632821713731989555377081)
    ·
      refine ⟨67224616285298992166532811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89632821713731989555377081 67224616285298992166532811)
      ·
        refine ⟨100836924427948488249799217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67224616285298992166532811 100836924427948488249799217)
        ·
          refine ⟨75627693320961366187349413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100836924427948488249799217 75627693320961366187349413)
          ·
            refine ⟨14180192497680256160128015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75627693320961366187349413 14180192497680256160128015)
            ·
              refine ⟨21270288746520384240192023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180192497680256160128015 21270288746520384240192023)
              ·
                refine ⟨31905433119780576360288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21270288746520384240192023 31905433119780576360288035)
                ·
                  refine ⟨47858149679670864540432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31905433119780576360288035 47858149679670864540432053)
                  ·
                    refine ⟨4486701532469143550665505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47858149679670864540432053 4486701532469143550665505)
                    ·
                      refine ⟨3365026149351857662999129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486701532469143550665505 3365026149351857662999129)
                      ·
                        rfl

theorem cell23_6553365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_6553365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553365 prefixEnd_6553365 := by exact prefixLift 6553365
  have htrace : WordTrace (prefixWord ++ tailWord_6553365) baseStart_6553365 baseEnd_6553365 := by
    simpa [prefixWord, tailWord_6553365, baseEnd_6553365] using wordTrace_append hprefix tailTrace_6553365
  have hstable : (prefixWord ++ tailWord_6553365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553365).length < 2 ^ (prefixWord ++ tailWord_6553365).sum := by decide
  have hdescent : baseEnd_6553365 < baseStart_6553365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553391 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_6553391 : Nat := 118140960795 + 6553391 * 2 ^ 59
def prefixEnd_6553391 : Nat := 4983230072969 + 3 ^ 40 * 6553391 * 2
def baseEnd_6553391 : Nat := 3365039499848874561274009

theorem tailTrace_6553391 : CollatzResearch.WordTrace tailWord_6553391 prefixEnd_6553391 3365039499848874561274009 := by
  unfold tailWord_6553391
  simp only [CollatzResearch.WordTrace]
  refine ⟨239021806201191111921452027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159347870800794074614301351 239021806201191111921452027)
  ·
    refine ⟨358532709301786667882178041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239021806201191111921452027 358532709301786667882178041)
    ·
      refine ⟨268899531976340000911633531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358532709301786667882178041 268899531976340000911633531)
      ·
        refine ⟨403349297964510001367450297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268899531976340000911633531 403349297964510001367450297)
        ·
          refine ⟨302511973473382501025587723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403349297964510001367450297 302511973473382501025587723)
          ·
            refine ⟨453767960210073751538381585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302511973473382501025587723 453767960210073751538381585)
            ·
              refine ⟨340325970157555313653786189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453767960210073751538381585 340325970157555313653786189)
              ·
                refine ⟨127622238809083242620169821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340325970157555313653786189 127622238809083242620169821)
                ·
                  refine ⟨47858339553406215982563683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127622238809083242620169821 47858339553406215982563683)
                  ·
                    refine ⟨71787509330109323973845525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47858339553406215982563683 71787509330109323973845525)
                    ·
                      refine ⟨3365039499848874561274009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71787509330109323973845525 3365039499848874561274009)
                      ·
                        rfl

theorem cell23_6553391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_6553391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553391 prefixEnd_6553391 := by exact prefixLift 6553391
  have htrace : WordTrace (prefixWord ++ tailWord_6553391) baseStart_6553391 baseEnd_6553391 := by
    simpa [prefixWord, tailWord_6553391, baseEnd_6553391] using wordTrace_append hprefix tailTrace_6553391
  have hstable : (prefixWord ++ tailWord_6553391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553391).length < 2 ^ (prefixWord ++ tailWord_6553391).sum := by decide
  have hdescent : baseEnd_6553391 < baseStart_6553391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553405 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_6553405 : Nat := 118140960795 + 6553405 * 2 ^ 59
def prefixEnd_6553405 : Nat := 4983230072969 + 3 ^ 40 * 6553405 * 2
def baseEnd_6553405 : Nat := 1121682229526012502166315

theorem tailTrace_6553405 : CollatzResearch.WordTrace tailWord_6553405 prefixEnd_6553405 1121682229526012502166315 := by
  unfold tailWord_6553405
  simp only [CollatzResearch.WordTrace]
  refine ⟨239022316823140392312461669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159348211215426928208307779 239022316823140392312461669)
  ·
    refine ⟨44816684404338823558586563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239022316823140392312461669 44816684404338823558586563)
    ·
      refine ⟨67225026606508235337879845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44816684404338823558586563 67225026606508235337879845)
      ·
        refine ⟨12604692488720294125852471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67225026606508235337879845 12604692488720294125852471)
        ·
          refine ⟨18907038733080441188778707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12604692488720294125852471 18907038733080441188778707)
          ·
            refine ⟨28360558099620661783168061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18907038733080441188778707 28360558099620661783168061)
            ·
              refine ⟨10635209287357748168688023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28360558099620661783168061 10635209287357748168688023)
              ·
                refine ⟨15952813931036622253032035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10635209287357748168688023 15952813931036622253032035)
                ·
                  refine ⟨23929220896554933379548053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15952813931036622253032035 23929220896554933379548053)
                  ·
                    refine ⟨1121682229526012502166315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23929220896554933379548053 1121682229526012502166315)
                    ·
                      rfl

theorem cell23_6553405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_6553405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553405 prefixEnd_6553405 := by exact prefixLift 6553405
  have htrace : WordTrace (prefixWord ++ tailWord_6553405) baseStart_6553405 baseEnd_6553405 := by
    simpa [prefixWord, tailWord_6553405, baseEnd_6553405] using wordTrace_append hprefix tailTrace_6553405
  have hstable : (prefixWord ++ tailWord_6553405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553405).length < 2 ^ (prefixWord ++ tailWord_6553405).sum := by decide
  have hdescent : baseEnd_6553405 < baseStart_6553405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553415 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_6553415 : Nat := 118140960795 + 6553415 * 2 ^ 59
def prefixEnd_6553415 : Nat := 4983230072969 + 3 ^ 40 * 6553415 * 2
def baseEnd_6553415 : Nat := 3365051823384582467373899

theorem tailTrace_6553415 : CollatzResearch.WordTrace tailWord_6553415 prefixEnd_6553415 3365051823384582467373899 := by
  unfold tailWord_6553415
  simp only [CollatzResearch.WordTrace]
  refine ⟨239022681553104164020325699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159348454368736109346883799 239022681553104164020325699)
  ·
    refine ⟨358534022329656246030488549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239022681553104164020325699 358534022329656246030488549)
    ·
      refine ⟨67225129186810546130716603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358534022329656246030488549 67225129186810546130716603)
      ·
        refine ⟨100837693780215819196074905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67225129186810546130716603 100837693780215819196074905)
        ·
          refine ⟨75628270335161864397056179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100837693780215819196074905 75628270335161864397056179)
          ·
            refine ⟨113442405502742796595584269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75628270335161864397056179 113442405502742796595584269)
            ·
              refine ⟨42540902063528548723344101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113442405502742796595584269 42540902063528548723344101)
              ·
                refine ⟨7976419136911602885627019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42540902063528548723344101 7976419136911602885627019)
                ·
                  refine ⟨11964628705367404328440529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976419136911602885627019 11964628705367404328440529)
                  ·
                    refine ⟨8973471529025553246330397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11964628705367404328440529 8973471529025553246330397)
                    ·
                      refine ⟨3365051823384582467373899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973471529025553246330397 3365051823384582467373899)
                      ·
                        rfl

theorem cell23_6553415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_6553415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553415 prefixEnd_6553415 := by exact prefixLift 6553415
  have htrace : WordTrace (prefixWord ++ tailWord_6553415) baseStart_6553415 baseEnd_6553415 := by
    simpa [prefixWord, tailWord_6553415, baseEnd_6553415] using wordTrace_append hprefix tailTrace_6553415
  have hstable : (prefixWord ++ tailWord_6553415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553415).length < 2 ^ (prefixWord ++ tailWord_6553415).sum := by decide
  have hdescent : baseEnd_6553415 < baseStart_6553415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553448 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6553448 : Nat := 118140960795 + 6553448 * 2 ^ 59
def prefixEnd_6553448 : Nat := 4983230072969 + 3 ^ 40 * 6553448 * 2
def baseEnd_6553448 : Nat := 1121689589415393612753749

theorem tailTrace_6553448 : CollatzResearch.WordTrace tailWord_6553448 prefixEnd_6553448 1121689589415393612753749 := by
  unfold tailWord_6553448
  simp only [CollatzResearch.WordTrace]
  refine ⟨119511942580992305328138499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159349256774656407104184665 119511942580992305328138499)
  ·
    refine ⟨179267913871488457992207749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119511942580992305328138499 179267913871488457992207749)
    ·
      refine ⟨33612733850904085873538953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179267913871488457992207749 33612733850904085873538953)
      ·
        refine ⟨25209550388178064405154215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33612733850904085873538953 25209550388178064405154215)
        ·
          refine ⟨37814325582267096607731323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209550388178064405154215 37814325582267096607731323)
          ·
            refine ⟨56721488373400644911596985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37814325582267096607731323 56721488373400644911596985)
            ·
              refine ⟨42541116280050483683697739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56721488373400644911596985 42541116280050483683697739)
              ·
                refine ⟨63811674420075725525546609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42541116280050483683697739 63811674420075725525546609)
                ·
                  refine ⟨47858755815056794144159957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63811674420075725525546609 47858755815056794144159957)
                  ·
                    refine ⟨1121689589415393612753749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47858755815056794144159957 1121689589415393612753749)
                    ·
                      rfl

theorem cell23_6553448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6553448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553448 prefixEnd_6553448 := by exact prefixLift 6553448
  have htrace : WordTrace (prefixWord ++ tailWord_6553448) baseStart_6553448 baseEnd_6553448 := by
    simpa [prefixWord, tailWord_6553448, baseEnd_6553448] using wordTrace_append hprefix tailTrace_6553448
  have hstable : (prefixWord ++ tailWord_6553448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553448).length < 2 ^ (prefixWord ++ tailWord_6553448).sum := by decide
  have hdescent : baseEnd_6553448 < baseStart_6553448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_6553488 : Nat := 118140960795 + 6553488 * 2 ^ 59
def prefixEnd_6553488 : Nat := 4983230072969 + 3 ^ 40 * 6553488 * 2
def baseEnd_6553488 : Nat := 3365089307472360681761063

theorem tailTrace_6553488 : CollatzResearch.WordTrace tailWord_6553488 prefixEnd_6553488 3365089307472360681761063 := by
  unfold tailWord_6553488
  simp only [CollatzResearch.WordTrace]
  refine ⟨119512672040919848743866559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159350229387893131658488745 119512672040919848743866559)
  ·
    refine ⟨179269008061379773115799839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119512672040919848743866559 179269008061379773115799839)
    ·
      refine ⟨268903512092069659673699759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179269008061379773115799839 268903512092069659673699759)
      ·
        refine ⟨403355268138104489510549639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268903512092069659673699759 403355268138104489510549639)
        ·
          refine ⟨605032902207156734265824459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403355268138104489510549639 605032902207156734265824459)
          ·
            refine ⟨907549353310735101398736689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605032902207156734265824459 907549353310735101398736689)
            ·
              refine ⟨680662014983051326049052517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907549353310735101398736689 680662014983051326049052517)
              ·
                refine ⟨127624127809322123634197347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680662014983051326049052517 127624127809322123634197347)
                ·
                  refine ⟨191436191713983185451296021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127624127809322123634197347 191436191713983185451296021)
                  ·
                    refine ⟨8973571486592961818029501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191436191713983185451296021 8973571486592961818029501)
                    ·
                      refine ⟨3365089307472360681761063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973571486592961818029501 3365089307472360681761063)
                      ·
                        rfl

theorem cell23_6553488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_6553488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553488 prefixEnd_6553488 := by exact prefixLift 6553488
  have htrace : WordTrace (prefixWord ++ tailWord_6553488) baseStart_6553488 baseEnd_6553488 := by
    simpa [prefixWord, tailWord_6553488, baseEnd_6553488] using wordTrace_append hprefix tailTrace_6553488
  have hstable : (prefixWord ++ tailWord_6553488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553488).length < 2 ^ (prefixWord ++ tailWord_6553488).sum := by decide
  have hdescent : baseEnd_6553488 < baseStart_6553488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553496 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6553496 : Nat := 118140960795 + 6553496 * 2 ^ 59
def prefixEnd_6553496 : Nat := 4983230072969 + 3 ^ 40 * 6553496 * 2
def baseEnd_6553496 : Nat := 3365093415317596650461027

theorem tailTrace_6553496 : CollatzResearch.WordTrace tailWord_6553496 prefixEnd_6553496 3365093415317596650461027 := by
  unfold tailWord_6553496
  simp only [CollatzResearch.WordTrace]
  refine ⟨119512817932905357427012171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159350423910540476569349561 119512817932905357427012171)
  ·
    refine ⟨179269226899358036140518257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119512817932905357427012171 179269226899358036140518257)
    ·
      refine ⟨134451920174518527105388693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179269226899358036140518257 134451920174518527105388693)
      ·
        refine ⟨6302433758180555958065095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134451920174518527105388693 6302433758180555958065095)
        ·
          refine ⟨9453650637270833937097643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302433758180555958065095 9453650637270833937097643)
          ·
            refine ⟨14180475955906250905646465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9453650637270833937097643 14180475955906250905646465)
            ·
              refine ⟨10635356966929688179234849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14180475955906250905646465 10635356966929688179234849)
              ·
                refine ⟨7976517725197266134426137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10635356966929688179234849 7976517725197266134426137)
                ·
                  refine ⟨5982388293897949600819603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976517725197266134426137 5982388293897949600819603)
                  ·
                    refine ⟨8973582440846924401229405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982388293897949600819603 8973582440846924401229405)
                    ·
                      refine ⟨3365093415317596650461027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973582440846924401229405 3365093415317596650461027)
                      ·
                        rfl

theorem cell23_6553496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6553496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553496 prefixEnd_6553496 := by exact prefixLift 6553496
  have htrace : WordTrace (prefixWord ++ tailWord_6553496) baseStart_6553496 baseEnd_6553496 := by
    simpa [prefixWord, tailWord_6553496, baseEnd_6553496] using wordTrace_append hprefix tailTrace_6553496
  have hstable : (prefixWord ++ tailWord_6553496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553496).length < 2 ^ (prefixWord ++ tailWord_6553496).sum := by decide
  have hdescent : baseEnd_6553496 < baseStart_6553496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553525 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 7]
def baseStart_6553525 : Nat := 118140960795 + 6553525 * 2 ^ 59
def prefixEnd_6553525 : Nat := 4983230072969 + 3 ^ 40 * 6553525 * 2
def baseEnd_6553525 : Nat := 373900922917397448555377

theorem tailTrace_6553525 : CollatzResearch.WordTrace tailWord_6553525 prefixEnd_6553525 373900922917397448555377 := by
  unfold tailWord_6553525
  simp only [CollatzResearch.WordTrace]
  refine ⟨239026693582705652806830029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159351129055137101871220019 239026693582705652806830029)
  ·
    refine ⟨89635010093514619802561261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239026693582705652806830029 89635010093514619802561261)
    ·
      refine ⟨33613128785067982425960473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89635010093514619802561261 33613128785067982425960473)
      ·
        refine ⟨25209846588800986819470355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33613128785067982425960473 25209846588800986819470355)
        ·
          refine ⟨37814769883201480229205533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209846588800986819470355 37814769883201480229205533)
          ·
            refine ⟨14180538706200555085952075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37814769883201480229205533 14180538706200555085952075)
            ·
              refine ⟨21270808059300832628928113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180538706200555085952075 21270808059300832628928113)
              ·
                refine ⟨15953106044475624471696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21270808059300832628928113 15953106044475624471696085)
                ·
                  refine ⟨373900922917397448555377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15953106044475624471696085 373900922917397448555377)
                  ·
                    rfl

theorem cell23_6553525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_6553525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553525 prefixEnd_6553525 := by exact prefixLift 6553525
  have htrace : WordTrace (prefixWord ++ tailWord_6553525) baseStart_6553525 baseEnd_6553525 := by
    simpa [prefixWord, tailWord_6553525, baseEnd_6553525] using wordTrace_append hprefix tailTrace_6553525
  have hstable : (prefixWord ++ tailWord_6553525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553525).length < 2 ^ (prefixWord ++ tailWord_6553525).sum := by decide
  have hdescent : baseEnd_6553525 < baseStart_6553525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553545 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 5, 2]
def baseStart_6553545 : Nat := 118140960795 + 6553545 * 2 ^ 59
def prefixEnd_6553545 : Nat := 4983230072969 + 3 ^ 40 * 6553545 * 2
def baseEnd_6553545 : Nat := 3365118575869666958748301

theorem tailTrace_6553545 : CollatzResearch.WordTrace tailWord_6553545 prefixEnd_6553545 3365118575869666958748301 := by
  unfold tailWord_6553545
  simp only [CollatzResearch.WordTrace]
  refine ⟨239027423042633196222558089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159351615361755464148372059 239027423042633196222558089)
  ·
    refine ⟨179270567281974897166918567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239027423042633196222558089 179270567281974897166918567)
    ·
      refine ⟨268905850922962345750377851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179270567281974897166918567 268905850922962345750377851)
      ·
        refine ⟨403358776384443518625566777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268905850922962345750377851 403358776384443518625566777)
        ·
          refine ⟨302519082288332638969175083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403358776384443518625566777 302519082288332638969175083)
          ·
            refine ⟨453778623432498958453762625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302519082288332638969175083 453778623432498958453762625)
            ·
              refine ⟨340333967574374218840321969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453778623432498958453762625 340333967574374218840321969)
              ·
                refine ⟨255250475680780664130241477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340333967574374218840321969 255250475680780664130241477)
                ·
                  refine ⟨47859464190146374524420277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255250475680780664130241477 47859464190146374524420277)
                  ·
                    refine ⟨4486824767826222611664401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47859464190146374524420277 4486824767826222611664401)
                    ·
                      refine ⟨3365118575869666958748301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486824767826222611664401 3365118575869666958748301)
                      ·
                        rfl

theorem cell23_6553545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5, 2].length) (baseStart_6553545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553545 prefixEnd_6553545 := by exact prefixLift 6553545
  have htrace : WordTrace (prefixWord ++ tailWord_6553545) baseStart_6553545 baseEnd_6553545 := by
    simpa [prefixWord, tailWord_6553545, baseEnd_6553545] using wordTrace_append hprefix tailTrace_6553545
  have hstable : (prefixWord ++ tailWord_6553545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553545).length < 2 ^ (prefixWord ++ tailWord_6553545).sum := by decide
  have hdescent : baseEnd_6553545 < baseStart_6553545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553570 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6553570 : Nat := 118140960795 + 6553570 * 2 ^ 59
def prefixEnd_6553570 : Nat := 4983230072969 + 3 ^ 40 * 6553570 * 2
def baseEnd_6553570 : Nat := 3365131412886029360935687

theorem tailTrace_6553570 : CollatzResearch.WordTrace tailWord_6553570 prefixEnd_6553570 3365131412886029360935687 := by
  unfold tailWord_6553570
  simp only [CollatzResearch.WordTrace]
  refine ⟨59757083716885656373054541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159352223245028416994812109 59757083716885656373054541)
  ·
    refine ⟨22408906393832121139895453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59757083716885656373054541 22408906393832121139895453)
    ·
      refine ⟨8403339897687045427460795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22408906393832121139895453 8403339897687045427460795)
      ·
        refine ⟨12605009846530568141191193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403339897687045427460795 12605009846530568141191193)
        ·
          refine ⟨9453757384897926105893395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605009846530568141191193 9453757384897926105893395)
          ·
            refine ⟨14180636077346889158840093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9453757384897926105893395 14180636077346889158840093)
            ·
              refine ⟨5317738529005083434565035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14180636077346889158840093 5317738529005083434565035)
              ·
                refine ⟨7976607793507625151847553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317738529005083434565035 7976607793507625151847553)
                ·
                  refine ⟨5982455845130718863885665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976607793507625151847553 5982455845130718863885665)
                  ·
                    refine ⟨4486841883848039147914249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982455845130718863885665 4486841883848039147914249)
                    ·
                      refine ⟨3365131412886029360935687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486841883848039147914249 3365131412886029360935687)
                      ·
                        rfl

theorem cell23_6553570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6553570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553570 prefixEnd_6553570 := by exact prefixLift 6553570
  have htrace : WordTrace (prefixWord ++ tailWord_6553570) baseStart_6553570 baseEnd_6553570 := by
    simpa [prefixWord, tailWord_6553570, baseEnd_6553570] using wordTrace_append hprefix tailTrace_6553570
  have hstable : (prefixWord ++ tailWord_6553570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553570).length < 2 ^ (prefixWord ++ tailWord_6553570).sum := by decide
  have hdescent : baseEnd_6553570 < baseStart_6553570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553595 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3]
def baseStart_6553595 : Nat := 118140960795 + 6553595 * 2 ^ 59
def prefixEnd_6553595 : Nat := 4983230072969 + 3 ^ 40 * 6553595 * 2
def baseEnd_6553595 : Nat := 3365144249902391763123071

theorem tailTrace_6553595 : CollatzResearch.WordTrace tailWord_6553595 prefixEnd_6553595 3365144249902391763123071 := by
  unfold tailWord_6553595
  simp only [CollatzResearch.WordTrace]
  refine ⟨239029246692452054761878239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159352831128301369841252159 239029246692452054761878239)
  ·
    refine ⟨358543870038678082142817359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239029246692452054761878239 358543870038678082142817359)
    ·
      refine ⟨537815805058017123214226039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358543870038678082142817359 537815805058017123214226039)
      ·
        refine ⟨806723707587025684821339059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537815805058017123214226039 806723707587025684821339059)
        ·
          refine ⟨1210085561380538527232008589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806723707587025684821339059 1210085561380538527232008589)
          ·
            refine ⟨453782085517701947712003221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210085561380538527232008589 453782085517701947712003221)
            ·
              refine ⟨21271035258642278799000151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 453782085517701947712003221 21271035258642278799000151)
              ·
                refine ⟨31906552887963418198500227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21271035258642278799000151 31906552887963418198500227)
                ·
                  refine ⟨47859829331945127297750341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31906552887963418198500227 47859829331945127297750341)
                  ·
                    refine ⟨8973717999739711368328189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47859829331945127297750341 8973717999739711368328189)
                    ·
                      refine ⟨3365144249902391763123071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973717999739711368328189 3365144249902391763123071)
                      ·
                        rfl

theorem cell23_6553595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 3].length) (baseStart_6553595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553595 prefixEnd_6553595 := by exact prefixLift 6553595
  have htrace : WordTrace (prefixWord ++ tailWord_6553595) baseStart_6553595 baseEnd_6553595 := by
    simpa [prefixWord, tailWord_6553595, baseEnd_6553595] using wordTrace_append hprefix tailTrace_6553595
  have hstable : (prefixWord ++ tailWord_6553595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553595).length < 2 ^ (prefixWord ++ tailWord_6553595).sum := by decide
  have hdescent : baseEnd_6553595 < baseStart_6553595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553612 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_6553612 : Nat := 118140960795 + 6553612 * 2 ^ 59
def prefixEnd_6553612 : Nat := 4983230072969 + 3 ^ 40 * 6553612 * 2
def baseEnd_6553612 : Nat := 3365152979073518196610493

theorem tailTrace_6553612 : CollatzResearch.WordTrace tailWord_6553612 prefixEnd_6553612 3365152979073518196610493 := by
  unfold tailWord_6553612
  simp only [CollatzResearch.WordTrace]
  refine ⟨119514933366695233332623545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159353244488926977776831393 119514933366695233332623545)
  ·
    refine ⟨89636200025021424999467659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119514933366695233332623545 89636200025021424999467659)
    ·
      refine ⟨134454300037532137499201489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89636200025021424999467659 134454300037532137499201489)
      ·
        refine ⟨100840725028149103124401117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134454300037532137499201489 100840725028149103124401117)
        ·
          refine ⟨37815271885555913671650419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100840725028149103124401117 37815271885555913671650419)
          ·
            refine ⟨56722907828333870507475629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37815271885555913671650419 56722907828333870507475629)
            ·
              refine ⟨21271090435625201440303361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56722907828333870507475629 21271090435625201440303361)
              ·
                refine ⟨15953317826718901080227521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21271090435625201440303361 15953317826718901080227521)
                ·
                  refine ⟨11964988370039175810170641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15953317826718901080227521 11964988370039175810170641)
                  ·
                    refine ⟨8973741277529381857627981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11964988370039175810170641 8973741277529381857627981)
                    ·
                      refine ⟨3365152979073518196610493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973741277529381857627981 3365152979073518196610493)
                      ·
                        rfl

theorem cell23_6553612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_6553612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553612 prefixEnd_6553612 := by exact prefixLift 6553612
  have htrace : WordTrace (prefixWord ++ tailWord_6553612) baseStart_6553612 baseEnd_6553612 := by
    simpa [prefixWord, tailWord_6553612, baseEnd_6553612] using wordTrace_append hprefix tailTrace_6553612
  have hstable : (prefixWord ++ tailWord_6553612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553612).length < 2 ^ (prefixWord ++ tailWord_6553612).sum := by decide
  have hdescent : baseEnd_6553612 < baseStart_6553612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553692 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6553692 : Nat := 118140960795 + 6553692 * 2 ^ 59
def prefixEnd_6553692 : Nat := 4983230072969 + 3 ^ 40 * 6553692 * 2
def baseEnd_6553692 : Nat := 1121731352508625961203375

theorem tailTrace_6553692 : CollatzResearch.WordTrace tailWord_6553692 prefixEnd_6553692 1121731352508625961203375 := by
  unfold tailWord_6553692
  simp only [CollatzResearch.WordTrace]
  refine ⟨119516392286550320164079665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159355189715400426885439553 119516392286550320164079665)
  ·
    refine ⟨89637294214912740123059749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119516392286550320164079665 89637294214912740123059749)
    ·
      refine ⟨16806992665296138773073703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89637294214912740123059749 16806992665296138773073703)
      ·
        refine ⟨25210488997944208159610555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16806992665296138773073703 25210488997944208159610555)
        ·
          refine ⟨37815733496916312239415833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25210488997944208159610555 37815733496916312239415833)
          ·
            refine ⟨28361800122687234179561875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37815733496916312239415833 28361800122687234179561875)
            ·
              refine ⟨42542700184030851269342813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28361800122687234179561875 42542700184030851269342813)
              ·
                refine ⟨15953512569011569226003555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42542700184030851269342813 15953512569011569226003555)
                ·
                  refine ⟨23930268853517353839005333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15953512569011569226003555 23930268853517353839005333)
                  ·
                    refine ⟨1121731352508625961203375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23930268853517353839005333 1121731352508625961203375)
                    ·
                      rfl

theorem cell23_6553692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6553692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553692 prefixEnd_6553692 := by exact prefixLift 6553692
  have htrace : WordTrace (prefixWord ++ tailWord_6553692) baseStart_6553692 baseEnd_6553692 := by
    simpa [prefixWord, tailWord_6553692, baseEnd_6553692] using wordTrace_append hprefix tailTrace_6553692
  have hstable : (prefixWord ++ tailWord_6553692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553692).length < 2 ^ (prefixWord ++ tailWord_6553692).sum := by decide
  have hdescent : baseEnd_6553692 < baseStart_6553692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553699 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 5, 2, 2]
def baseStart_6553699 : Nat := 118140960795 + 6553699 * 2 ^ 59
def prefixEnd_6553699 : Nat := 4983230072969 + 3 ^ 40 * 6553699 * 2
def baseEnd_6553699 : Nat := 3365197651890459356222593

theorem tailTrace_6553699 : CollatzResearch.WordTrace tailWord_6553699 prefixEnd_6553699 3365197651890459356222593 := by
  unfold tailWord_6553699
  simp only [CollatzResearch.WordTrace]
  refine ⟨239033039884075280523664151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159355359922716853682442767 239033039884075280523664151)
  ·
    refine ⟨358549559826112920785496227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239033039884075280523664151 358549559826112920785496227)
    ·
      refine ⟨537824339739169381178244341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358549559826112920785496227 537824339739169381178244341)
      ·
        refine ⟨50421031850547129485460407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 537824339739169381178244341 50421031850547129485460407)
        ·
          refine ⟨75631547775820694228190611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50421031850547129485460407 75631547775820694228190611)
          ·
            refine ⟨113447321663731041342285917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75631547775820694228190611 113447321663731041342285917)
            ·
              refine ⟨42542745623899140503357219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113447321663731041342285917 42542745623899140503357219)
              ·
                refine ⟨63814118435848710755035829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42542745623899140503357219 63814118435848710755035829)
                ·
                  refine ⟨5982573603360816633284609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63814118435848710755035829 5982573603360816633284609)
                  ·
                    refine ⟨4486930202520612474963457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982573603360816633284609 4486930202520612474963457)
                    ·
                      refine ⟨3365197651890459356222593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486930202520612474963457 3365197651890459356222593)
                      ·
                        rfl

theorem cell23_6553699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_6553699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553699 prefixEnd_6553699 := by exact prefixLift 6553699
  have htrace : WordTrace (prefixWord ++ tailWord_6553699) baseStart_6553699 baseEnd_6553699 := by
    simpa [prefixWord, tailWord_6553699, baseEnd_6553699] using wordTrace_append hprefix tailTrace_6553699
  have hstable : (prefixWord ++ tailWord_6553699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553699).length < 2 ^ (prefixWord ++ tailWord_6553699).sum := by decide
  have hdescent : baseEnd_6553699 < baseStart_6553699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553712 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_6553712 : Nat := 118140960795 + 6553712 * 2 ^ 59
def prefixEnd_6553712 : Nat := 4983230072969 + 3 ^ 40 * 6553712 * 2
def baseEnd_6553712 : Nat := 3365204327138967805360033

theorem tailTrace_6553712 : CollatzResearch.WordTrace tailWord_6553712 prefixEnd_6553712 3365204327138967805360033 := by
  unfold tailWord_6553712
  simp only [CollatzResearch.WordTrace]
  refine ⟨119516757016514091871943695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159355676022018789162591593 119516757016514091871943695)
  ·
    refine ⟨179275135524771137807915543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119516757016514091871943695 179275135524771137807915543)
    ·
      refine ⟨268912703287156706711873315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179275135524771137807915543 268912703287156706711873315)
      ·
        refine ⟨403369054930735060067809973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268912703287156706711873315 403369054930735060067809973)
        ·
          refine ⟨37815848899756411881357185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 403369054930735060067809973 37815848899756411881357185)
          ·
            refine ⟨28361886674817308911017889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37815848899756411881357185 28361886674817308911017889)
            ·
              refine ⟨21271415006112981683263417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28361886674817308911017889 21271415006112981683263417)
              ·
                refine ⟨15953561254584736262447563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21271415006112981683263417 15953561254584736262447563)
                ·
                  refine ⟨23930341881877104393671345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15953561254584736262447563 23930341881877104393671345)
                  ·
                    refine ⟨17947756411407828295253509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23930341881877104393671345 17947756411407828295253509)
                    ·
                      refine ⟨3365204327138967805360033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17947756411407828295253509 3365204327138967805360033)
                      ·
                        rfl

theorem cell23_6553712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_6553712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553712 prefixEnd_6553712 := by exact prefixLift 6553712
  have htrace : WordTrace (prefixWord ++ tailWord_6553712) baseStart_6553712 baseEnd_6553712 := by
    simpa [prefixWord, tailWord_6553712, baseEnd_6553712] using wordTrace_append hprefix tailTrace_6553712
  have hstable : (prefixWord ++ tailWord_6553712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553712).length < 2 ^ (prefixWord ++ tailWord_6553712).sum := by decide
  have hdescent : baseEnd_6553712 < baseStart_6553712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553719 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_6553719 : Nat := 118140960795 + 6553719 * 2 ^ 59
def prefixEnd_6553719 : Nat := 4983230072969 + 3 ^ 40 * 6553719 * 2
def baseEnd_6553719 : Nat := 3365207921503549277972501

theorem tailTrace_6553719 : CollatzResearch.WordTrace tailWord_6553719 prefixEnd_6553719 3365207921503549277972501 := by
  unfold tailWord_6553719
  simp only [CollatzResearch.WordTrace]
  refine ⟨239033769344002823939392211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159355846229335215959594807 239033769344002823939392211)
  ·
    refine ⟨358550654016004235909088317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239033769344002823939392211 358550654016004235909088317)
    ·
      refine ⟨134456495256001588465908119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358550654016004235909088317 134456495256001588465908119)
      ·
        refine ⟨201684742884002382698862179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134456495256001588465908119 201684742884002382698862179)
        ·
          refine ⟨302527114326003574048293269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201684742884002382698862179 302527114326003574048293269)
          ·
            refine ⟨14180958484031417533513747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 302527114326003574048293269 14180958484031417533513747)
            ·
              refine ⟨21271437726047126300270621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180958484031417533513747 21271437726047126300270621)
              ·
                refine ⟨7976789147267672362601483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21271437726047126300270621 7976789147267672362601483)
                ·
                  refine ⟨11965183720901508543902225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976789147267672362601483 11965183720901508543902225)
                  ·
                    refine ⟨8973887790676131407926669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11965183720901508543902225 8973887790676131407926669)
                    ·
                      refine ⟨3365207921503549277972501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8973887790676131407926669 3365207921503549277972501)
                      ·
                        rfl

theorem cell23_6553719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_6553719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553719 prefixEnd_6553719 := by exact prefixLift 6553719
  have htrace : WordTrace (prefixWord ++ tailWord_6553719) baseStart_6553719 baseEnd_6553719 := by
    simpa [prefixWord, tailWord_6553719, baseEnd_6553719] using wordTrace_append hprefix tailTrace_6553719
  have hstable : (prefixWord ++ tailWord_6553719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553719).length < 2 ^ (prefixWord ++ tailWord_6553719).sum := by decide
  have hdescent : baseEnd_6553719 < baseStart_6553719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553733 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_6553733 : Nat := 118140960795 + 6553733 * 2 ^ 59
def prefixEnd_6553733 : Nat := 4983230072969 + 3 ^ 40 * 6553733 * 2
def baseEnd_6553733 : Nat := 3365215110232712223197437

theorem tailTrace_6553733 : CollatzResearch.WordTrace tailWord_6553733 prefixEnd_6553733 3365215110232712223197437 := by
  unfold tailWord_6553733
  simp only [CollatzResearch.WordTrace]
  refine ⟨239034279965952104330401853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159356186643968069553601235 239034279965952104330401853)
  ·
    refine ⟨89637854987232039123900695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239034279965952104330401853 89637854987232039123900695)
    ·
      refine ⟨134456782480848058685851043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89637854987232039123900695 134456782480848058685851043)
      ·
        refine ⟨201685173721272088028776565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134456782480848058685851043 201685173721272088028776565)
        ·
          refine ⟨18907985036369258252697803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201685173721272088028776565 18907985036369258252697803)
          ·
            refine ⟨28361977554553887379046705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18907985036369258252697803 28361977554553887379046705)
            ·
              refine ⟨21271483165915415534285029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28361977554553887379046705 21271483165915415534285029)
              ·
                refine ⟨3988403093609140412678443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21271483165915415534285029 3988403093609140412678443)
                ·
                  refine ⟨5982604640413710619017665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988403093609140412678443 5982604640413710619017665)
                  ·
                    refine ⟨4486953480310282964263249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982604640413710619017665 4486953480310282964263249)
                    ·
                      refine ⟨3365215110232712223197437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486953480310282964263249 3365215110232712223197437)
                      ·
                        rfl

theorem cell23_6553733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_6553733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553733 prefixEnd_6553733 := by exact prefixLift 6553733
  have htrace : WordTrace (prefixWord ++ tailWord_6553733) baseStart_6553733 baseEnd_6553733 := by
    simpa [prefixWord, tailWord_6553733, baseEnd_6553733] using wordTrace_append hprefix tailTrace_6553733
  have hstable : (prefixWord ++ tailWord_6553733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553733).length < 2 ^ (prefixWord ++ tailWord_6553733).sum := by decide
  have hdescent : baseEnd_6553733 < baseStart_6553733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553735 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 9]
def baseStart_6553735 : Nat := 118140960795 + 6553735 * 2 ^ 59
def prefixEnd_6553735 : Nat := 4983230072969 + 3 ^ 40 * 6553735 * 2
def baseEnd_6553735 : Nat := 1121738712398007071790809

theorem tailTrace_6553735 : CollatzResearch.WordTrace tailWord_6553735 prefixEnd_6553735 1121738712398007071790809 := by
  unfold tailWord_6553735
  simp only [CollatzResearch.WordTrace]
  refine ⟨239034352911944858671974659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159356235274629905781316439 239034352911944858671974659)
  ·
    refine ⟨358551529367917288007961989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239034352911944858671974659 358551529367917288007961989)
    ·
      refine ⟨67228411756484491501492873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358551529367917288007961989 67228411756484491501492873)
      ·
        refine ⟨50421308817363368626119655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67228411756484491501492873 50421308817363368626119655)
        ·
          refine ⟨75631963226045052939179483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50421308817363368626119655 75631963226045052939179483)
          ·
            refine ⟨113447944839067579408769225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75631963226045052939179483 113447944839067579408769225)
            ·
              refine ⟨85085958629300684556576919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113447944839067579408769225 85085958629300684556576919)
              ·
                refine ⟨127628937943951026834865379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85085958629300684556576919 127628937943951026834865379)
                ·
                  refine ⟨191443406915926540252298069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127628937943951026834865379 191443406915926540252298069)
                  ·
                    refine ⟨1121738712398007071790809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 191443406915926540252298069 1121738712398007071790809)
                    ·
                      rfl

theorem cell23_6553735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_6553735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553735 prefixEnd_6553735 := by exact prefixLift 6553735
  have htrace : WordTrace (prefixWord ++ tailWord_6553735) baseStart_6553735 baseEnd_6553735 := by
    simpa [prefixWord, tailWord_6553735, baseEnd_6553735] using wordTrace_append hprefix tailTrace_6553735
  have hstable : (prefixWord ++ tailWord_6553735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553735).length < 2 ^ (prefixWord ++ tailWord_6553735).sum := by decide
  have hdescent : baseEnd_6553735 < baseStart_6553735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553745 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_6553745 : Nat := 118140960795 + 6553745 * 2 ^ 59
def prefixEnd_6553745 : Nat := 4983230072969 + 3 ^ 40 * 6553745 * 2
def baseEnd_6553745 : Nat := 3365221272000566176247381

theorem tailTrace_6553745 : CollatzResearch.WordTrace tailWord_6553745 prefixEnd_6553745 3365221272000566176247381 := by
  unfold tailWord_6553745
  simp only [CollatzResearch.WordTrace]
  refine ⟨239034717641908630379838689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159356478427939086919892459 239034717641908630379838689)
  ·
    refine ⟨179276038231431472784879017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239034717641908630379838689 179276038231431472784879017)
    ·
      refine ⟨134457028673573604588659263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179276038231431472784879017 134457028673573604588659263)
      ·
        refine ⟨201685543010360406882988895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134457028673573604588659263 201685543010360406882988895)
        ·
          refine ⟨302528314515540610324483343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201685543010360406882988895 302528314515540610324483343)
          ·
            refine ⟨453792471773310915486725015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302528314515540610324483343 453792471773310915486725015)
            ·
              refine ⟨680688707659966373230087523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453792471773310915486725015 680688707659966373230087523)
              ·
                refine ⟨1021033061489949559845131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680688707659966373230087523 1021033061489949559845131285)
                ·
                  refine ⟨47860924757341385617740529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1021033061489949559845131285 47860924757341385617740529)
                  ·
                    refine ⟨35895693568006039213305397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47860924757341385617740529 35895693568006039213305397)
                    ·
                      refine ⟨3365221272000566176247381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35895693568006039213305397 3365221272000566176247381)
                      ·
                        rfl

theorem cell23_6553745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_6553745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553745 prefixEnd_6553745 := by exact prefixLift 6553745
  have htrace : WordTrace (prefixWord ++ tailWord_6553745) baseStart_6553745 baseEnd_6553745 := by
    simpa [prefixWord, tailWord_6553745, baseEnd_6553745] using wordTrace_append hprefix tailTrace_6553745
  have hstable : (prefixWord ++ tailWord_6553745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553745).length < 2 ^ (prefixWord ++ tailWord_6553745).sum := by decide
  have hdescent : baseEnd_6553745 < baseStart_6553745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553767 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6553767 : Nat := 118140960795 + 6553767 * 2 ^ 59
def prefixEnd_6553767 : Nat := 4983230072969 + 3 ^ 40 * 6553767 * 2
def baseEnd_6553767 : Nat := 3365232568574965090172281

theorem tailTrace_6553767 : CollatzResearch.WordTrace tailWord_6553767 prefixEnd_6553767 3365232568574965090172281 := by
  unfold tailWord_6553767
  simp only [CollatzResearch.WordTrace]
  refine ⟨239035520047828928137139555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159357013365219285424759703 239035520047828928137139555)
  ·
    refine ⟨358553280071743392205709333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239035520047828928137139555 358553280071743392205709333)
    ·
      refine ⟨16807185003362971509642625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 358553280071743392205709333 16807185003362971509642625)
      ·
        refine ⟨12605388752522228632231969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16807185003362971509642625 12605388752522228632231969)
        ·
          refine ⟨9454041564391671474173977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605388752522228632231969 9454041564391671474173977)
          ·
            refine ⟨7090531173293753605630483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454041564391671474173977 7090531173293753605630483)
            ·
              refine ⟨10635796759940630408445725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090531173293753605630483 10635796759940630408445725)
              ·
                refine ⟨3988423784977736403167147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10635796759940630408445725 3988423784977736403167147)
                ·
                  refine ⟨5982635677466604604750721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988423784977736403167147 5982635677466604604750721)
                  ·
                    refine ⟨4486976758099953453563041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982635677466604604750721 4486976758099953453563041)
                    ·
                      refine ⟨3365232568574965090172281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4486976758099953453563041 3365232568574965090172281)
                      ·
                        rfl

theorem cell23_6553767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6553767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553767 prefixEnd_6553767 := by exact prefixLift 6553767
  have htrace : WordTrace (prefixWord ++ tailWord_6553767) baseStart_6553767 baseEnd_6553767 := by
    simpa [prefixWord, tailWord_6553767, baseEnd_6553767] using wordTrace_append hprefix tailTrace_6553767
  have hstable : (prefixWord ++ tailWord_6553767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553767).length < 2 ^ (prefixWord ++ tailWord_6553767).sum := by decide
  have hdescent : baseEnd_6553767 < baseStart_6553767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553802 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_6553802 : Nat := 118140960795 + 6553802 * 2 ^ 59
def prefixEnd_6553802 : Nat := 4983230072969 + 3 ^ 40 * 6553802 * 2
def baseEnd_6553802 : Nat := 3365250540397872453234619

theorem tailTrace_6553802 : CollatzResearch.WordTrace tailWord_6553802 prefixEnd_6553802 3365250540397872453234619 := by
  unfold tailWord_6553802
  simp only [CollatzResearch.WordTrace]
  refine ⟨59759199150675532278665915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159357864401801419409775773 59759199150675532278665915)
  ·
    refine ⟨89638798726013298417998873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59759199150675532278665915 89638798726013298417998873)
    ·
      refine ⟨67229099044509973813499155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89638798726013298417998873 67229099044509973813499155)
      ·
        refine ⟨100843648566764960720248733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67229099044509973813499155 100843648566764960720248733)
        ·
          refine ⟨37816368212536860270093275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100843648566764960720248733 37816368212536860270093275)
          ·
            refine ⟨56724552318805290405139913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37816368212536860270093275 56724552318805290405139913)
            ·
              refine ⟨42543414239103967803854935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56724552318805290405139913 42543414239103967803854935)
              ·
                refine ⟨63815121358655951705782403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42543414239103967803854935 63815121358655951705782403)
                ·
                  refine ⟨95722682037983927558673605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63815121358655951705782403 95722682037983927558673605)
                  ·
                    refine ⟨17948002882121986417251301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95722682037983927558673605 17948002882121986417251301)
                    ·
                      refine ⟨3365250540397872453234619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17948002882121986417251301 3365250540397872453234619)
                      ·
                        rfl

theorem cell23_6553802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_6553802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553802 prefixEnd_6553802 := by exact prefixLift 6553802
  have htrace : WordTrace (prefixWord ++ tailWord_6553802) baseStart_6553802 baseEnd_6553802 := by
    simpa [prefixWord, tailWord_6553802, baseEnd_6553802] using wordTrace_append hprefix tailTrace_6553802
  have hstable : (prefixWord ++ tailWord_6553802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553802).length < 2 ^ (prefixWord ++ tailWord_6553802).sum := by decide
  have hdescent : baseEnd_6553802 < baseStart_6553802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553879 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6553879 : Nat := 118140960795 + 6553879 * 2 ^ 59
def prefixEnd_6553879 : Nat := 4983230072969 + 3 ^ 40 * 6553879 * 2
def baseEnd_6553879 : Nat := 3365290078408268651971765

theorem tailTrace_6553879 : CollatzResearch.WordTrace tailWord_6553879 prefixEnd_6553879 3365290078408268651971765 := by
  unfold tailWord_6553879
  simp only [CollatzResearch.WordTrace]
  refine ⟨239039605023423171265216691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159359736682282114176811127 239039605023423171265216691)
  ·
    refine ⟨358559407535134756897825037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239039605023423171265216691 358559407535134756897825037)
    ·
      refine ⟨134459777825675533836684389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358559407535134756897825037 134459777825675533836684389)
      ·
        refine ⟨25211208342314162594378323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134459777825675533836684389 25211208342314162594378323)
        ·
          refine ⟨37816812513471243891567485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25211208342314162594378323 37816812513471243891567485)
          ·
            refine ⟨14181304692551716459337807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37816812513471243891567485 14181304692551716459337807)
            ·
              refine ⟨21271957038827574689006711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14181304692551716459337807 21271957038827574689006711)
              ·
                refine ⟨31907935558241362033510067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21271957038827574689006711 31907935558241362033510067)
                ·
                  refine ⟨47861903337362043050265101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31907935558241362033510067 47861903337362043050265101)
                  ·
                    refine ⟨17948213751510766143849413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47861903337362043050265101 17948213751510766143849413)
                    ·
                      refine ⟨3365290078408268651971765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17948213751510766143849413 3365290078408268651971765)
                      ·
                        rfl

theorem cell23_6553879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6553879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553879 prefixEnd_6553879 := by exact prefixLift 6553879
  have htrace : WordTrace (prefixWord ++ tailWord_6553879) baseStart_6553879 baseEnd_6553879 := by
    simpa [prefixWord, tailWord_6553879, baseEnd_6553879] using wordTrace_append hprefix tailTrace_6553879
  have hstable : (prefixWord ++ tailWord_6553879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553879).length < 2 ^ (prefixWord ++ tailWord_6553879).sum := by decide
  have hdescent : baseEnd_6553879 < baseStart_6553879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553940 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_6553940 : Nat := 118140960795 + 6553940 * 2 ^ 59
def prefixEnd_6553940 : Nat := 4983230072969 + 3 ^ 40 * 6553940 * 2
def baseEnd_6553940 : Nat := 1121773800242730971102995

theorem tailTrace_6553940 : CollatzResearch.WordTrace tailWord_6553940 prefixEnd_6553940 1121773800242730971102995 := by
  unfold tailWord_6553940
  simp only [CollatzResearch.WordTrace]
  refine ⟨119520914938101089341593637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159361219917468119122124849 119520914938101089341593637)
  ·
    refine ⟨22410171550893954251548807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119520914938101089341593637 22410171550893954251548807)
    ·
      refine ⟨33615257326340931377323211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22410171550893954251548807 33615257326340931377323211)
      ·
        refine ⟨50422885989511397065984817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33615257326340931377323211 50422885989511397065984817)
        ·
          refine ⟨37817164492133547799488613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50422885989511397065984817 37817164492133547799488613)
          ·
            refine ⟨7090718342275040212404115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37817164492133547799488613 7090718342275040212404115)
            ·
              refine ⟨10636077513412560318606173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090718342275040212404115 10636077513412560318606173)
              ·
                refine ⟨3988529067529710119477315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10636077513412560318606173 3988529067529710119477315)
                ·
                  refine ⟨5982793601294565179215973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988529067529710119477315 5982793601294565179215973)
                  ·
                    refine ⟨1121773800242730971102995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5982793601294565179215973 1121773800242730971102995)
                    ·
                      rfl

theorem cell23_6553940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_6553940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553940 prefixEnd_6553940 := by exact prefixLift 6553940
  have htrace : WordTrace (prefixWord ++ tailWord_6553940) baseStart_6553940 baseEnd_6553940 := by
    simpa [prefixWord, tailWord_6553940, baseEnd_6553940] using wordTrace_append hprefix tailTrace_6553940
  have hstable : (prefixWord ++ tailWord_6553940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553940).length < 2 ^ (prefixWord ++ tailWord_6553940).sum := by decide
  have hdescent : baseEnd_6553940 < baseStart_6553940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6553969 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_6553969 : Nat := 118140960795 + 6553969 * 2 ^ 59
def prefixEnd_6553969 : Nat := 4983230072969 + 3 ^ 40 * 6553969 * 2
def baseEnd_6553969 : Nat := 3365336291667173299846351

theorem tailTrace_6553969 : CollatzResearch.WordTrace tailWord_6553969 prefixEnd_6553969 3365336291667173299846351 := by
  unfold tailWord_6553969
  simp only [CollatzResearch.WordTrace]
  refine ⟨239042887593097116635992961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159361925062064744423995307 239042887593097116635992961)
  ·
    refine ⟨179282165694822837476994721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239042887593097116635992961 179282165694822837476994721)
    ·
      refine ⟨134461624271117128107746041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179282165694822837476994721 134461624271117128107746041)
      ·
        refine ⟨100846218203337846080809531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134461624271117128107746041 100846218203337846080809531)
        ·
          refine ⟨151269327305006769121214297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100846218203337846080809531 151269327305006769121214297)
          ·
            refine ⟨113451995478755076840910723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151269327305006769121214297 113451995478755076840910723)
            ·
              refine ⟨170177993218132615261366085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113451995478755076840910723 170177993218132615261366085)
              ·
                refine ⟨31908373728399865361506141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170177993218132615261366085 31908373728399865361506141)
                ·
                  refine ⟨11965640148149949510564803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31908373728399865361506141 11965640148149949510564803)
                  ·
                    refine ⟨17948460222224924265847205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11965640148149949510564803 17948460222224924265847205)
                    ·
                      refine ⟨3365336291667173299846351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17948460222224924265847205 3365336291667173299846351)
                      ·
                        rfl

theorem cell23_6553969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_6553969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6553969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6553969 prefixEnd_6553969 := by exact prefixLift 6553969
  have htrace : WordTrace (prefixWord ++ tailWord_6553969) baseStart_6553969 baseEnd_6553969 := by
    simpa [prefixWord, tailWord_6553969, baseEnd_6553969] using wordTrace_append hprefix tailTrace_6553969
  have hstable : (prefixWord ++ tailWord_6553969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6553969).length < 2 ^ (prefixWord ++ tailWord_6553969).sum := by decide
  have hdescent : baseEnd_6553969 < baseStart_6553969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6553969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554014 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6554014 : Nat := 118140960795 + 6554014 * 2 ^ 59
def prefixEnd_6554014 : Nat := 4983230072969 + 3 ^ 40 * 6554014 * 2
def baseEnd_6554014 : Nat := 3365359398296625623783645

theorem tailTrace_6554014 : CollatzResearch.WordTrace tailWord_6554014 prefixEnd_6554014 3365359398296625623783645 := by
  unfold tailWord_6554014
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880566109741761165172637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159363019251956059547587397 29880566109741761165172637)
  ·
    refine ⟨11205212291153160436939739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29880566109741761165172637 11205212291153160436939739)
    ·
      refine ⟨16807818436729740655409609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11205212291153160436939739 16807818436729740655409609)
      ·
        refine ⟨12605863827547305491557207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16807818436729740655409609 12605863827547305491557207)
        ·
          refine ⟨18908795741320958237335811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12605863827547305491557207 18908795741320958237335811)
          ·
            refine ⟨28363193611981437356003717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18908795741320958237335811 28363193611981437356003717)
            ·
              refine ⟨5318098802246519504250697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28363193611981437356003717 5318098802246519504250697)
              ·
                refine ⟨3988574101684889628188023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318098802246519504250697 3988574101684889628188023)
                ·
                  refine ⟨5982861152527334442282035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988574101684889628188023 5982861152527334442282035)
                  ·
                    refine ⟨8974291728791001663423053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982861152527334442282035 8974291728791001663423053)
                    ·
                      refine ⟨3365359398296625623783645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974291728791001663423053 3365359398296625623783645)
                      ·
                        rfl

theorem cell23_6554014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6554014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554014 prefixEnd_6554014 := by exact prefixLift 6554014
  have htrace : WordTrace (prefixWord ++ tailWord_6554014) baseStart_6554014 baseEnd_6554014 := by
    simpa [prefixWord, tailWord_6554014, baseEnd_6554014] using wordTrace_append hprefix tailTrace_6554014
  have hstable : (prefixWord ++ tailWord_6554014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554014).length < 2 ^ (prefixWord ++ tailWord_6554014).sum := by decide
  have hdescent : baseEnd_6554014 < baseStart_6554014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554070 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6554070 : Nat := 118140960795 + 6554070 * 2 ^ 59
def prefixEnd_6554070 : Nat := 4983230072969 + 3 ^ 40 * 6554070 * 2
def baseEnd_6554070 : Nat := 3365388153213277404683387

theorem tailTrace_6554070 : CollatzResearch.WordTrace tailWord_6554070 prefixEnd_6554070 3365388153213277404683387 := by
  unfold tailWord_6554070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940410710358200680338729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159364380910487473923613109 14940410710358200680338729)
  ·
    refine ⟨11205308032768650510254047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14940410710358200680338729 11205308032768650510254047)
    ·
      refine ⟨16807962049152975765381071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11205308032768650510254047 16807962049152975765381071)
      ·
        refine ⟨25211943073729463648071607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16807962049152975765381071 25211943073729463648071607)
        ·
          refine ⟨37817914610594195472107411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25211943073729463648071607 37817914610594195472107411)
          ·
            refine ⟨56726871915891293208161117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37817914610594195472107411 56726871915891293208161117)
            ·
              refine ⟨21272576968459234953060419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56726871915891293208161117 21272576968459234953060419)
              ·
                refine ⟨31908865452688852429590629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21272576968459234953060419 31908865452688852429590629)
                ·
                  refine ⟨5982912272379159830548243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31908865452688852429590629 5982912272379159830548243)
                  ·
                    refine ⟨8974368408568739745822365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982912272379159830548243 8974368408568739745822365)
                    ·
                      refine ⟨3365388153213277404683387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974368408568739745822365 3365388153213277404683387)
                      ·
                        rfl

theorem cell23_6554070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6554070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554070 prefixEnd_6554070 := by exact prefixLift 6554070
  have htrace : WordTrace (prefixWord ++ tailWord_6554070) baseStart_6554070 baseEnd_6554070 := by
    simpa [prefixWord, tailWord_6554070, baseEnd_6554070] using wordTrace_append hprefix tailTrace_6554070
  have hstable : (prefixWord ++ tailWord_6554070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554070).length < 2 ^ (prefixWord ++ tailWord_6554070).sum := by decide
  have hdescent : baseEnd_6554070 < baseStart_6554070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554089 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_6554089 : Nat := 118140960795 + 6554089 * 2 ^ 59
def prefixEnd_6554089 : Nat := 4983230072969 + 3 ^ 40 * 6554089 * 2
def baseEnd_6554089 : Nat := 3365397909345712830345799

theorem tailTrace_6554089 : CollatzResearch.WordTrace tailWord_6554089 prefixEnd_6554089 3365397909345712830345799 := by
  unfold tailWord_6554089
  simp only [CollatzResearch.WordTrace]
  refine ⟨239047264352662377130361321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159364842901774918086907547 239047264352662377130361321)
  ·
    refine ⟨179285448264496782847770991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239047264352662377130361321 179285448264496782847770991)
    ·
      refine ⟨268928172396745174271656487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179285448264496782847770991 268928172396745174271656487)
      ·
        refine ⟨403392258595117761407484731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268928172396745174271656487 403392258595117761407484731)
        ·
          refine ⟨605088387892676642111227097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403392258595117761407484731 605088387892676642111227097)
          ·
            refine ⟨453816290919507481583420323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605088387892676642111227097 453816290919507481583420323)
            ·
              refine ⟨680724436379261222375130485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453816290919507481583420323 680724436379261222375130485)
              ·
                refine ⟨63817915910555739597668483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680724436379261222375130485 63817915910555739597668483)
                ·
                  refine ⟨95726873865833609396502725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63817915910555739597668483 95726873865833609396502725)
                  ·
                    refine ⟨17948788849843801761844261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95726873865833609396502725 17948788849843801761844261)
                    ·
                      refine ⟨3365397909345712830345799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17948788849843801761844261 3365397909345712830345799)
                      ·
                        rfl

theorem cell23_6554089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_6554089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554089 prefixEnd_6554089 := by exact prefixLift 6554089
  have htrace : WordTrace (prefixWord ++ tailWord_6554089) baseStart_6554089 baseEnd_6554089 := by
    simpa [prefixWord, tailWord_6554089, baseEnd_6554089] using wordTrace_append hprefix tailTrace_6554089
  have hstable : (prefixWord ++ tailWord_6554089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554089).length < 2 ^ (prefixWord ++ tailWord_6554089).sum := by decide
  have hdescent : baseEnd_6554089 < baseStart_6554089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554099 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 7]
def baseStart_6554099 : Nat := 118140960795 + 6554099 * 2 ^ 59
def prefixEnd_6554099 : Nat := 4983230072969 + 3 ^ 40 * 6554099 * 2
def baseEnd_6554099 : Nat := 373933671572473087913417

theorem tailTrace_6554099 : CollatzResearch.WordTrace tailWord_6554099 prefixEnd_6554099 373933671572473087913417 := by
  unfold tailWord_6554099
  simp only [CollatzResearch.WordTrace]
  refine ⟨239047629082626148838225351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159365086055084099225483567 239047629082626148838225351)
  ·
    refine ⟨358571443623939223257338027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239047629082626148838225351 358571443623939223257338027)
    ·
      refine ⟨537857165435908834886007041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358571443623939223257338027 537857165435908834886007041)
      ·
        refine ⟨403392874076931626164505281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537857165435908834886007041 403392874076931626164505281)
        ·
          refine ⟨302544655557698719623378961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403392874076931626164505281 302544655557698719623378961)
          ·
            refine ⟨226908491668274039717534221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302544655557698719623378961 226908491668274039717534221)
            ·
              refine ⟨85090684375602764894075333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226908491668274039717534221 85090684375602764894075333)
              ·
                refine ⟨15954503320425518417639125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85090684375602764894075333 15954503320425518417639125)
                ·
                  refine ⟨373933671572473087913417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15954503320425518417639125 373933671572473087913417)
                  ·
                    rfl

theorem cell23_6554099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 7].length) (baseStart_6554099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554099 prefixEnd_6554099 := by exact prefixLift 6554099
  have htrace : WordTrace (prefixWord ++ tailWord_6554099) baseStart_6554099 baseEnd_6554099 := by
    simpa [prefixWord, tailWord_6554099, baseEnd_6554099] using wordTrace_append hprefix tailTrace_6554099
  have hstable : (prefixWord ++ tailWord_6554099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554099).length < 2 ^ (prefixWord ++ tailWord_6554099).sum := by decide
  have hdescent : baseEnd_6554099 < baseStart_6554099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554129 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_6554129 : Nat := 118140960795 + 6554129 * 2 ^ 59
def prefixEnd_6554129 : Nat := 4983230072969 + 3 ^ 40 * 6554129 * 2
def baseEnd_6554129 : Nat := 1121806149523964224615205

theorem tailTrace_6554129 : CollatzResearch.WordTrace tailWord_6554129 prefixEnd_6554129 1121806149523964224615205 := by
  unfold tailWord_6554129
  simp only [CollatzResearch.WordTrace]
  refine ⟨239048723272517463961817441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159365815515011642641211627 239048723272517463961817441)
  ·
    refine ⟨179286542454388097971363081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239048723272517463961817441 179286542454388097971363081)
    ·
      refine ⟨134464906840791073478522311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179286542454388097971363081 134464906840791073478522311)
      ·
        refine ⟨201697360261186610217783467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134464906840791073478522311 201697360261186610217783467)
        ·
          refine ⟨302546040391779915326675201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201697360261186610217783467 302546040391779915326675201)
          ·
            refine ⟨226909530293834936495006401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302546040391779915326675201 226909530293834936495006401)
            ·
              refine ⟨170182147720376202371254801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226909530293834936495006401 170182147720376202371254801)
              ·
                refine ⟨127636610790282151778441101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170182147720376202371254801 127636610790282151778441101)
                ·
                  refine ⟨47863729046355806916915413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127636610790282151778441101 47863729046355806916915413)
                  ·
                    refine ⟨1121806149523964224615205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47863729046355806916915413 1121806149523964224615205)
                    ·
                      rfl

theorem cell23_6554129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_6554129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554129 prefixEnd_6554129 := by exact prefixLift 6554129
  have htrace : WordTrace (prefixWord ++ tailWord_6554129) baseStart_6554129 baseEnd_6554129 := by
    simpa [prefixWord, tailWord_6554129, baseEnd_6554129] using wordTrace_append hprefix tailTrace_6554129
  have hstable : (prefixWord ++ tailWord_6554129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554129).length < 2 ^ (prefixWord ++ tailWord_6554129).sum := by decide
  have hdescent : baseEnd_6554129 < baseStart_6554129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554146 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6554146 : Nat := 118140960795 + 6554146 * 2 ^ 59
def prefixEnd_6554146 : Nat := 4983230072969 + 3 ^ 40 * 6554146 * 2
def baseEnd_6554146 : Nat := 1121809059247673035777679

theorem tailTrace_6554146 : CollatzResearch.WordTrace tailWord_6554146 prefixEnd_6554146 1121809059247673035777679 := by
  unfold tailWord_6554146
  simp only [CollatzResearch.WordTrace]
  refine ⟨59762335828363968966296573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159366228875637250576790861 59762335828363968966296573)
  ·
    refine ⟨22410875935636488362361215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59762335828363968966296573 22410875935636488362361215)
    ·
      refine ⟨33616313903454732543541823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22410875935636488362361215 33616313903454732543541823)
      ·
        refine ⟨50424470855182098815312735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33616313903454732543541823 50424470855182098815312735)
        ·
          refine ⟨75636706282773148222969103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50424470855182098815312735 75636706282773148222969103)
          ·
            refine ⟨113455059424159722334453655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75636706282773148222969103 113455059424159722334453655)
            ·
              refine ⟨170182589136239583501680483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113455059424159722334453655 170182589136239583501680483)
              ·
                refine ⟨255273883704359375252520725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170182589136239583501680483 255273883704359375252520725)
                ·
                  refine ⟨11965963298641845714961909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255273883704359375252520725 11965963298641845714961909)
                  ·
                    refine ⟨1121809059247673035777679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11965963298641845714961909 1121809059247673035777679)
                    ·
                      rfl

theorem cell23_6554146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6554146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554146 prefixEnd_6554146 := by exact prefixLift 6554146
  have htrace : WordTrace (prefixWord ++ tailWord_6554146) baseStart_6554146 baseEnd_6554146 := by
    simpa [prefixWord, tailWord_6554146, baseEnd_6554146] using wordTrace_append hprefix tailTrace_6554146
  have hstable : (prefixWord ++ tailWord_6554146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554146).length < 2 ^ (prefixWord ++ tailWord_6554146).sum := by decide
  have hdescent : baseEnd_6554146 < baseStart_6554146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554183 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_6554183 : Nat := 118140960795 + 6554183 * 2 ^ 59
def prefixEnd_6554183 : Nat := 4983230072969 + 3 ^ 40 * 6554183 * 2
def baseEnd_6554183 : Nat := 3365446176527235462570367

theorem tailTrace_6554183 : CollatzResearch.WordTrace tailWord_6554183 prefixEnd_6554183 3365446176527235462570367 := by
  unfold tailWord_6554183
  simp only [CollatzResearch.WordTrace]
  refine ⟨239050692814321831184283203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159367128542881220789522135 239050692814321831184283203)
  ·
    refine ⟨358576039221482746776424805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239050692814321831184283203 358576039221482746776424805)
    ·
      refine ⟨67233007354028015020579651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358576039221482746776424805 67233007354028015020579651)
      ·
        refine ⟨100849511031042022530869477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67233007354028015020579651 100849511031042022530869477)
        ·
          refine ⟨18909283318320379224538027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100849511031042022530869477 18909283318320379224538027)
          ·
            refine ⟨28363924977480568836807041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18909283318320379224538027 28363924977480568836807041)
            ·
              refine ⟨21272943733110426627605281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28363924977480568836807041 21272943733110426627605281)
              ·
                refine ⟨15954707799832819970703961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21272943733110426627605281 15954707799832819970703961)
                ·
                  refine ⟨11966030849874614978027971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15954707799832819970703961 11966030849874614978027971)
                  ·
                    refine ⟨17949046274811922467041957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11966030849874614978027971 17949046274811922467041957)
                    ·
                      refine ⟨3365446176527235462570367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17949046274811922467041957 3365446176527235462570367)
                      ·
                        rfl

theorem cell23_6554183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_6554183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554183 prefixEnd_6554183 := by exact prefixLift 6554183
  have htrace : WordTrace (prefixWord ++ tailWord_6554183) baseStart_6554183 baseEnd_6554183 := by
    simpa [prefixWord, tailWord_6554183, baseEnd_6554183] using wordTrace_append hprefix tailTrace_6554183
  have hstable : (prefixWord ++ tailWord_6554183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554183).length < 2 ^ (prefixWord ++ tailWord_6554183).sum := by decide
  have hdescent : baseEnd_6554183 < baseStart_6554183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554300 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_6554300 : Nat := 118140960795 + 6554300 * 2 ^ 59
def prefixEnd_6554300 : Nat := 4983230072969 + 3 ^ 40 * 6554300 * 2
def baseEnd_6554300 : Nat := 1121835417921270501602443

theorem tailTrace_6554300 : CollatzResearch.WordTrace tailWord_6554300 prefixEnd_6554300 1121835417921270501602443 := by
  unfold tailWord_6554300
  simp only [CollatzResearch.WordTrace]
  refine ⟨119527480077448980083146177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159369973436598640110861569 119527480077448980083146177)
  ·
    refine ⟨89645610058086735062359633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119527480077448980083146177 89645610058086735062359633)
    ·
      refine ⟨67234207543565051296769725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89645610058086735062359633 67234207543565051296769725)
      ·
        refine ⟨25212827828836894236288647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67234207543565051296769725 25212827828836894236288647)
        ·
          refine ⟨37819241743255341354432971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25212827828836894236288647 37819241743255341354432971)
          ·
            refine ⟨56728862614883012031649457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37819241743255341354432971 56728862614883012031649457)
            ·
              refine ⟨42546646961162259023737093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56728862614883012031649457 42546646961162259023737093)
              ·
                refine ⟨7977496305217923566950705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42546646961162259023737093 7977496305217923566950705)
                ·
                  refine ⟨5983122228913442675213029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7977496305217923566950705 5983122228913442675213029)
                  ·
                    refine ⟨1121835417921270501602443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983122228913442675213029 1121835417921270501602443)
                    ·
                      rfl

theorem cell23_6554300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_6554300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554300 prefixEnd_6554300 := by exact prefixLift 6554300
  have htrace : WordTrace (prefixWord ++ tailWord_6554300) baseStart_6554300 baseEnd_6554300 := by
    simpa [prefixWord, tailWord_6554300, baseEnd_6554300] using wordTrace_append hprefix tailTrace_6554300
  have hstable : (prefixWord ++ tailWord_6554300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554300).length < 2 ^ (prefixWord ++ tailWord_6554300).sum := by decide
  have hdescent : baseEnd_6554300 < baseStart_6554300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554324 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6554324 : Nat := 118140960795 + 6554324 * 2 ^ 59
def prefixEnd_6554324 : Nat := 4983230072969 + 3 ^ 40 * 6554324 * 2
def baseEnd_6554324 : Nat := 3365518577299519410907219

theorem tailTrace_6554324 : CollatzResearch.WordTrace tailWord_6554324 prefixEnd_6554324 3365518577299519410907219 := by
  unfold tailWord_6554324
  simp only [CollatzResearch.WordTrace]
  refine ⟨119527917753405506132583013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159370557004540674843444017 119527917753405506132583013)
  ·
    refine ⟨22411484578763532399859315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119527917753405506132583013 22411484578763532399859315)
    ·
      refine ⟨33617226868145298599788973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22411484578763532399859315 33617226868145298599788973)
      ·
        refine ⟨12606460075554486974920865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33617226868145298599788973 12606460075554486974920865)
        ·
          refine ⟨9454845056665865231190649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12606460075554486974920865 9454845056665865231190649)
          ·
            refine ⟨7091133792499398923392987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454845056665865231190649 7091133792499398923392987)
            ·
              refine ⟨10636700688749098385089481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091133792499398923392987 10636700688749098385089481)
              ·
                refine ⟨7977525516561823788817111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10636700688749098385089481 7977525516561823788817111)
                ·
                  refine ⟨11966288274842735683225667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977525516561823788817111 11966288274842735683225667)
                  ·
                    refine ⟨17949432412264103524838501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11966288274842735683225667 17949432412264103524838501)
                    ·
                      refine ⟨3365518577299519410907219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17949432412264103524838501 3365518577299519410907219)
                      ·
                        rfl

theorem cell23_6554324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6554324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554324 prefixEnd_6554324 := by exact prefixLift 6554324
  have htrace : WordTrace (prefixWord ++ tailWord_6554324) baseStart_6554324 baseEnd_6554324 := by
    simpa [prefixWord, tailWord_6554324, baseEnd_6554324] using wordTrace_append hprefix tailTrace_6554324
  have hstable : (prefixWord ++ tailWord_6554324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554324).length < 2 ^ (prefixWord ++ tailWord_6554324).sum := by decide
  have hdescent : baseEnd_6554324 < baseStart_6554324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554327 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_6554327 : Nat := 118140960795 + 6554327 * 2 ^ 59
def prefixEnd_6554327 : Nat := 4983230072969 + 3 ^ 40 * 6554327 * 2
def baseEnd_6554327 : Nat := 3365520117741482899169705

theorem tailTrace_6554327 : CollatzResearch.WordTrace tailWord_6554327 prefixEnd_6554327 3365520117741482899169705 := by
  unfold tailWord_6554327
  simp only [CollatzResearch.WordTrace]
  refine ⟨239055944925800143777525235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159370629950533429185016823 239055944925800143777525235)
  ·
    refine ⟨358583917388700215666287853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239055944925800143777525235 358583917388700215666287853)
    ·
      refine ⟨134468969020762580874857945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358583917388700215666287853 134468969020762580874857945)
      ·
        refine ⟨100851726765571935656143459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134468969020762580874857945 100851726765571935656143459)
        ·
          refine ⟨151277590148357903484215189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100851726765571935656143459 151277590148357903484215189)
          ·
            refine ⟨7091137038204276725822587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151277590148357903484215189 7091137038204276725822587)
            ·
              refine ⟨10636705557306415088733881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091137038204276725822587 10636705557306415088733881)
              ·
                refine ⟨7977529167979811316550411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10636705557306415088733881 7977529167979811316550411)
                ·
                  refine ⟨11966293751969716974825617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977529167979811316550411 11966293751969716974825617)
                  ·
                    refine ⟨8974720313977287731119213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11966293751969716974825617 8974720313977287731119213)
                    ·
                      refine ⟨3365520117741482899169705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974720313977287731119213 3365520117741482899169705)
                      ·
                        rfl

theorem cell23_6554327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_6554327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554327 prefixEnd_6554327 := by exact prefixLift 6554327
  have htrace : WordTrace (prefixWord ++ tailWord_6554327) baseStart_6554327 baseEnd_6554327 := by
    simpa [prefixWord, tailWord_6554327, baseEnd_6554327] using wordTrace_append hprefix tailTrace_6554327
  have hstable : (prefixWord ++ tailWord_6554327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554327).length < 2 ^ (prefixWord ++ tailWord_6554327).sum := by decide
  have hdescent : baseEnd_6554327 < baseStart_6554327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554340 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_6554340 : Nat := 118140960795 + 6554340 * 2 ^ 59
def prefixEnd_6554340 : Nat := 4983230072969 + 3 ^ 40 * 6554340 * 2
def baseEnd_6554340 : Nat := 3365526792989991348307145

theorem tailTrace_6554340 : CollatzResearch.WordTrace tailWord_6554340 prefixEnd_6554340 3365526792989991348307145 := by
  unfold tailWord_6554340
  simp only [CollatzResearch.WordTrace]
  refine ⟨119528209537376523498874237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159370946049835364665165649 119528209537376523498874237)
  ·
    refine ⟨44823078576516196312077839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119528209537376523498874237 44823078576516196312077839)
    ·
      refine ⟨67234617864774294468116759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44823078576516196312077839 67234617864774294468116759)
      ·
        refine ⟨100851926797161441702175139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67234617864774294468116759 100851926797161441702175139)
        ·
          refine ⟨151277890195742162553262709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100851926797161441702175139 151277890195742162553262709)
          ·
            refine ⟨14182302205850827739368379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151277890195742162553262709 14182302205850827739368379)
            ·
              refine ⟨21273453308776241609052569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182302205850827739368379 21273453308776241609052569)
              ·
                refine ⟨15955089981582181206789427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21273453308776241609052569 15955089981582181206789427)
                ·
                  refine ⟨23932634972373271810184141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15955089981582181206789427 23932634972373271810184141)
                  ·
                    refine ⟨8974738114639976928819053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23932634972373271810184141 8974738114639976928819053)
                    ·
                      refine ⟨3365526792989991348307145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974738114639976928819053 3365526792989991348307145)
                      ·
                        rfl

theorem cell23_6554340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_6554340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554340 prefixEnd_6554340 := by exact prefixLift 6554340
  have htrace : WordTrace (prefixWord ++ tailWord_6554340) baseStart_6554340 baseEnd_6554340 := by
    simpa [prefixWord, tailWord_6554340, baseEnd_6554340] using wordTrace_append hprefix tailTrace_6554340
  have hstable : (prefixWord ++ tailWord_6554340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554340).length < 2 ^ (prefixWord ++ tailWord_6554340).sum := by decide
  have hdescent : baseEnd_6554340 < baseStart_6554340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554344 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6554344 : Nat := 118140960795 + 6554344 * 2 ^ 59
def prefixEnd_6554344 : Nat := 4983230072969 + 3 ^ 40 * 6554344 * 2
def baseEnd_6554344 : Nat := 3365528846912609332657127

theorem tailTrace_6554344 : CollatzResearch.WordTrace tailWord_6554344 prefixEnd_6554344 3365528846912609332657127 := by
  unfold tailWord_6554344
  simp only [CollatzResearch.WordTrace]
  refine ⟨119528282483369277840447043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159371043311159037120596057 119528282483369277840447043)
  ·
    refine ⟨179292423725053916760670565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119528282483369277840447043 179292423725053916760670565)
    ·
      refine ⟨33617329448447609392625731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179292423725053916760670565 33617329448447609392625731)
      ·
        refine ⟨50425994172671414088938597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33617329448447609392625731 50425994172671414088938597)
        ·
          refine ⟨9454873907375890141675987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50425994172671414088938597 9454873907375890141675987)
          ·
            refine ⟨14182310861063835212513981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454873907375890141675987 14182310861063835212513981)
            ·
              refine ⟨5318366572898938204692743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14182310861063835212513981 5318366572898938204692743)
              ·
                refine ⟨7977549859348407307039115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318366572898938204692743 7977549859348407307039115)
                ·
                  refine ⟨11966324789022610960558673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977549859348407307039115 11966324789022610960558673)
                  ·
                    refine ⟨8974743591766958220419005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11966324789022610960558673 8974743591766958220419005)
                    ·
                      refine ⟨3365528846912609332657127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974743591766958220419005 3365528846912609332657127)
                      ·
                        rfl

theorem cell23_6554344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6554344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554344 prefixEnd_6554344 := by exact prefixLift 6554344
  have htrace : WordTrace (prefixWord ++ tailWord_6554344) baseStart_6554344 baseEnd_6554344 := by
    simpa [prefixWord, tailWord_6554344, baseEnd_6554344] using wordTrace_append hprefix tailTrace_6554344
  have hstable : (prefixWord ++ tailWord_6554344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554344).length < 2 ^ (prefixWord ++ tailWord_6554344).sum := by decide
  have hdescent : baseEnd_6554344 < baseStart_6554344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554383 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_6554383 : Nat := 118140960795 + 6554383 * 2 ^ 59
def prefixEnd_6554383 : Nat := 4983230072969 + 3 ^ 40 * 6554383 * 2
def baseEnd_6554383 : Nat := 3365548872658134680069447

theorem tailTrace_6554383 : CollatzResearch.WordTrace tailWord_6554383 prefixEnd_6554383 3365548872658134680069447 := by
  unfold tailWord_6554383
  simp only [CollatzResearch.WordTrace]
  refine ⟨239057987413597265341563803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159371991609064843561042535 239057987413597265341563803)
  ·
    refine ⟨358586981120395898012345705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239057987413597265341563803 358586981120395898012345705)
    ·
      refine ⟨268940235840296923509259279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358586981120395898012345705 268940235840296923509259279)
      ·
        refine ⟨403410353760445385263888919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268940235840296923509259279 403410353760445385263888919)
        ·
          refine ⟨605115530640668077895833379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403410353760445385263888919 605115530640668077895833379)
          ·
            refine ⟨907673295961002116843750069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605115530640668077895833379 907673295961002116843750069)
            ·
              refine ⟨85094371496343948454101569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 907673295961002116843750069 85094371496343948454101569)
              ·
                refine ⟨63820778622257961340576177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85094371496343948454101569 63820778622257961340576177)
                ·
                  refine ⟨47865583966693471005432133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63820778622257961340576177 47865583966693471005432133)
                  ·
                    refine ⟨8974796993755025813518525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47865583966693471005432133 8974796993755025813518525)
                    ·
                      refine ⟨3365548872658134680069447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974796993755025813518525 3365548872658134680069447)
                      ·
                        rfl

theorem cell23_6554383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_6554383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554383 prefixEnd_6554383 := by exact prefixLift 6554383
  have htrace : WordTrace (prefixWord ++ tailWord_6554383) baseStart_6554383 baseEnd_6554383 := by
    simpa [prefixWord, tailWord_6554383, baseEnd_6554383] using wordTrace_append hprefix tailTrace_6554383
  have hstable : (prefixWord ++ tailWord_6554383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554383).length < 2 ^ (prefixWord ++ tailWord_6554383).sum := by decide
  have hdescent : baseEnd_6554383 < baseStart_6554383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554431 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 2, 2, 2]
def baseStart_6554431 : Nat := 118140960795 + 6554431 * 2 ^ 59
def prefixEnd_6554431 : Nat := 4983230072969 + 3 ^ 40 * 6554431 * 2
def baseEnd_6554431 : Nat := 3365573519729550492269227

theorem tailTrace_6554431 : CollatzResearch.WordTrace tailWord_6554431 prefixEnd_6554431 3365573519729550492269227 := by
  unfold tailWord_6554431
  simp only [CollatzResearch.WordTrace]
  refine ⟨239059738117423369539311147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159373158744948913026207431 239059738117423369539311147)
  ·
    refine ⟨358589607176135054308966721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239059738117423369539311147 358589607176135054308966721)
    ·
      refine ⟨268942205382101290731725041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358589607176135054308966721 268942205382101290731725041)
      ·
        refine ⟨201706654036575968048793781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268942205382101290731725041 201706654036575968048793781)
        ·
          refine ⟨18909998815928997004574417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201706654036575968048793781 18909998815928997004574417)
          ·
            refine ⟨14182499111946747753430813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18909998815928997004574417 14182499111946747753430813)
            ·
              refine ⟨5318437166980030407536555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14182499111946747753430813 5318437166980030407536555)
              ·
                refine ⟨7977655750470045611304833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318437166980030407536555 7977655750470045611304833)
                ·
                  refine ⟨5983241812852534208478625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7977655750470045611304833 5983241812852534208478625)
                  ·
                    refine ⟨4487431359639400656358969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983241812852534208478625 4487431359639400656358969)
                    ·
                      refine ⟨3365573519729550492269227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487431359639400656358969 3365573519729550492269227)
                      ·
                        rfl

theorem cell23_6554431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_6554431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554431 prefixEnd_6554431 := by exact prefixLift 6554431
  have htrace : WordTrace (prefixWord ++ tailWord_6554431) baseStart_6554431 baseEnd_6554431 := by
    simpa [prefixWord, tailWord_6554431, baseEnd_6554431] using wordTrace_append hprefix tailTrace_6554431
  have hstable : (prefixWord ++ tailWord_6554431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554431).length < 2 ^ (prefixWord ++ tailWord_6554431).sum := by decide
  have hdescent : baseEnd_6554431 < baseStart_6554431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554450 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_6554450 : Nat := 118140960795 + 6554450 * 2 ^ 59
def prefixEnd_6554450 : Nat := 4983230072969 + 3 ^ 40 * 6554450 * 2
def baseEnd_6554450 : Nat := 1121861091953995305977213

theorem tailTrace_6554450 : CollatzResearch.WordTrace tailWord_6554450 prefixEnd_6554450 1121861091953995305977213 := by
  unfold tailWord_6554450
  simp only [CollatzResearch.WordTrace]
  refine ⟨59765107776088633946063201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159373620736236357189501869 59765107776088633946063201)
  ·
    refine ⟨44823830832066475459547401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59765107776088633946063201 44823830832066475459547401)
    ·
      refine ⟨33617873124049856594660551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44823830832066475459547401 33617873124049856594660551)
      ·
        refine ⟨50426809686074784891990827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33617873124049856594660551 50426809686074784891990827)
        ·
          refine ⟨75640214529112177337986241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50426809686074784891990827 75640214529112177337986241)
          ·
            refine ⟨56730160896834133003489681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75640214529112177337986241 56730160896834133003489681)
            ·
              refine ⟨42547620672625599752617261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56730160896834133003489681 42547620672625599752617261)
              ·
                refine ⟨15955357752234599907231473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42547620672625599752617261 15955357752234599907231473)
                ·
                  refine ⟨11966518314175949930423605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15955357752234599907231473 11966518314175949930423605)
                  ·
                    refine ⟨1121861091953995305977213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11966518314175949930423605 1121861091953995305977213)
                    ·
                      rfl

theorem cell23_6554450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_6554450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554450 prefixEnd_6554450 := by exact prefixLift 6554450
  have htrace : WordTrace (prefixWord ++ tailWord_6554450) baseStart_6554450 baseEnd_6554450 := by
    simpa [prefixWord, tailWord_6554450, baseEnd_6554450] using wordTrace_append hprefix tailTrace_6554450
  have hstable : (prefixWord ++ tailWord_6554450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554450).length < 2 ^ (prefixWord ++ tailWord_6554450).sum := by decide
  have hdescent : baseEnd_6554450 < baseStart_6554450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554483 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_6554483 : Nat := 118140960795 + 6554483 * 2 ^ 59
def prefixEnd_6554483 : Nat := 4983230072969 + 3 ^ 40 * 6554483 * 2
def baseEnd_6554483 : Nat := 3365600220723584288818987

theorem tailTrace_6554483 : CollatzResearch.WordTrace tailWord_6554483 prefixEnd_6554483 3365600220723584288818987 := by
  unfold tailWord_6554483
  simp only [CollatzResearch.WordTrace]
  refine ⟨239061634713234982420204103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159374423142156654946802735 239061634713234982420204103)
  ·
    refine ⟨358592452069852473630306155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239061634713234982420204103 358592452069852473630306155)
    ·
      refine ⟨537888678104778710445459233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358592452069852473630306155 537888678104778710445459233)
      ·
        refine ⟨403416508578584032834094425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537888678104778710445459233 403416508578584032834094425)
        ·
          refine ⟨302562381433938024625570819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403416508578584032834094425 302562381433938024625570819)
          ·
            refine ⟨453843572150907036938356229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302562381433938024625570819 453843572150907036938356229)
            ·
              refine ⟨85095669778295069425941793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453843572150907036938356229 85095669778295069425941793)
              ·
                refine ⟨63821752333721302069456345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85095669778295069425941793 63821752333721302069456345)
                ·
                  refine ⟨47866314250290976552092259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63821752333721302069456345 47866314250290976552092259)
                  ·
                    refine ⟨71799471375436464828138389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47866314250290976552092259 71799471375436464828138389)
                    ·
                      refine ⟨3365600220723584288818987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71799471375436464828138389 3365600220723584288818987)
                      ·
                        rfl

theorem cell23_6554483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_6554483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554483 prefixEnd_6554483 := by exact prefixLift 6554483
  have htrace : WordTrace (prefixWord ++ tailWord_6554483) baseStart_6554483 baseEnd_6554483 := by
    simpa [prefixWord, tailWord_6554483, baseEnd_6554483] using wordTrace_append hprefix tailTrace_6554483
  have hstable : (prefixWord ++ tailWord_6554483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554483).length < 2 ^ (prefixWord ++ tailWord_6554483).sum := by decide
  have hdescent : baseEnd_6554483 < baseStart_6554483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554490 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_6554490 : Nat := 118140960795 + 6554490 * 2 ^ 59
def prefixEnd_6554490 : Nat := 4983230072969 + 3 ^ 40 * 6554490 * 2
def baseEnd_6554490 : Nat := 3365603815088165761431455

theorem tailTrace_6554490 : CollatzResearch.WordTrace tailWord_6554490 prefixEnd_6554490 3365603815088165761431455 := by
  unfold tailWord_6554490
  simp only [CollatzResearch.WordTrace]
  refine ⟨59765472506052405653927231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159374593349473081743805949 59765472506052405653927231)
  ·
    refine ⟨89648208759078608480890847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59765472506052405653927231 89648208759078608480890847)
    ·
      refine ⟨134472313138617912721336271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89648208759078608480890847 134472313138617912721336271)
      ·
        refine ⟨201708469707926869082004407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134472313138617912721336271 201708469707926869082004407)
        ·
          refine ⟨302562704561890303623006611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201708469707926869082004407 302562704561890303623006611)
          ·
            refine ⟨453844056842835455434509917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302562704561890303623006611 453844056842835455434509917)
            ·
              refine ⟨170191521316063295787941219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453844056842835455434509917 170191521316063295787941219)
              ·
                refine ⟨255287281974094943681911829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170191521316063295787941219 255287281974094943681911829)
                ·
                  refine ⟨11966591342535700485089617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255287281974094943681911829 11966591342535700485089617)
                  ·
                    refine ⟨8974943506901775363817213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11966591342535700485089617 8974943506901775363817213)
                    ·
                      refine ⟨3365603815088165761431455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8974943506901775363817213 3365603815088165761431455)
                      ·
                        rfl

theorem cell23_6554490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_6554490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554490 prefixEnd_6554490 := by exact prefixLift 6554490
  have htrace : WordTrace (prefixWord ++ tailWord_6554490) baseStart_6554490 baseEnd_6554490 := by
    simpa [prefixWord, tailWord_6554490, baseEnd_6554490] using wordTrace_append hprefix tailTrace_6554490
  have hstable : (prefixWord ++ tailWord_6554490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554490).length < 2 ^ (prefixWord ++ tailWord_6554490).sum := by decide
  have hdescent : baseEnd_6554490 < baseStart_6554490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_6554513 : Nat := 118140960795 + 6554513 * 2 ^ 59
def prefixEnd_6554513 : Nat := 4983230072969 + 3 ^ 40 * 6554513 * 2
def baseEnd_6554513 : Nat := 3365615625143219171443849

theorem tailTrace_6554513 : CollatzResearch.WordTrace tailWord_6554513 prefixEnd_6554513 3365615625143219171443849 := by
  unfold tailWord_6554513
  simp only [CollatzResearch.WordTrace]
  refine ⟨239062728903126297543796193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159375152602084198362530795 239062728903126297543796193)
  ·
    refine ⟨179297046677344723157847145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239062728903126297543796193 179297046677344723157847145)
    ·
      refine ⟨134472785008008542368385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179297046677344723157847145 134472785008008542368385359)
      ·
        refine ⟨201709177512012813552578039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134472785008008542368385359 201709177512012813552578039)
        ·
          refine ⟨302563766268019220328867059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201709177512012813552578039 302563766268019220328867059)
          ·
            refine ⟨453845649402028830493300589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302563766268019220328867059 453845649402028830493300589)
            ·
              refine ⟨170192118525760811434987721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453845649402028830493300589 170192118525760811434987721)
              ·
                refine ⟨127644088894320608576240791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170192118525760811434987721 127644088894320608576240791)
                ·
                  refine ⟨191466133341480912864361187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127644088894320608576240791 191466133341480912864361187)
                  ·
                    refine ⟨287199200012221369296541781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191466133341480912864361187 287199200012221369296541781)
                    ·
                      refine ⟨3365615625143219171443849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287199200012221369296541781 3365615625143219171443849)
                      ·
                        rfl

theorem cell23_6554513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_6554513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554513 prefixEnd_6554513 := by exact prefixLift 6554513
  have htrace : WordTrace (prefixWord ++ tailWord_6554513) baseStart_6554513 baseEnd_6554513 := by
    simpa [prefixWord, tailWord_6554513, baseEnd_6554513] using wordTrace_append hprefix tailTrace_6554513
  have hstable : (prefixWord ++ tailWord_6554513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554513).length < 2 ^ (prefixWord ++ tailWord_6554513).sum := by decide
  have hdescent : baseEnd_6554513 < baseStart_6554513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554527 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 6]
def baseStart_6554527 : Nat := 118140960795 + 6554527 * 2 ^ 59
def prefixEnd_6554527 : Nat := 4983230072969 + 3 ^ 40 * 6554527 * 2
def baseEnd_6554527 : Nat := 373958090430264679629865

theorem tailTrace_6554527 : CollatzResearch.WordTrace tailWord_6554527 prefixEnd_6554527 373958090430264679629865 := by
  unfold tailWord_6554527
  simp only [CollatzResearch.WordTrace]
  refine ⟨239063239525075577934805835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159375493016717051956537223 239063239525075577934805835)
  ·
    refine ⟨358594859287613366902208753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239063239525075577934805835 358594859287613366902208753)
    ·
      refine ⟨268946144465710025176656565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358594859287613366902208753 268946144465710025176656565)
      ·
        refine ⟨25213701043660314860311553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268946144465710025176656565 25213701043660314860311553)
        ·
          refine ⟨18910275782745236145233665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25213701043660314860311553 18910275782745236145233665)
          ·
            refine ⟨14182706837058927108925249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18910275782745236145233665 14182706837058927108925249)
            ·
              refine ⟨10637030127794195331693937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14182706837058927108925249 10637030127794195331693937)
              ·
                refine ⟨7977772595845646498770453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637030127794195331693937 7977772595845646498770453)
                ·
                  refine ⟨373958090430264679629865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7977772595845646498770453 373958090430264679629865)
                  ·
                    rfl

theorem cell23_6554527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 6].length) (baseStart_6554527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554527 prefixEnd_6554527 := by exact prefixLift 6554527
  have htrace : WordTrace (prefixWord ++ tailWord_6554527) baseStart_6554527 baseEnd_6554527 := by
    simpa [prefixWord, tailWord_6554527, baseEnd_6554527] using wordTrace_append hprefix tailTrace_6554527
  have hstable : (prefixWord ++ tailWord_6554527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554527).length < 2 ^ (prefixWord ++ tailWord_6554527).sum := by decide
  have hdescent : baseEnd_6554527 < baseStart_6554527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554537 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 3]
def baseStart_6554537 : Nat := 118140960795 + 6554537 * 2 ^ 59
def prefixEnd_6554537 : Nat := 4983230072969 + 3 ^ 40 * 6554537 * 2
def baseEnd_6554537 : Nat := 3365627948678927077543739

theorem tailTrace_6554537 : CollatzResearch.WordTrace tailWord_6554537 prefixEnd_6554537 3365627948678927077543739 := by
  unfold tailWord_6554537
  simp only [CollatzResearch.WordTrace]
  refine ⟨239063604255039349642669865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159375736170026233095113243 239063604255039349642669865)
  ·
    refine ⟨179297703191279512232002399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239063604255039349642669865 179297703191279512232002399)
    ·
      refine ⟨268946554786919268348003599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179297703191279512232002399 268946554786919268348003599)
      ·
        refine ⟨403419832180378902522005399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268946554786919268348003599 403419832180378902522005399)
        ·
          refine ⟨605129748270568353783008099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403419832180378902522005399 605129748270568353783008099)
          ·
            refine ⟨907694622405852530674512149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605129748270568353783008099 907694622405852530674512149)
            ·
              refine ⟨42548185425274337375367757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 907694622405852530674512149 42548185425274337375367757)
              ·
                refine ⟨15955569534477876515762909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42548185425274337375367757 15955569534477876515762909)
                ·
                  refine ⟨5983338575429203693411091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15955569534477876515762909 5983338575429203693411091)
                  ·
                    refine ⟨8975007863143805540116637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983338575429203693411091 8975007863143805540116637)
                    ·
                      refine ⟨3365627948678927077543739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975007863143805540116637 3365627948678927077543739)
                      ·
                        rfl

theorem cell23_6554537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 3].length) (baseStart_6554537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554537 prefixEnd_6554537 := by exact prefixLift 6554537
  have htrace : WordTrace (prefixWord ++ tailWord_6554537) baseStart_6554537 baseEnd_6554537 := by
    simpa [prefixWord, tailWord_6554537, baseEnd_6554537] using wordTrace_append hprefix tailTrace_6554537
  have hstable : (prefixWord ++ tailWord_6554537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554537).length < 2 ^ (prefixWord ++ tailWord_6554537).sum := by decide
  have hdescent : baseEnd_6554537 < baseStart_6554537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554571 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 1, 1, 3]
def baseStart_6554571 : Nat := 118140960795 + 6554571 * 2 ^ 59
def prefixEnd_6554571 : Nat := 4983230072969 + 3 ^ 40 * 6554571 * 2
def baseEnd_6554571 : Nat := 3365645407021179944518583

theorem tailTrace_6554571 : CollatzResearch.WordTrace tailWord_6554571 prefixEnd_6554571 3365645407021179944518583 := by
  unfold tailWord_6554571
  simp only [CollatzResearch.WordTrace]
  refine ⟨239064844336916173449407567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159376562891277448966271711 239064844336916173449407567)
  ·
    refine ⟨358597266505374260174111351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239064844336916173449407567 358597266505374260174111351)
    ·
      refine ⟨537895899758061390261167027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358597266505374260174111351 537895899758061390261167027)
      ·
        refine ⟨806843849637092085391750541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537895899758061390261167027 806843849637092085391750541)
        ·
          refine ⟨302566443613909532021906453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806843849637092085391750541 302566443613909532021906453)
          ·
            refine ⟨14182802044402009313526865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 302566443613909532021906453 14182802044402009313526865)
            ·
              refine ⟨10637101533301506985145149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14182802044402009313526865 10637101533301506985145149)
              ·
                refine ⟨3988913074988065119429431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10637101533301506985145149 3988913074988065119429431)
                ·
                  refine ⟨5983369612482097679144147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988913074988065119429431 5983369612482097679144147)
                  ·
                    refine ⟨8975054418723146518716221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983369612482097679144147 8975054418723146518716221)
                    ·
                      refine ⟨3365645407021179944518583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975054418723146518716221 3365645407021179944518583)
                      ·
                        rfl

theorem cell23_6554571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 1, 3].length) (baseStart_6554571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554571 prefixEnd_6554571 := by exact prefixLift 6554571
  have htrace : WordTrace (prefixWord ++ tailWord_6554571) baseStart_6554571 baseEnd_6554571 := by
    simpa [prefixWord, tailWord_6554571, baseEnd_6554571] using wordTrace_append hprefix tailTrace_6554571
  have hstable : (prefixWord ++ tailWord_6554571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554571).length < 2 ^ (prefixWord ++ tailWord_6554571).sum := by decide
  have hdescent : baseEnd_6554571 < baseStart_6554571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554574 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_6554574 : Nat := 118140960795 + 6554574 * 2 ^ 59
def prefixEnd_6554574 : Nat := 4983230072969 + 3 ^ 40 * 6554574 * 2
def baseEnd_6554574 : Nat := 1121882315821047810927023

theorem tailTrace_6554574 : CollatzResearch.WordTrace tailWord_6554574 prefixEnd_6554574 1121882315821047810927023 := by
  unfold tailWord_6554574
  simp only [CollatzResearch.WordTrace]
  refine ⟨29883119219488163120220847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159376635837270203307844517 29883119219488163120220847)
  ·
    refine ⟨44824678829232244680331271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29883119219488163120220847 44824678829232244680331271)
    ·
      refine ⟨67237018243848367020496907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44824678829232244680331271 67237018243848367020496907)
      ·
        refine ⟨100855527365772550530745361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67237018243848367020496907 100855527365772550530745361)
        ·
          refine ⟨75641645524329412898059021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100855527365772550530745361 75641645524329412898059021)
          ·
            refine ⟨28365617071623529836772133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75641645524329412898059021 28365617071623529836772133)
            ·
              refine ⟨5318553200929411844394775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28365617071623529836772133 5318553200929411844394775)
              ·
                refine ⟨7977829801394117766592163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318553200929411844394775 7977829801394117766592163)
                ·
                  refine ⟨11966744702091176649888245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977829801394117766592163 11966744702091176649888245)
                  ·
                    refine ⟨1121882315821047810927023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11966744702091176649888245 1121882315821047810927023)
                    ·
                      rfl

theorem cell23_6554574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_6554574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554574 prefixEnd_6554574 := by exact prefixLift 6554574
  have htrace : WordTrace (prefixWord ++ tailWord_6554574) baseStart_6554574 baseEnd_6554574 := by
    simpa [prefixWord, tailWord_6554574, baseEnd_6554574] using wordTrace_append hprefix tailTrace_6554574
  have hstable : (prefixWord ++ tailWord_6554574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554574).length < 2 ^ (prefixWord ++ tailWord_6554574).sum := by decide
  have hdescent : baseEnd_6554574 < baseStart_6554574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554577 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_6554577 : Nat := 118140960795 + 6554577 * 2 ^ 59
def prefixEnd_6554577 : Nat := 4983230072969 + 3 ^ 40 * 6554577 * 2
def baseEnd_6554577 : Nat := 3365648487905106921043555

theorem tailTrace_6554577 : CollatzResearch.WordTrace tailWord_6554577 prefixEnd_6554577 3365648487905106921043555 := by
  unfold tailWord_6554577
  simp only [CollatzResearch.WordTrace]
  refine ⟨239065063174894436474125985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159376708783262957649417323 239065063174894436474125985)
  ·
    refine ⟨179298797381170827355594489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239065063174894436474125985 179298797381170827355594489)
    ·
      refine ⟨134474098035878120516695867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179298797381170827355594489 134474098035878120516695867)
      ·
        refine ⟨201711147053817180775043801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134474098035878120516695867 201711147053817180775043801)
        ·
          refine ⟨151283360290362885581282851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201711147053817180775043801 151283360290362885581282851)
          ·
            refine ⟨226925040435544328371924277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151283360290362885581282851 226925040435544328371924277)
            ·
              refine ⟨21274222540832280784867901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226925040435544328371924277 21274222540832280784867901)
              ·
                refine ⟨7977833452812105294325463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21274222540832280784867901 7977833452812105294325463)
                ·
                  refine ⟨11966750179218157941488195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7977833452812105294325463 11966750179218157941488195)
                  ·
                    refine ⟨17950125268827236912232293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11966750179218157941488195 17950125268827236912232293)
                    ·
                      refine ⟨3365648487905106921043555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17950125268827236912232293 3365648487905106921043555)
                      ·
                        rfl

theorem cell23_6554577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_6554577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554577 prefixEnd_6554577 := by exact prefixLift 6554577
  have htrace : WordTrace (prefixWord ++ tailWord_6554577) baseStart_6554577 baseEnd_6554577 := by
    simpa [prefixWord, tailWord_6554577, baseEnd_6554577] using wordTrace_append hprefix tailTrace_6554577
  have hstable : (prefixWord ++ tailWord_6554577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554577).length < 2 ^ (prefixWord ++ tailWord_6554577).sum := by decide
  have hdescent : baseEnd_6554577 < baseStart_6554577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554607 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_6554607 : Nat := 118140960795 + 6554607 * 2 ^ 59
def prefixEnd_6554607 : Nat := 4983230072969 + 3 ^ 40 * 6554607 * 2
def baseEnd_6554607 : Nat := 3365663892324741803668417

theorem tailTrace_6554607 : CollatzResearch.WordTrace tailWord_6554607 prefixEnd_6554607 3365663892324741803668417 := by
  unfold tailWord_6554607
  simp only [CollatzResearch.WordTrace]
  refine ⟨239066157364785751597718075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159377438243190501065145383 239066157364785751597718075)
  ·
    refine ⟨358599236047178627396577113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239066157364785751597718075 358599236047178627396577113)
    ·
      refine ⟨268949427035383970547432835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358599236047178627396577113 268949427035383970547432835)
      ·
        refine ⟨403424140553075955821149253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268949427035383970547432835 403424140553075955821149253)
        ·
          refine ⟨75642026353701741716465485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403424140553075955821149253 75642026353701741716465485)
          ·
            refine ⟨28365759882638153143674557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75642026353701741716465485 28365759882638153143674557)
            ·
              refine ⟨10637159955989307428877959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28365759882638153143674557 10637159955989307428877959)
              ·
                refine ⟨15955739933983961143316939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10637159955989307428877959 15955739933983961143316939)
                ·
                  refine ⟨23933609900975941714975409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15955739933983961143316939 23933609900975941714975409)
                  ·
                    refine ⟨17950207425731956286231557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23933609900975941714975409 17950207425731956286231557)
                    ·
                      refine ⟨3365663892324741803668417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17950207425731956286231557 3365663892324741803668417)
                      ·
                        rfl

theorem cell23_6554607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_6554607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554607 prefixEnd_6554607 := by exact prefixLift 6554607
  have htrace : WordTrace (prefixWord ++ tailWord_6554607) baseStart_6554607 baseEnd_6554607 := by
    simpa [prefixWord, tailWord_6554607, baseEnd_6554607] using wordTrace_append hprefix tailTrace_6554607
  have hstable : (prefixWord ++ tailWord_6554607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554607).length < 2 ^ (prefixWord ++ tailWord_6554607).sum := by decide
  have hdescent : baseEnd_6554607 < baseStart_6554607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554622 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6554622 : Nat := 118140960795 + 6554622 * 2 ^ 59
def prefixEnd_6554622 : Nat := 4983230072969 + 3 ^ 40 * 6554622 * 2
def baseEnd_6554622 : Nat := 3365671594534559244980849

theorem tailTrace_6554622 : CollatzResearch.WordTrace tailWord_6554622 prefixEnd_6554622 3365671594534559244980849 := by
  unfold tailWord_6554622
  simp only [CollatzResearch.WordTrace]
  refine ⟨29883338057466426144939265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159377802973154272773009413 29883338057466426144939265)
  ·
    refine ⟨22412503543099819608704449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29883338057466426144939265 22412503543099819608704449)
    ·
      refine ⟨16809377657324864706528337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22412503543099819608704449 16809377657324864706528337)
      ·
        refine ⟨12607033242993648529896253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16809377657324864706528337 12607033242993648529896253)
        ·
          refine ⟨4727637466122618198711095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12607033242993648529896253 4727637466122618198711095)
          ·
            refine ⟨7091456199183927298066643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727637466122618198711095 7091456199183927298066643)
            ·
              refine ⟨10637184298775890947099965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091456199183927298066643 10637184298775890947099965)
              ·
                refine ⟨3988944112040959105162487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10637184298775890947099965 3988944112040959105162487)
                ·
                  refine ⟨5983416168061438657743731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988944112040959105162487 5983416168061438657743731)
                  ·
                    refine ⟨8975124252092157986615597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983416168061438657743731 8975124252092157986615597)
                    ·
                      refine ⟨3365671594534559244980849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975124252092157986615597 3365671594534559244980849)
                      ·
                        rfl

theorem cell23_6554622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6554622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554622 prefixEnd_6554622 := by exact prefixLift 6554622
  have htrace : WordTrace (prefixWord ++ tailWord_6554622) baseStart_6554622 baseEnd_6554622 := by
    simpa [prefixWord, tailWord_6554622, baseEnd_6554622] using wordTrace_append hprefix tailTrace_6554622
  have hstable : (prefixWord ++ tailWord_6554622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554622).length < 2 ^ (prefixWord ++ tailWord_6554622).sum := by decide
  have hdescent : baseEnd_6554622 < baseStart_6554622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554645 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_6554645 : Nat := 118140960795 + 6554645 * 2 ^ 59
def prefixEnd_6554645 : Nat := 4983230072969 + 3 ^ 40 * 6554645 * 2
def baseEnd_6554645 : Nat := 3365683404589612654993243

theorem tailTrace_6554645 : CollatzResearch.WordTrace tailWord_6554645 prefixEnd_6554645 3365683404589612654993243 := by
  unfold tailWord_6554645
  simp only [CollatzResearch.WordTrace]
  refine ⟨239067543338648084087601389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159378362225765389391734259 239067543338648084087601389)
  ·
    refine ⟨89650328751993031532850521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239067543338648084087601389 89650328751993031532850521)
    ·
      refine ⟨67237746563994773649637891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89650328751993031532850521 67237746563994773649637891)
      ·
        refine ⟨100856619845992160474456837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67237746563994773649637891 100856619845992160474456837)
        ·
          refine ⟨18910616221123530088960657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100856619845992160474456837 18910616221123530088960657)
          ·
            refine ⟨14182962165842647566720493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18910616221123530088960657 14182962165842647566720493)
            ·
              refine ⟨5318610812190992837520185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14182962165842647566720493 5318610812190992837520185)
              ·
                refine ⟨3988958109143244628140139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318610812190992837520185 3988958109143244628140139)
                ·
                  refine ⟨5983437163714866942210209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988958109143244628140139 5983437163714866942210209)
                  ·
                    refine ⟨4487577872786150206657657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983437163714866942210209 4487577872786150206657657)
                    ·
                      refine ⟨3365683404589612654993243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487577872786150206657657 3365683404589612654993243)
                      ·
                        rfl

theorem cell23_6554645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_6554645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554645 prefixEnd_6554645 := by exact prefixLift 6554645
  have htrace : WordTrace (prefixWord ++ tailWord_6554645) baseStart_6554645 baseEnd_6554645 := by
    simpa [prefixWord, tailWord_6554645, baseEnd_6554645] using wordTrace_append hprefix tailTrace_6554645
  have hstable : (prefixWord ++ tailWord_6554645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554645).length < 2 ^ (prefixWord ++ tailWord_6554645).sum := by decide
  have hdescent : baseEnd_6554645 < baseStart_6554645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554684 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_6554684 : Nat := 118140960795 + 6554684 * 2 ^ 59
def prefixEnd_6554684 : Nat := 4983230072969 + 3 ^ 40 * 6554684 * 2
def baseEnd_6554684 : Nat := 3365703430335138002405563

theorem tailTrace_6554684 : CollatzResearch.WordTrace tailWord_6554684 prefixEnd_6554684 3365703430335138002405563 := by
  unfold tailWord_6554684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119534482892753396874135553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159379310523671195832180737 119534482892753396874135553)
  ·
    refine ⟨89650862169565047655601665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119534482892753396874135553 89650862169565047655601665)
    ·
      refine ⟨67238146627173785741701249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89650862169565047655601665 67238146627173785741701249)
      ·
        refine ⟨50428609970380339306275937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67238146627173785741701249 50428609970380339306275937)
        ·
          refine ⟨37821457477785254479706953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50428609970380339306275937 37821457477785254479706953)
          ·
            refine ⟨28366093108338940859780215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37821457477785254479706953 28366093108338940859780215)
            ·
              refine ⟨42549139662508411289670323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28366093108338940859780215 42549139662508411289670323)
              ·
                refine ⟨63823709493762616934505485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42549139662508411289670323 63823709493762616934505485)
                ·
                  refine ⟨23933891060160981350439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63823709493762616934505485 23933891060160981350439557)
                  ·
                    refine ⟨4487604573780184003207417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23933891060160981350439557 4487604573780184003207417)
                    ·
                      refine ⟨3365703430335138002405563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487604573780184003207417 3365703430335138002405563)
                      ·
                        rfl

theorem cell23_6554684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_6554684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554684 prefixEnd_6554684 := by exact prefixLift 6554684
  have htrace : WordTrace (prefixWord ++ tailWord_6554684) baseStart_6554684 baseEnd_6554684 := by
    simpa [prefixWord, tailWord_6554684, baseEnd_6554684] using wordTrace_append hprefix tailTrace_6554684
  have hstable : (prefixWord ++ tailWord_6554684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554684).length < 2 ^ (prefixWord ++ tailWord_6554684).sum := by decide
  have hdescent : baseEnd_6554684 < baseStart_6554684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554737 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_6554737 : Nat := 118140960795 + 6554737 * 2 ^ 59
def prefixEnd_6554737 : Nat := 4983230072969 + 3 ^ 40 * 6554737 * 2
def baseEnd_6554737 : Nat := 1121910214936608765014273

theorem tailTrace_6554737 : CollatzResearch.WordTrace tailWord_6554737 prefixEnd_6554737 1121910214936608765014273 := by
  unfold tailWord_6554737
  simp only [CollatzResearch.WordTrace]
  refine ⟨239070898854314783799950465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159380599236209855866633643 239070898854314783799950465)
  ·
    refine ⟨179303174140736087849962849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239070898854314783799950465 179303174140736087849962849)
    ·
      refine ⟨134477380605552065887472137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179303174140736087849962849 134477380605552065887472137)
      ·
        refine ⟨100858035454164049415604103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134477380605552065887472137 100858035454164049415604103)
        ·
          refine ⟨151287053181246074123406155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100858035454164049415604103 151287053181246074123406155)
          ·
            refine ⟨226930579771869111185109233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151287053181246074123406155 226930579771869111185109233)
            ·
              refine ⟨170197934828901833388831925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226930579771869111185109233 170197934828901833388831925)
              ·
                refine ⟨15956056390209546880202993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170197934828901833388831925 15956056390209546880202993)
                ·
                  refine ⟨11967042292657160160152245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15956056390209546880202993 11967042292657160160152245)
                  ·
                    refine ⟨1121910214936608765014273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11967042292657160160152245 1121910214936608765014273)
                    ·
                      rfl

theorem cell23_6554737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_6554737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554737 prefixEnd_6554737 := by exact prefixLift 6554737
  have htrace : WordTrace (prefixWord ++ tailWord_6554737) baseStart_6554737 baseEnd_6554737 := by
    simpa [prefixWord, tailWord_6554737, baseEnd_6554737] using wordTrace_append hprefix tailTrace_6554737
  have hstable : (prefixWord ++ tailWord_6554737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554737).length < 2 ^ (prefixWord ++ tailWord_6554737).sum := by decide
  have hdescent : baseEnd_6554737 < baseStart_6554737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554784 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_6554784 : Nat := 118140960795 + 6554784 * 2 ^ 59
def prefixEnd_6554784 : Nat := 4983230072969 + 3 ^ 40 * 6554784 * 2
def baseEnd_6554784 : Nat := 1121918259466862537051701

theorem tailTrace_6554784 : CollatzResearch.WordTrace tailWord_6554784 prefixEnd_6554784 1121918259466862537051701 := by
  unfold tailWord_6554784
  simp only [CollatzResearch.WordTrace]
  refine ⟨119536306542572255413455703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159381742056763007217940937 119536306542572255413455703)
  ·
    refine ⟨179304459813858383120183555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119536306542572255413455703 179304459813858383120183555)
    ·
      refine ⟨268956689720787574680275333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179304459813858383120183555 268956689720787574680275333)
      ·
        refine ⟨50429379322647670252551625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268956689720787574680275333 50429379322647670252551625)
        ·
          refine ⟨37822034491985752689413719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50429379322647670252551625 37822034491985752689413719)
          ·
            refine ⟨56733051737978629034120579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37822034491985752689413719 56733051737978629034120579)
            ·
              refine ⟨85099577606967943551180869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56733051737978629034120579 85099577606967943551180869)
              ·
                refine ⟨15956170801306489415846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85099577606967943551180869 15956170801306489415846413)
                ·
                  refine ⟨5983564050489933530942405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15956170801306489415846413 5983564050489933530942405)
                  ·
                    refine ⟨1121918259466862537051701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983564050489933530942405 1121918259466862537051701)
                    ·
                      rfl

theorem cell23_6554784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_6554784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554784 prefixEnd_6554784 := by exact prefixLift 6554784
  have htrace : WordTrace (prefixWord ++ tailWord_6554784) baseStart_6554784 baseEnd_6554784 := by
    simpa [prefixWord, tailWord_6554784, baseEnd_6554784] using wordTrace_append hprefix tailTrace_6554784
  have hstable : (prefixWord ++ tailWord_6554784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554784).length < 2 ^ (prefixWord ++ tailWord_6554784).sum := by decide
  have hdescent : baseEnd_6554784 < baseStart_6554784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554814 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_6554814 : Nat := 118140960795 + 6554814 * 2 ^ 59
def prefixEnd_6554814 : Nat := 4983230072969 + 3 ^ 40 * 6554814 * 2
def baseEnd_6554814 : Nat := 373974464757802499308885

theorem tailTrace_6554814 : CollatzResearch.WordTrace tailWord_6554814 prefixEnd_6554814 373974464757802499308885 := by
  unfold tailWord_6554814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29884213409379478243812937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159382471516690550633668997 29884213409379478243812937)
  ·
    refine ⟨22413160057034608682859703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29884213409379478243812937 22413160057034608682859703)
    ·
      refine ⟨33619740085551913024289555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22413160057034608682859703 33619740085551913024289555)
      ·
        refine ⟨50429610128327869536434333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33619740085551913024289555 50429610128327869536434333)
        ·
          refine ⟨18911103798122951076162875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50429610128327869536434333 18911103798122951076162875)
          ·
            refine ⟨28366655697184426614244313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18911103798122951076162875 28366655697184426614244313)
            ·
              refine ⟨21274991772888319960683235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28366655697184426614244313 21274991772888319960683235)
              ·
                refine ⟨31912487659332479941024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21274991772888319960683235 31912487659332479941024853)
                ·
                  refine ⟨373974464757802499308885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31912487659332479941024853 373974464757802499308885)
                  ·
                    rfl

theorem cell23_6554814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_6554814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554814 prefixEnd_6554814 := by exact prefixLift 6554814
  have htrace : WordTrace (prefixWord ++ tailWord_6554814) baseStart_6554814 baseEnd_6554814 := by
    simpa [prefixWord, tailWord_6554814, baseEnd_6554814] using wordTrace_append hprefix tailTrace_6554814
  have hstable : (prefixWord ++ tailWord_6554814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554814).length < 2 ^ (prefixWord ++ tailWord_6554814).sum := by decide
  have hdescent : baseEnd_6554814 < baseStart_6554814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554891 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 2, 4]
def baseStart_6554891 : Nat := 118140960795 + 6554891 * 2 ^ 59
def prefixEnd_6554891 : Nat := 4983230072969 + 3 ^ 40 * 6554891 * 2
def baseEnd_6554891 : Nat := 1121936573610206230839037

theorem tailTrace_6554891 : CollatzResearch.WordTrace tailWord_6554891 prefixEnd_6554891 1121936573610206230839037 := by
  unfold tailWord_6554891
  simp only [CollatzResearch.WordTrace]
  refine ⟨239076515695756868101056527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159384343797171245400704351 239076515695756868101056527)
  ·
    refine ⟨358614773543635302151584791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239076515695756868101056527 358614773543635302151584791)
    ·
      refine ⟨537922160315452953227377187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358614773543635302151584791 537922160315452953227377187)
      ·
        refine ⟨806883240473179429841065781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537922160315452953227377187 806883240473179429841065781)
        ·
          refine ⟨75645303794360571547599917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 806883240473179429841065781 75645303794360571547599917)
          ·
            refine ⟨28366988922885214330349969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75645303794360571547599917 28366988922885214330349969)
            ·
              refine ⟨21275241692163910747762477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28366988922885214330349969 21275241692163910747762477)
              ·
                refine ⟨7978215634561466530410929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21275241692163910747762477 7978215634561466530410929)
                ·
                  refine ⟨5983661725921099897808197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978215634561466530410929 5983661725921099897808197)
                  ·
                    refine ⟨1121936573610206230839037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983661725921099897808197 1121936573610206230839037)
                    ·
                      rfl

theorem cell23_6554891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 4].length) (baseStart_6554891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554891 prefixEnd_6554891 := by exact prefixLift 6554891
  have htrace : WordTrace (prefixWord ++ tailWord_6554891) baseStart_6554891 baseEnd_6554891 := by
    simpa [prefixWord, tailWord_6554891, baseEnd_6554891] using wordTrace_append hprefix tailTrace_6554891
  have hstable : (prefixWord ++ tailWord_6554891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554891).length < 2 ^ (prefixWord ++ tailWord_6554891).sum := by decide
  have hdescent : baseEnd_6554891 < baseStart_6554891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554901 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_6554901 : Nat := 118140960795 + 6554901 * 2 ^ 59
def prefixEnd_6554901 : Nat := 4983230072969 + 3 ^ 40 * 6554901 * 2
def baseEnd_6554901 : Nat := 3365814855637163653392065

theorem tailTrace_6554901 : CollatzResearch.WordTrace tailWord_6554901 prefixEnd_6554901 3365814855637163653392065 := by
  unfold tailWord_6554901
  simp only [CollatzResearch.WordTrace]
  refine ⟨239076880425720639808920557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159384586950480426539280371 239076880425720639808920557)
  ·
    refine ⟨89653830159645239928345209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239076880425720639808920557 89653830159645239928345209)
    ·
      refine ⟨67240372619733929946258907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89653830159645239928345209 67240372619733929946258907)
      ·
        refine ⟨100860558929600894919388361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67240372619733929946258907 100860558929600894919388361)
        ·
          refine ⟨75645419197200671189541271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100860558929600894919388361 75645419197200671189541271)
          ·
            refine ⟨113468128795801006784311907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75645419197200671189541271 113468128795801006784311907)
            ·
              refine ⟨170202193193701510176467861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113468128795801006784311907 170202193193701510176467861)
              ·
                refine ⟨7978227805954758289521931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170202193193701510176467861 7978227805954758289521931)
                ·
                  refine ⟨11967341708932137434282897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978227805954758289521931 11967341708932137434282897)
                  ·
                    refine ⟨8975506281699103075712173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11967341708932137434282897 8975506281699103075712173)
                    ·
                      refine ⟨3365814855637163653392065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975506281699103075712173 3365814855637163653392065)
                      ·
                        rfl

theorem cell23_6554901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_6554901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554901 prefixEnd_6554901 := by exact prefixLift 6554901
  have htrace : WordTrace (prefixWord ++ tailWord_6554901) baseStart_6554901 baseEnd_6554901 := by
    simpa [prefixWord, tailWord_6554901, baseEnd_6554901] using wordTrace_append hprefix tailTrace_6554901
  have hstable : (prefixWord ++ tailWord_6554901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554901).length < 2 ^ (prefixWord ++ tailWord_6554901).sum := by decide
  have hdescent : baseEnd_6554901 < baseStart_6554901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554915 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 1, 2, 2]
def baseStart_6554915 : Nat := 118140960795 + 6554915 * 2 ^ 59
def prefixEnd_6554915 : Nat := 4983230072969 + 3 ^ 40 * 6554915 * 2
def baseEnd_6554915 : Nat := 3365822044366326598617001

theorem tailTrace_6554915 : CollatzResearch.WordTrace tailWord_6554915 prefixEnd_6554915 3365822044366326598617001 := by
  unfold tailWord_6554915
  simp only [CollatzResearch.WordTrace]
  refine ⟨239077391047669920199930199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159384927365113280133286799 239077391047669920199930199)
  ·
    refine ⟨358616086571504880299895299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239077391047669920199930199 358616086571504880299895299)
    ·
      refine ⟨537924129857257320449842949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358616086571504880299895299 537924129857257320449842949)
      ·
        refine ⟨100860774348235747584345553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537924129857257320449842949 100860774348235747584345553)
        ·
          refine ⟨75645580761176810688259165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100860774348235747584345553 75645580761176810688259165)
          ·
            refine ⟨28367092785441304008097187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75645580761176810688259165 28367092785441304008097187)
            ·
              refine ⟨42550639178161956012145781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28367092785441304008097187 42550639178161956012145781)
              ·
                refine ⟨3989122422952683376138667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42550639178161956012145781 3989122422952683376138667)
                ·
                  refine ⟨5983683634429025064208001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989122422952683376138667 5983683634429025064208001)
                  ·
                    refine ⟨4487762725821768798156001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983683634429025064208001 4487762725821768798156001)
                    ·
                      refine ⟨3365822044366326598617001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487762725821768798156001 3365822044366326598617001)
                      ·
                        rfl

theorem cell23_6554915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_6554915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554915 prefixEnd_6554915 := by exact prefixLift 6554915
  have htrace : WordTrace (prefixWord ++ tailWord_6554915) baseStart_6554915 baseEnd_6554915 := by
    simpa [prefixWord, tailWord_6554915, baseEnd_6554915] using wordTrace_append hprefix tailTrace_6554915
  have hstable : (prefixWord ++ tailWord_6554915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554915).length < 2 ^ (prefixWord ++ tailWord_6554915).sum := by decide
  have hdescent : baseEnd_6554915 < baseStart_6554915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554925 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6554925 : Nat := 118140960795 + 6554925 * 2 ^ 59
def prefixEnd_6554925 : Nat := 4983230072969 + 3 ^ 40 * 6554925 * 2
def baseEnd_6554925 : Nat := 1121942393057623853163985

theorem tailTrace_6554925 : CollatzResearch.WordTrace tailWord_6554925 prefixEnd_6554925 1121942393057623853163985 := by
  unfold tailWord_6554925
  simp only [CollatzResearch.WordTrace]
  refine ⟨239077755777633691907794229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159385170518422461271862819 239077755777633691907794229)
  ·
    refine ⟨22413539604153158616355709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239077755777633691907794229 22413539604153158616355709)
    ·
      refine ⟨8405077351557434481133391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22413539604153158616355709 8405077351557434481133391)
      ·
        refine ⟨12607616027336151721700087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405077351557434481133391 12607616027336151721700087)
        ·
          refine ⟨18911424041004227582550131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12607616027336151721700087 18911424041004227582550131)
          ·
            refine ⟨28367136061506341373825197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18911424041004227582550131 28367136061506341373825197)
            ·
              refine ⟨10637676023064878015184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28367136061506341373825197 10637676023064878015184449)
              ·
                refine ⟨7978257017298658511388337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637676023064878015184449 7978257017298658511388337)
                ·
                  refine ⟨5983692762973993883541253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978257017298658511388337 5983692762973993883541253)
                  ·
                    refine ⟨1121942393057623853163985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983692762973993883541253 1121942393057623853163985)
                    ·
                      rfl

theorem cell23_6554925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6554925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554925 prefixEnd_6554925 := by exact prefixLift 6554925
  have htrace : WordTrace (prefixWord ++ tailWord_6554925) baseStart_6554925 baseEnd_6554925 := by
    simpa [prefixWord, tailWord_6554925, baseEnd_6554925] using wordTrace_append hprefix tailTrace_6554925
  have hstable : (prefixWord ++ tailWord_6554925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554925).length < 2 ^ (prefixWord ++ tailWord_6554925).sum := by decide
  have hdescent : baseEnd_6554925 < baseStart_6554925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554932 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6554932 : Nat := 118140960795 + 6554932 * 2 ^ 59
def prefixEnd_6554932 : Nat := 4983230072969 + 3 ^ 40 * 6554932 * 2
def baseEnd_6554932 : Nat := 3365830773537453032104423

theorem tailTrace_6554932 : CollatzResearch.WordTrace tailWord_6554932 prefixEnd_6554932 3365830773537453032104423 := by
  unfold tailWord_6554932
  simp only [CollatzResearch.WordTrace]
  refine ⟨119539005544304166051649525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159385340725738888068866033 119539005544304166051649525)
  ·
    refine ⟨11206781769778515567342143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119539005544304166051649525 11206781769778515567342143)
    ·
      refine ⟨16810172654667773351013215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11206781769778515567342143 16810172654667773351013215)
      ·
        refine ⟨25215258982001660026519823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16810172654667773351013215 25215258982001660026519823)
        ·
          refine ⟨37822888473002490039779735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25215258982001660026519823 37822888473002490039779735)
          ·
            refine ⟨56734332709503735059669603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37822888473002490039779735 56734332709503735059669603)
            ·
              refine ⟨85101499064255602589504405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56734332709503735059669603 85101499064255602589504405)
              ·
                refine ⟨3989132768636981371383019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85101499064255602589504405 3989132768636981371383019)
                ·
                  refine ⟨5983699152955472057074529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989132768636981371383019 5983699152955472057074529)
                  ·
                    refine ⟨4487774364716604042805897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983699152955472057074529 4487774364716604042805897)
                    ·
                      refine ⟨3365830773537453032104423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487774364716604042805897 3365830773537453032104423)
                      ·
                        rfl

theorem cell23_6554932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6554932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554932 prefixEnd_6554932 := by exact prefixLift 6554932
  have htrace : WordTrace (prefixWord ++ tailWord_6554932) baseStart_6554932 baseEnd_6554932 := by
    simpa [prefixWord, tailWord_6554932, baseEnd_6554932] using wordTrace_append hprefix tailTrace_6554932
  have hstable : (prefixWord ++ tailWord_6554932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554932).length < 2 ^ (prefixWord ++ tailWord_6554932).sum := by decide
  have hdescent : baseEnd_6554932 < baseStart_6554932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6554954 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_6554954 : Nat := 118140960795 + 6554954 * 2 ^ 59
def prefixEnd_6554954 : Nat := 4983230072969 + 3 ^ 40 * 6554954 * 2
def baseEnd_6554954 : Nat := 3365842070111851946029321

theorem tailTrace_6554954 : CollatzResearch.WordTrace tailWord_6554954 prefixEnd_6554954 3365842070111851946029321 := by
  unfold tailWord_6554954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59769703373632157465149979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159385875663019086573733277 59769703373632157465149979)
  ·
    refine ⟨89654555060448236197724969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59769703373632157465149979 89654555060448236197724969)
    ·
      refine ⟨67240916295336177148293727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89654555060448236197724969 67240916295336177148293727)
      ·
        refine ⟨100861374443004265722440591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67240916295336177148293727 100861374443004265722440591)
        ·
          refine ⟨151292061664506398583660887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100861374443004265722440591 151292061664506398583660887)
          ·
            refine ⟨226938092496759597875491331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151292061664506398583660887 226938092496759597875491331)
            ·
              refine ⟨340407138745139396813236997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226938092496759597875491331 340407138745139396813236997)
              ·
                refine ⟨63826338514713636902481937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340407138745139396813236997 63826338514713636902481937)
                ·
                  refine ⟨47869753886035227676861453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63826338514713636902481937 47869753886035227676861453)
                  ·
                    refine ⟨17951157707263210378823045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47869753886035227676861453 17951157707263210378823045)
                    ·
                      refine ⟨3365842070111851946029321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17951157707263210378823045 3365842070111851946029321)
                      ·
                        rfl

theorem cell23_6554954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_6554954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6554954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6554954 prefixEnd_6554954 := by exact prefixLift 6554954
  have htrace : WordTrace (prefixWord ++ tailWord_6554954) baseStart_6554954 baseEnd_6554954 := by
    simpa [prefixWord, tailWord_6554954, baseEnd_6554954] using wordTrace_append hprefix tailTrace_6554954
  have hstable : (prefixWord ++ tailWord_6554954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6554954).length < 2 ^ (prefixWord ++ tailWord_6554954).sum := by decide
  have hdescent : baseEnd_6554954 < baseStart_6554954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6554954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555005 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_6555005 : Nat := 118140960795 + 6555005 * 2 ^ 59
def prefixEnd_6555005 : Nat := 4983230072969 + 3 ^ 40 * 6555005 * 2
def baseEnd_6555005 : Nat := 3365868257625231246491587

theorem tailTrace_6555005 : CollatzResearch.WordTrace tailWord_6555005 prefixEnd_6555005 3365868257625231246491587 := by
  unfold tailWord_6555005
  simp only [CollatzResearch.WordTrace]
  refine ⟨239080673617343865570706469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159387115744895910380470979 239080673617343865570706469)
  ·
    refine ⟨44827626303251974794507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239080673617343865570706469 44827626303251974794507463)
    ·
      refine ⟨67241439454877962191761195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44827626303251974794507463 67241439454877962191761195)
      ·
        refine ⟨100862159182316943287641793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67241439454877962191761195 100862159182316943287641793)
        ·
          refine ⟨75646619386737707465731345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100862159182316943287641793 75646619386737707465731345)
          ·
            refine ⟨56734964540053280599298509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75646619386737707465731345 56734964540053280599298509)
            ·
              refine ⟨21275611702519980224736941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56734964540053280599298509 21275611702519980224736941)
              ·
                refine ⟨7978354388444992584276353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21275611702519980224736941 7978354388444992584276353)
                ·
                  refine ⟨5983765791333744438207265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978354388444992584276353 5983765791333744438207265)
                  ·
                    refine ⟨4487824343500308328655449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983765791333744438207265 4487824343500308328655449)
                    ·
                      refine ⟨3365868257625231246491587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487824343500308328655449 3365868257625231246491587)
                      ·
                        rfl

theorem cell23_6555005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_6555005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555005 prefixEnd_6555005 := by exact prefixLift 6555005
  have htrace : WordTrace (prefixWord ++ tailWord_6555005) baseStart_6555005 baseEnd_6555005 := by
    simpa [prefixWord, tailWord_6555005, baseEnd_6555005] using wordTrace_append hprefix tailTrace_6555005
  have hstable : (prefixWord ++ tailWord_6555005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555005).length < 2 ^ (prefixWord ++ tailWord_6555005).sum := by decide
  have hdescent : baseEnd_6555005 < baseStart_6555005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555009 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6555009 : Nat := 118140960795 + 6555009 * 2 ^ 59
def prefixEnd_6555009 : Nat := 4983230072969 + 3 ^ 40 * 6555009 * 2
def baseEnd_6555009 : Nat := 3365870311547849230841569

theorem tailTrace_6555009 : CollatzResearch.WordTrace tailWord_6555009 prefixEnd_6555009 3365870311547849230841569 := by
  unfold tailWord_6555009
  simp only [CollatzResearch.WordTrace]
  refine ⟨239080819509329374253852081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159387213006219582835901387 239080819509329374253852081)
  ·
    refine ⟨179310614631997030690389061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239080819509329374253852081 179310614631997030690389061)
    ·
      refine ⟨33620740243499443254447949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179310614631997030690389061 33620740243499443254447949)
      ·
        refine ⟨12607777591312291220417981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33620740243499443254447949 12607777591312291220417981)
        ·
          refine ⟨4727916596742109207656743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12607777591312291220417981 4727916596742109207656743)
          ·
            refine ⟨7091874895113163811485115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727916596742109207656743 7091874895113163811485115)
            ·
              refine ⟨10637812342669745717227673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091874895113163811485115 10637812342669745717227673)
              ·
                refine ⟨7978359257002309287920755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637812342669745717227673 7978359257002309287920755)
                ·
                  refine ⟨11967538885503463931881133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978359257002309287920755 11967538885503463931881133)
                  ·
                    refine ⟨4487827082063798974455425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11967538885503463931881133 4487827082063798974455425)
                    ·
                      refine ⟨3365870311547849230841569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487827082063798974455425 3365870311547849230841569)
                      ·
                        rfl

theorem cell23_6555009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6555009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555009 prefixEnd_6555009 := by exact prefixLift 6555009
  have htrace : WordTrace (prefixWord ++ tailWord_6555009) baseStart_6555009 baseEnd_6555009 := by
    simpa [prefixWord, tailWord_6555009, baseEnd_6555009] using wordTrace_append hprefix tailTrace_6555009
  have hstable : (prefixWord ++ tailWord_6555009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555009).length < 2 ^ (prefixWord ++ tailWord_6555009).sum := by decide
  have hdescent : baseEnd_6555009 < baseStart_6555009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555105 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 1, 4]
def baseStart_6555105 : Nat := 118140960795 + 6555105 * 2 ^ 59
def prefixEnd_6555105 : Nat := 4983230072969 + 3 ^ 40 * 6555105 * 2
def baseEnd_6555105 : Nat := 1121973201896893618413709

theorem tailTrace_6555105 : CollatzResearch.WordTrace tailWord_6555105 prefixEnd_6555105 1121973201896893618413709 := by
  unfold tailWord_6555105
  simp only [CollatzResearch.WordTrace]
  refine ⟨239084320916981582649346769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159389547277987721766231179 239084320916981582649346769)
  ·
    refine ⟨179313240687736186987010077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239084320916981582649346769 179313240687736186987010077)
    ·
      refine ⟨67242465257901070120128779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179313240687736186987010077 67242465257901070120128779)
      ·
        refine ⟨100863697886851605180193169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67242465257901070120128779 100863697886851605180193169)
        ·
          refine ⟨75647773415138703885144877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100863697886851605180193169 75647773415138703885144877)
          ·
            refine ⟨28367915030677013956929329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75647773415138703885144877 28367915030677013956929329)
            ·
              refine ⟨21275936273007760467696997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28367915030677013956929329 21275936273007760467696997)
              ·
                refine ⟨3989238051188955087693187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21275936273007760467696997 3989238051188955087693187)
                ·
                  refine ⟨5983857076783432631539781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989238051188955087693187 5983857076783432631539781)
                  ·
                    refine ⟨1121973201896893618413709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983857076783432631539781 1121973201896893618413709)
                    ·
                      rfl

theorem cell23_6555105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_6555105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555105 prefixEnd_6555105 := by exact prefixLift 6555105
  have htrace : WordTrace (prefixWord ++ tailWord_6555105) baseStart_6555105 baseEnd_6555105 := by
    simpa [prefixWord, tailWord_6555105, baseEnd_6555105] using wordTrace_append hprefix tailTrace_6555105
  have hstable : (prefixWord ++ tailWord_6555105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555105).length < 2 ^ (prefixWord ++ tailWord_6555105).sum := by decide
  have hdescent : baseEnd_6555105 < baseStart_6555105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555149 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6555149 : Nat := 118140960795 + 6555149 * 2 ^ 59
def prefixEnd_6555149 : Nat := 4983230072969 + 3 ^ 40 * 6555149 * 2
def baseEnd_6555149 : Nat := 3365942198839478683090925

theorem tailTrace_6555149 : CollatzResearch.WordTrace tailWord_6555149 prefixEnd_6555149 3365942198839478683090925 := by
  unfold tailWord_6555149
  simp only [CollatzResearch.WordTrace]
  refine ⟨239085925728822178163948501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159390617152548118775965667 239085925728822178163948501)
  ·
    refine ⟨5603576384269269800717543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 239085925728822178163948501 5603576384269269800717543)
    ·
      refine ⟨8405364576403904701076315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5603576384269269800717543 8405364576403904701076315)
      ·
        refine ⟨12608046864605857051614473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405364576403904701076315 12608046864605857051614473)
        ·
          refine ⟨9456035148454392788710855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12608046864605857051614473 9456035148454392788710855)
          ·
            refine ⟨14184052722681589183066283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456035148454392788710855 14184052722681589183066283)
            ·
              refine ⟨21276079084022383774599425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14184052722681589183066283 21276079084022383774599425)
              ·
                refine ⟨15957059313016787830949569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21276079084022383774599425 15957059313016787830949569)
                ·
                  refine ⟨11967794484762590873212177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15957059313016787830949569 11967794484762590873212177)
                  ·
                    refine ⟨8975845863571943154909133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11967794484762590873212177 8975845863571943154909133)
                    ·
                      refine ⟨3365942198839478683090925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975845863571943154909133 3365942198839478683090925)
                      ·
                        rfl

theorem cell23_6555149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6555149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555149 prefixEnd_6555149 := by exact prefixLift 6555149
  have htrace : WordTrace (prefixWord ++ tailWord_6555149) baseStart_6555149 baseEnd_6555149 := by
    simpa [prefixWord, tailWord_6555149, baseEnd_6555149] using wordTrace_append hprefix tailTrace_6555149
  have hstable : (prefixWord ++ tailWord_6555149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555149).length < 2 ^ (prefixWord ++ tailWord_6555149).sum := by decide
  have hdescent : baseEnd_6555149 < baseStart_6555149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555155 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 2, 3, 2]
def baseStart_6555155 : Nat := 118140960795 + 6555155 * 2 ^ 59
def prefixEnd_6555155 : Nat := 4983230072969 + 3 ^ 40 * 6555155 * 2
def baseEnd_6555155 : Nat := 3365945279723405659615897

theorem tailTrace_6555155 : CollatzResearch.WordTrace tailWord_6555155 prefixEnd_6555155 3365945279723405659615897 := by
  unfold tailWord_6555155
  simp only [CollatzResearch.WordTrace]
  refine ⟨239086144566800441188666919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159390763044533627459111279 239086144566800441188666919)
  ·
    refine ⟨358629216850200661783000379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239086144566800441188666919 358629216850200661783000379)
    ·
      refine ⟨537943825275300992674500569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358629216850200661783000379 537943825275300992674500569)
      ·
        refine ⟨403457868956475744505875427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537943825275300992674500569 403457868956475744505875427)
        ·
          refine ⟨605186803434713616758813141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403457868956475744505875427 605186803434713616758813141)
          ·
            refine ⟨14184065705501100392784683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 605186803434713616758813141 14184065705501100392784683)
            ·
              refine ⟨21276098558251650589177025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14184065705501100392784683 21276098558251650589177025)
              ·
                refine ⟨15957073918688737941882769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21276098558251650589177025 15957073918688737941882769)
                ·
                  refine ⟨11967805439016553456412077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15957073918688737941882769 11967805439016553456412077)
                  ·
                    refine ⟨4487927039631207546154529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11967805439016553456412077 4487927039631207546154529)
                    ·
                      refine ⟨3365945279723405659615897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487927039631207546154529 3365945279723405659615897)
                      ·
                        rfl

theorem cell23_6555155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3, 2].length) (baseStart_6555155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555155 prefixEnd_6555155 := by exact prefixLift 6555155
  have htrace : WordTrace (prefixWord ++ tailWord_6555155) baseStart_6555155 baseEnd_6555155 := by
    simpa [prefixWord, tailWord_6555155, baseEnd_6555155] using wordTrace_append hprefix tailTrace_6555155
  have hstable : (prefixWord ++ tailWord_6555155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555155).length < 2 ^ (prefixWord ++ tailWord_6555155).sum := by decide
  have hdescent : baseEnd_6555155 < baseStart_6555155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555156 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6555156 : Nat := 118140960795 + 6555156 * 2 ^ 59
def prefixEnd_6555156 : Nat := 4983230072969 + 3 ^ 40 * 6555156 * 2
def baseEnd_6555156 : Nat := 1121981931068020051901131

theorem tailTrace_6555156 : CollatzResearch.WordTrace tailWord_6555156 prefixEnd_6555156 1121981931068020051901131 := by
  unfold tailWord_6555156
  simp only [CollatzResearch.WordTrace]
  refine ⟨119543090519898409179726661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159390787359864545572968881 119543090519898409179726661)
  ·
    refine ⟨22414329472480951721198749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119543090519898409179726661 22414329472480951721198749)
    ·
      refine ⟨8405373552180356895449531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22414329472480951721198749 8405373552180356895449531)
      ·
        refine ⟨12608060328270535343174297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405373552180356895449531 12608060328270535343174297)
        ·
          refine ⟨9456045246202901507380723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12608060328270535343174297 9456045246202901507380723)
          ·
            refine ⟨14184067869304352261071085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456045246202901507380723 14184067869304352261071085)
            ·
              refine ⟨5319025450989132097901657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14184067869304352261071085 5319025450989132097901657)
              ·
                refine ⟨3989269088241849073426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319025450989132097901657 3989269088241849073426243)
                ·
                  refine ⟨5983903632362773610139365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989269088241849073426243 5983903632362773610139365)
                  ·
                    refine ⟨1121981931068020051901131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983903632362773610139365 1121981931068020051901131)
                    ·
                      rfl

theorem cell23_6555156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6555156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555156 prefixEnd_6555156 := by exact prefixLift 6555156
  have htrace : WordTrace (prefixWord ++ tailWord_6555156) baseStart_6555156 baseEnd_6555156 := by
    simpa [prefixWord, tailWord_6555156, baseEnd_6555156] using wordTrace_append hprefix tailTrace_6555156
  have hstable : (prefixWord ++ tailWord_6555156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555156).length < 2 ^ (prefixWord ++ tailWord_6555156).sum := by decide
  have hdescent : baseEnd_6555156 < baseStart_6555156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555178 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_6555178 : Nat := 118140960795 + 6555178 * 2 ^ 59
def prefixEnd_6555178 : Nat := 4983230072969 + 3 ^ 40 * 6555178 * 2
def baseEnd_6555178 : Nat := 1121985696592819689876097

theorem tailTrace_6555178 : CollatzResearch.WordTrace tailWord_6555178 prefixEnd_6555178 1121985696592819689876097 := by
  unfold tailWord_6555178
  simp only [CollatzResearch.WordTrace]
  refine ⟨59771745861429279029188547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159391322297144744077836125 59771745861429279029188547)
  ·
    refine ⟨89657618792143918543782821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59771745861429279029188547 89657618792143918543782821)
    ·
      refine ⟨16810803523526984726959279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89657618792143918543782821 16810803523526984726959279)
      ·
        refine ⟨25216205285290477090438919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16810803523526984726959279 25216205285290477090438919)
        ·
          refine ⟨37824307927935715635658379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25216205285290477090438919 37824307927935715635658379)
          ·
            refine ⟨56736461891903573453487569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37824307927935715635658379 56736461891903573453487569)
            ·
              refine ⟨42552346418927680090115677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56736461891903573453487569 42552346418927680090115677)
              ·
                refine ⟨15957129907097880033793379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42552346418927680090115677 15957129907097880033793379)
                ·
                  refine ⟨23935694860646820050690069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15957129907097880033793379 23935694860646820050690069)
                  ·
                    refine ⟨1121985696592819689876097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23935694860646820050690069 1121985696592819689876097)
                    ·
                      rfl

theorem cell23_6555178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_6555178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555178 prefixEnd_6555178 := by exact prefixLift 6555178
  have htrace : WordTrace (prefixWord ++ tailWord_6555178) baseStart_6555178 baseEnd_6555178 := by
    simpa [prefixWord, tailWord_6555178, baseEnd_6555178] using wordTrace_append hprefix tailTrace_6555178
  have hstable : (prefixWord ++ tailWord_6555178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555178).length < 2 ^ (prefixWord ++ tailWord_6555178).sum := by decide
  have hdescent : baseEnd_6555178 < baseStart_6555178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555182 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_6555182 : Nat := 118140960795 + 6555182 * 2 ^ 59
def prefixEnd_6555182 : Nat := 4983230072969 + 3 ^ 40 * 6555182 * 2
def baseEnd_6555182 : Nat := 1121986381233692351326091

theorem tailTrace_6555182 : CollatzResearch.WordTrace tailWord_6555182 prefixEnd_6555182 1121986381233692351326091 := by
  unfold tailWord_6555182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885891167212828099987475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159391419558468416533266533 29885891167212828099987475)
  ·
    refine ⟨44828836750819242149981213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885891167212828099987475 44828836750819242149981213)
    ·
      refine ⟨16810813781557215806242955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44828836750819242149981213 16810813781557215806242955)
      ·
        refine ⟨25216220672335823709364433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16810813781557215806242955 25216220672335823709364433)
        ·
          refine ⟨18912165504251867782023325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25216220672335823709364433 18912165504251867782023325)
          ·
            refine ⟨7092062064094450418258747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18912165504251867782023325 7092062064094450418258747)
            ·
              refine ⟨10638093096141675627388121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092062064094450418258747 10638093096141675627388121)
              ·
                refine ⟨7978569822106256720541091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10638093096141675627388121 7978569822106256720541091)
                ·
                  refine ⟨11967854733159385080811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978569822106256720541091 11967854733159385080811637)
                  ·
                    refine ⟨1121986381233692351326091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11967854733159385080811637 1121986381233692351326091)
                    ·
                      rfl

theorem cell23_6555182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_6555182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555182 prefixEnd_6555182 := by exact prefixLift 6555182
  have htrace : WordTrace (prefixWord ++ tailWord_6555182) baseStart_6555182 baseEnd_6555182 := by
    simpa [prefixWord, tailWord_6555182, baseEnd_6555182] using wordTrace_append hprefix tailTrace_6555182
  have hstable : (prefixWord ++ tailWord_6555182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555182).length < 2 ^ (prefixWord ++ tailWord_6555182).sum := by decide
  have hdescent : baseEnd_6555182 < baseStart_6555182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555185 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_6555185 : Nat := 118140960795 + 6555185 * 2 ^ 59
def prefixEnd_6555185 : Nat := 4983230072969 + 3 ^ 40 * 6555185 * 2
def baseEnd_6555185 : Nat := 3365960684143040542240759

theorem tailTrace_6555185 : CollatzResearch.WordTrace tailWord_6555185 prefixEnd_6555185 3365960684143040542240759 := by
  unfold tailWord_6555185
  simp only [CollatzResearch.WordTrace]
  refine ⟨239087238756691756312259009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159391492504461170874839339 239087238756691756312259009)
  ·
    refine ⟨179315429067518817234194257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239087238756691756312259009 179315429067518817234194257)
    ·
      refine ⟨134486571800639112925645693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179315429067518817234194257 134486571800639112925645693)
      ·
        refine ⟨50432464425239667347117135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134486571800639112925645693 50432464425239667347117135)
        ·
          refine ⟨75648696637859501020675703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50432464425239667347117135 75648696637859501020675703)
          ·
            refine ⟨113473044956789251531013555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75648696637859501020675703 113473044956789251531013555)
            ·
              refine ⟨170209567435183877296520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113473044956789251531013555 170209567435183877296520333)
              ·
                refine ⟨63828587788193953986195125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170209567435183877296520333 63828587788193953986195125)
                ·
                  refine ⟨5983930105143183186205793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63828587788193953986195125 5983930105143183186205793)
                  ·
                    refine ⟨4487947578857387389654345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983930105143183186205793 4487947578857387389654345)
                    ·
                      refine ⟨3365960684143040542240759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4487947578857387389654345 3365960684143040542240759)
                      ·
                        rfl

theorem cell23_6555185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_6555185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555185 prefixEnd_6555185 := by exact prefixLift 6555185
  have htrace : WordTrace (prefixWord ++ tailWord_6555185) baseStart_6555185 baseEnd_6555185 := by
    simpa [prefixWord, tailWord_6555185, baseEnd_6555185] using wordTrace_append hprefix tailTrace_6555185
  have hstable : (prefixWord ++ tailWord_6555185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555185).length < 2 ^ (prefixWord ++ tailWord_6555185).sum := by decide
  have hdescent : baseEnd_6555185 < baseStart_6555185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555191 : List Nat := [1, 1, 3, 1, 2, 4, 2, 9]
def baseStart_6555191 : Nat := 118140960795 + 6555191 * 2 ^ 59
def prefixEnd_6555191 : Nat := 4983230072969 + 3 ^ 40 * 6555191 * 2
def baseEnd_6555191 : Nat := 124665324630628426620953

theorem tailTrace_6555191 : CollatzResearch.WordTrace tailWord_6555191 prefixEnd_6555191 124665324630628426620953 := by
  unfold tailWord_6555191
  simp only [CollatzResearch.WordTrace]
  refine ⟨239087457594670019336977427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159391638396446679557984951 239087457594670019336977427)
  ·
    refine ⟨358631186392005029005466141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239087457594670019336977427 358631186392005029005466141)
    ·
      refine ⟨134486694897001885877049803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358631186392005029005466141 134486694897001885877049803)
      ·
        refine ⟨201730042345502828815574705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134486694897001885877049803 201730042345502828815574705)
        ·
          refine ⟨151297531759127121611681029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201730042345502828815574705 151297531759127121611681029)
          ·
            refine ⟨28368287204836335302190193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151297531759127121611681029 28368287204836335302190193)
            ·
              refine ⟨21276215403627251476642645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28368287204836335302190193 21276215403627251476642645)
              ·
                refine ⟨124665324630628426620953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21276215403627251476642645 124665324630628426620953)
                ·
                  rfl

theorem cell23_6555191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 9].length) (baseStart_6555191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555191 prefixEnd_6555191 := by exact prefixLift 6555191
  have htrace : WordTrace (prefixWord ++ tailWord_6555191) baseStart_6555191 baseEnd_6555191 := by
    simpa [prefixWord, tailWord_6555191, baseEnd_6555191] using wordTrace_append hprefix tailTrace_6555191
  have hstable : (prefixWord ++ tailWord_6555191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555191).length < 2 ^ (prefixWord ++ tailWord_6555191).sum := by decide
  have hdescent : baseEnd_6555191 < baseStart_6555191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555213 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6555213 : Nat := 118140960795 + 6555213 * 2 ^ 59
def prefixEnd_6555213 : Nat := 4983230072969 + 3 ^ 40 * 6555213 * 2
def baseEnd_6555213 : Nat := 3365975061601366432690631

theorem tailTrace_6555213 : CollatzResearch.WordTrace tailWord_6555213 prefixEnd_6555213 3365975061601366432690631 := by
  unfold tailWord_6555213
  simp only [CollatzResearch.WordTrace]
  refine ⟨239088260000590317094278293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159392173333726878062852195 239088260000590317094278293)
  ·
    refine ⟨11207262187527671113794295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239088260000590317094278293 11207262187527671113794295)
    ·
      refine ⟨16810893281291506670691443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11207262187527671113794295 16810893281291506670691443)
      ·
        refine ⟨25216339921937260006037165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16810893281291506670691443 25216339921937260006037165)
        ·
          refine ⟨9456127470726472502263937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25216339921937260006037165 9456127470726472502263937)
          ·
            refine ⟨7092095603044854376697953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9456127470726472502263937 7092095603044854376697953)
            ·
              refine ⟨5319071702283640782523465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092095603044854376697953 5319071702283640782523465)
              ·
                refine ⟨3989303776712730586892599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319071702283640782523465 3989303776712730586892599)
                ·
                  refine ⟨5983955665069095880338899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989303776712730586892599 5983955665069095880338899)
                  ·
                    refine ⟨8975933497603643820508349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983955665069095880338899 8975933497603643820508349)
                    ·
                      refine ⟨3365975061601366432690631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975933497603643820508349 3365975061601366432690631)
                      ·
                        rfl

theorem cell23_6555213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6555213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555213 prefixEnd_6555213 := by exact prefixLift 6555213
  have htrace : WordTrace (prefixWord ++ tailWord_6555213) baseStart_6555213 baseEnd_6555213 := by
    simpa [prefixWord, tailWord_6555213, baseEnd_6555213] using wordTrace_append hprefix tailTrace_6555213
  have hstable : (prefixWord ++ tailWord_6555213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555213).length < 2 ^ (prefixWord ++ tailWord_6555213).sum := by decide
  have hdescent : baseEnd_6555213 < baseStart_6555213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555231 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6555231 : Nat := 118140960795 + 6555231 * 2 ^ 59
def prefixEnd_6555231 : Nat := 4983230072969 + 3 ^ 40 * 6555231 * 2
def baseEnd_6555231 : Nat := 3365984304253147362265547

theorem tailTrace_6555231 : CollatzResearch.WordTrace tailWord_6555231 prefixEnd_6555231 3365984304253147362265547 := by
  unfold tailWord_6555231
  simp only [CollatzResearch.WordTrace]
  refine ⟨239088916514525106168433547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159392611009683404112289031 239088916514525106168433547)
  ·
    refine ⟨358633374771787659252650321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239088916514525106168433547 358633374771787659252650321)
    ·
      refine ⟨268975031078840744439487741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358633374771787659252650321 268975031078840744439487741)
      ·
        refine ⟨100865636654565279164807903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268975031078840744439487741 100865636654565279164807903)
        ·
          refine ⟨151298454981847918747211855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100865636654565279164807903 151298454981847918747211855)
          ·
            refine ⟨226947682472771878120817783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151298454981847918747211855 226947682472771878120817783)
            ·
              refine ⟨340421523709157817181226675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226947682472771878120817783 340421523709157817181226675)
              ·
                refine ⟨510632285563736725771840013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340421523709157817181226675 510632285563736725771840013)
                ·
                  refine ⟨191487107086401272164440005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 510632285563736725771840013 191487107086401272164440005)
                  ·
                    refine ⟨35903832578700238530832501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191487107086401272164440005 35903832578700238530832501)
                    ·
                      refine ⟨3365984304253147362265547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35903832578700238530832501 3365984304253147362265547)
                      ·
                        rfl

theorem cell23_6555231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6555231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555231 prefixEnd_6555231 := by exact prefixLift 6555231
  have htrace : WordTrace (prefixWord ++ tailWord_6555231) baseStart_6555231 baseEnd_6555231 := by
    simpa [prefixWord, tailWord_6555231, baseEnd_6555231] using wordTrace_append hprefix tailTrace_6555231
  have hstable : (prefixWord ++ tailWord_6555231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555231).length < 2 ^ (prefixWord ++ tailWord_6555231).sum := by decide
  have hdescent : baseEnd_6555231 < baseStart_6555231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555235 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3]
def baseStart_6555235 : Nat := 118140960795 + 6555235 * 2 ^ 59
def prefixEnd_6555235 : Nat := 4983230072969 + 3 ^ 40 * 6555235 * 2
def baseEnd_6555235 : Nat := 3365986358175765346615529

theorem tailTrace_6555235 : CollatzResearch.WordTrace tailWord_6555235 prefixEnd_6555235 3365986358175765346615529 := by
  unfold tailWord_6555235
  simp only [CollatzResearch.WordTrace]
  refine ⟨239089062406510614851579159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159392708271007076567719439 239089062406510614851579159)
  ·
    refine ⟨358633593609765922277368739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239089062406510614851579159 358633593609765922277368739)
    ·
      refine ⟨537950390414648883416053109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358633593609765922277368739 537950390414648883416053109)
      ·
        refine ⟨50432849101373332820254979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 537950390414648883416053109 50432849101373332820254979)
        ·
          refine ⟨75649273652059999230382469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50432849101373332820254979 75649273652059999230382469)
          ·
            refine ⟨14184238809761249855696713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75649273652059999230382469 14184238809761249855696713)
            ·
              refine ⟨10638179107320937391772535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14184238809761249855696713 10638179107320937391772535)
              ·
                refine ⟨15957268660981406087658803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10638179107320937391772535 15957268660981406087658803)
                ·
                  refine ⟨23935902991472109131488205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15957268660981406087658803 23935902991472109131488205)
                  ·
                    refine ⟨8975963621802040924308077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23935902991472109131488205 8975963621802040924308077)
                    ·
                      refine ⟨3365986358175765346615529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8975963621802040924308077 3365986358175765346615529)
                      ·
                        rfl

theorem cell23_6555235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_6555235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555235 prefixEnd_6555235 := by exact prefixLift 6555235
  have htrace : WordTrace (prefixWord ++ tailWord_6555235) baseStart_6555235 baseEnd_6555235 := by
    simpa [prefixWord, tailWord_6555235, baseEnd_6555235] using wordTrace_append hprefix tailTrace_6555235
  have hstable : (prefixWord ++ tailWord_6555235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555235).length < 2 ^ (prefixWord ++ tailWord_6555235).sum := by decide
  have hdescent : baseEnd_6555235 < baseStart_6555235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555335 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_6555335 : Nat := 118140960795 + 6555335 * 2 ^ 59
def prefixEnd_6555335 : Nat := 4983230072969 + 3 ^ 40 * 6555335 * 2
def baseEnd_6555335 : Nat := 3366037706241214955365069

theorem tailTrace_6555335 : CollatzResearch.WordTrace tailWord_6555335 prefixEnd_6555335 3366037706241214955365069 := by
  unfold tailWord_6555335
  simp only [CollatzResearch.WordTrace]
  refine ⟨239092709706148331930219459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159395139804098887953479639 239092709706148331930219459)
  ·
    refine ⟨358639064559222497895329189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239092709706148331930219459 358639064559222497895329189)
    ·
      refine ⟨67244824604854218355374223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358639064559222497895329189 67244824604854218355374223)
      ·
        refine ⟨100867236907281327533061335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67244824604854218355374223 100867236907281327533061335)
        ·
          refine ⟨151300855360921991299592003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100867236907281327533061335 151300855360921991299592003)
          ·
            refine ⟨226951283041382986949388005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151300855360921991299592003 226951283041382986949388005)
            ·
              refine ⟨42553365570259310053010251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226951283041382986949388005 42553365570259310053010251)
              ·
                refine ⟨63830048355388965079515377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42553365570259310053010251 63830048355388965079515377)
                ·
                  refine ⟨47872536266541723809636533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63830048355388965079515377 47872536266541723809636533)
                  ·
                    refine ⟨4488050274988286607153425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47872536266541723809636533 4488050274988286607153425)
                    ·
                      refine ⟨3366037706241214955365069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488050274988286607153425 3366037706241214955365069)
                      ·
                        rfl

theorem cell23_6555335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_6555335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555335 prefixEnd_6555335 := by exact prefixLift 6555335
  have htrace : WordTrace (prefixWord ++ tailWord_6555335) baseStart_6555335 baseEnd_6555335 := by
    simpa [prefixWord, tailWord_6555335, baseEnd_6555335] using wordTrace_append hprefix tailTrace_6555335
  have hstable : (prefixWord ++ tailWord_6555335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555335).length < 2 ^ (prefixWord ++ tailWord_6555335).sum := by decide
  have hdescent : baseEnd_6555335 < baseStart_6555335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555382 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6555382 : Nat := 118140960795 + 6555382 * 2 ^ 59
def prefixEnd_6555382 : Nat := 4983230072969 + 3 ^ 40 * 6555382 * 2
def baseEnd_6555382 : Nat := 3366061839831976271477353

theorem tailTrace_6555382 : CollatzResearch.WordTrace tailWord_6555382 prefixEnd_6555382 3366061839831976271477353 := by
  unfold tailWord_6555382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943401496061128684823775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159396282624652039304786933 14943401496061128684823775)
  ·
    refine ⟨22415102244091693027235663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14943401496061128684823775 22415102244091693027235663)
    ·
      refine ⟨33622653366137539540853495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22415102244091693027235663 33622653366137539540853495)
      ·
        refine ⟨50433980049206309311280243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33622653366137539540853495 50433980049206309311280243)
        ·
          refine ⟨75650970073809463966920365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50433980049206309311280243 75650970073809463966920365)
          ·
            refine ⟨28369113777678548987595137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75650970073809463966920365 28369113777678548987595137)
            ·
              refine ⟨21276835333258911740696353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28369113777678548987595137 21276835333258911740696353)
              ·
                refine ⟨15957626499944183805522265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21276835333258911740696353 15957626499944183805522265)
                ·
                  refine ⟨11968219874958137854141699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15957626499944183805522265 11968219874958137854141699)
                  ·
                    refine ⟨17952329812437206781212549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11968219874958137854141699 17952329812437206781212549)
                    ·
                      refine ⟨3366061839831976271477353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17952329812437206781212549 3366061839831976271477353)
                      ·
                        rfl

theorem cell23_6555382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6555382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555382 prefixEnd_6555382 := by exact prefixLift 6555382
  have htrace : WordTrace (prefixWord ++ tailWord_6555382) baseStart_6555382 baseEnd_6555382 := by
    simpa [prefixWord, tailWord_6555382, baseEnd_6555382] using wordTrace_append hprefix tailTrace_6555382
  have hstable : (prefixWord ++ tailWord_6555382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555382).length < 2 ^ (prefixWord ++ tailWord_6555382).sum := by decide
  have hdescent : baseEnd_6555382 < baseStart_6555382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555392 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 1, 4]
def baseStart_6555392 : Nat := 118140960795 + 6555392 * 2 ^ 59
def prefixEnd_6555392 : Nat := 4983230072969 + 3 ^ 40 * 6555392 * 2
def baseEnd_6555392 : Nat := 1122022324879507077450769

theorem tailTrace_6555392 : CollatzResearch.WordTrace tailWord_6555392 prefixEnd_6555392 1122022324879507077450769 := by
  unfold tailWord_6555392
  simp only [CollatzResearch.WordTrace]
  refine ⟨119547394333470915332522215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159396525777961220443362953 119547394333470915332522215)
  ·
    refine ⟨179321091500206372998783323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119547394333470915332522215 179321091500206372998783323)
    ·
      refine ⟨268981637250309559498174985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179321091500206372998783323 268981637250309559498174985)
      ·
        refine ⟨201736227937732169623631239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268981637250309559498174985 201736227937732169623631239)
        ·
          refine ⟨302604341906598254435446859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201736227937732169623631239 302604341906598254435446859)
          ·
            refine ⟨453906512859897381653170289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302604341906598254435446859 453906512859897381653170289)
            ·
              refine ⟨340429884644923036239877717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453906512859897381653170289 340429884644923036239877717)
              ·
                refine ⟨3989412710682691830936067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 340429884644923036239877717 3989412710682691830936067)
                ·
                  refine ⟨5984119066024037746404101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989412710682691830936067 5984119066024037746404101)
                  ·
                    refine ⟨1122022324879507077450769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5984119066024037746404101 1122022324879507077450769)
                    ·
                      rfl

theorem cell23_6555392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_6555392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555392 prefixEnd_6555392 := by exact prefixLift 6555392
  have htrace : WordTrace (prefixWord ++ tailWord_6555392) baseStart_6555392 baseEnd_6555392 := by
    simpa [prefixWord, tailWord_6555392, baseEnd_6555392] using wordTrace_append hprefix tailTrace_6555392
  have hstable : (prefixWord ++ tailWord_6555392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555392).length < 2 ^ (prefixWord ++ tailWord_6555392).sum := by decide
  have hdescent : baseEnd_6555392 < baseStart_6555392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6555399 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6555399 : Nat := 118140960795 + 6555399 * 2 ^ 59
def prefixEnd_6555399 : Nat := 4983230072969 + 3 ^ 40 * 6555399 * 2
def baseEnd_6555399 : Nat := 3366070569003102704964775

theorem tailTrace_6555399 : CollatzResearch.WordTrace tailWord_6555399 prefixEnd_6555399 3366070569003102704964775 := by
  unfold tailWord_6555399
  simp only [CollatzResearch.WordTrace]
  refine ⟨239095043977916470860549251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159396695985277647240366167 239095043977916470860549251)
  ·
    refine ⟨358642565966874706290823877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239095043977916470860549251 358642565966874706290823877)
    ·
      refine ⟨67245481118789007429529477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358642565966874706290823877 67245481118789007429529477)
      ·
        refine ⟨12608527709772938893036777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67245481118789007429529477 12608527709772938893036777)
        ·
          refine ⟨9456395782329704169777583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12608527709772938893036777 9456395782329704169777583)
          ·
            refine ⟨14184593673494556254666375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456395782329704169777583 14184593673494556254666375)
            ·
              refine ⟨21276890510241834381999563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14184593673494556254666375 21276890510241834381999563)
              ·
                refine ⟨31915335765362751572999345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21276890510241834381999563 31915335765362751572999345)
                ·
                  refine ⟨23936501824022063679749509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31915335765362751572999345 23936501824022063679749509)
                  ·
                    refine ⟨4488094092004136939953033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23936501824022063679749509 4488094092004136939953033)
                    ·
                      refine ⟨3366070569003102704964775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4488094092004136939953033 3366070569003102704964775)
                      ·
                        rfl

theorem cell23_6555399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6555399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6555399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6555399 prefixEnd_6555399 := by exact prefixLift 6555399
  have htrace : WordTrace (prefixWord ++ tailWord_6555399) baseStart_6555399 baseEnd_6555399 := by
    simpa [prefixWord, tailWord_6555399, baseEnd_6555399] using wordTrace_append hprefix tailTrace_6555399
  have hstable : (prefixWord ++ tailWord_6555399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6555399).length < 2 ^ (prefixWord ++ tailWord_6555399).sum := by decide
  have hdescent : baseEnd_6555399 < baseStart_6555399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6555399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
