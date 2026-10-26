import V185TrunkScan23Chunk1197

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7097565 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7097565 : Nat := 118140960795 + 7097565 * 2 ^ 59
def prefixEnd_7097565 : Nat := 4983230072969 + 3 ^ 40 * 7097565 * 2
def baseEnd_7097565 : Nat := 1214820773842876159332133

theorem tailTrace_7097565 : CollatzResearch.WordTrace tailWord_7097565 prefixEnd_7097565 1214820773842876159332133 := by
  unfold tailWord_7097565
  simp only [CollatzResearch.WordTrace]
  refine ⟨258869462531741647441518149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172579641687827764961012099 258869462531741647441518149)
  ·
    refine ⟨48538024224701558895284653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258869462531741647441518149 48538024224701558895284653)
    ·
      refine ⟨18201759084263084585731745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48538024224701558895284653 18201759084263084585731745)
      ·
        refine ⟨13651319313197313439298809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18201759084263084585731745 13651319313197313439298809)
        ·
          refine ⟨10238489484897985079474107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13651319313197313439298809 10238489484897985079474107)
          ·
            refine ⟨15357734227346977619211161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238489484897985079474107 15357734227346977619211161)
            ·
              refine ⟨11518300670510233214408371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15357734227346977619211161 11518300670510233214408371)
              ·
                refine ⟨17277451005765349821612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518300670510233214408371 17277451005765349821612557)
                ·
                  refine ⟨6479044127162006183104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17277451005765349821612557 6479044127162006183104709)
                  ·
                    refine ⟨1214820773842876159332133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479044127162006183104709 1214820773842876159332133)
                    ·
                      rfl

theorem cell23_7097565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7097565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097565 prefixEnd_7097565 := by exact prefixLift 7097565
  have htrace : WordTrace (prefixWord ++ tailWord_7097565) baseStart_7097565 baseEnd_7097565 := by
    simpa [prefixWord, tailWord_7097565, baseEnd_7097565] using wordTrace_append hprefix tailTrace_7097565
  have hstable : (prefixWord ++ tailWord_7097565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097565).length < 2 ^ (prefixWord ++ tailWord_7097565).sum := by decide
  have hdescent : baseEnd_7097565 < baseStart_7097565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097578 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_7097578 : Nat := 118140960795 + 7097578 * 2 ^ 59
def prefixEnd_7097578 : Nat := 4983230072969 + 3 ^ 40 * 7097578 * 2
def baseEnd_7097578 : Nat := 404940999641904103014871

theorem tailTrace_7097578 : CollatzResearch.WordTrace tailWord_7097578 prefixEnd_7097578 404940999641904103014871 := by
  unfold tailWord_7097578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64717484170173637665435347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172579957787129700441160925 64717484170173637665435347)
  ·
    refine ⟨97076226255260456498153021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64717484170173637665435347 97076226255260456498153021)
    ·
      refine ⟨36403584845722671186807383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97076226255260456498153021 36403584845722671186807383)
      ·
        refine ⟨54605377268584006780211075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36403584845722671186807383 54605377268584006780211075)
        ·
          refine ⟨81908065902876010170316613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54605377268584006780211075 81908065902876010170316613)
          ·
            refine ⟨15357762356789251906934365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81908065902876010170316613 15357762356789251906934365)
            ·
              refine ⟨5759160883795969465100387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15357762356789251906934365 5759160883795969465100387)
              ·
                refine ⟨8638741325693954197650581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759160883795969465100387 8638741325693954197650581)
                ·
                  refine ⟨404940999641904103014871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8638741325693954197650581 404940999641904103014871)
                  ·
                    rfl

theorem cell23_7097578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_7097578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097578 prefixEnd_7097578 := by exact prefixLift 7097578
  have htrace : WordTrace (prefixWord ++ tailWord_7097578) baseStart_7097578 baseEnd_7097578 := by
    simpa [prefixWord, tailWord_7097578, baseEnd_7097578] using wordTrace_append hprefix tailTrace_7097578
  have hstable : (prefixWord ++ tailWord_7097578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097578).length < 2 ^ (prefixWord ++ tailWord_7097578).sum := by decide
  have hdescent : baseEnd_7097578 < baseStart_7097578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097645 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7097645 : Nat := 118140960795 + 7097645 * 2 ^ 59
def prefixEnd_7097645 : Nat := 4983230072969 + 3 ^ 40 * 7097645 * 2
def baseEnd_7097645 : Nat := 3644503399980988164996031

theorem tailTrace_7097645 : CollatzResearch.WordTrace tailWord_7097645 prefixEnd_7097645 3644503399980988164996031 := by
  unfold tailWord_7097645
  simp only [CollatzResearch.WordTrace]
  refine ⟨258872380371451821104430389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172581586914301214069620259 258872380371451821104430389)
  ·
    refine ⟨24269285659823608228540349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258872380371451821104430389 24269285659823608228540349)
    ·
      refine ⟨9100982122433853085702631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24269285659823608228540349 9100982122433853085702631)
      ·
        refine ⟨13651473183650779628553947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100982122433853085702631 13651473183650779628553947)
        ·
          refine ⟨20477209775476169442830921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651473183650779628553947 20477209775476169442830921)
          ·
            refine ⟨15357907331607127082123191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20477209775476169442830921 15357907331607127082123191)
            ·
              refine ⟨23036860997410690623184787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15357907331607127082123191 23036860997410690623184787)
              ·
                refine ⟨34555291496116035934777181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23036860997410690623184787 34555291496116035934777181)
                ·
                  refine ⟨12958234311043513475541443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34555291496116035934777181 12958234311043513475541443)
                  ·
                    refine ⟨19437351466565270213312165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12958234311043513475541443 19437351466565270213312165)
                    ·
                      refine ⟨3644503399980988164996031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19437351466565270213312165 3644503399980988164996031)
                      ·
                        rfl

theorem cell23_7097645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7097645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097645 prefixEnd_7097645 := by exact prefixLift 7097645
  have htrace : WordTrace (prefixWord ++ tailWord_7097645) baseStart_7097645 baseEnd_7097645 := by
    simpa [prefixWord, tailWord_7097645, baseEnd_7097645] using wordTrace_append hprefix tailTrace_7097645
  have hstable : (prefixWord ++ tailWord_7097645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097645).length < 2 ^ (prefixWord ++ tailWord_7097645).sum := by decide
  have hdescent : baseEnd_7097645 < baseStart_7097645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097665 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7097665 : Nat := 118140960795 + 7097665 * 2 ^ 59
def prefixEnd_7097665 : Nat := 4983230072969 + 3 ^ 40 * 7097665 * 2
def baseEnd_7097665 : Nat := 3644513669594078086745939

theorem tailTrace_7097665 : CollatzResearch.WordTrace tailWord_7097665 prefixEnd_7097665 3644513669594078086745939 := by
  unfold tailWord_7097665
  simp only [CollatzResearch.WordTrace]
  refine ⟨258873109831379364520158449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172582073220919576346772299 258873109831379364520158449)
  ·
    refine ⟨194154832373534523390118837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258873109831379364520158449 194154832373534523390118837)
    ·
      refine ⟨18202015535018861567823641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194154832373534523390118837 18202015535018861567823641)
      ·
        refine ⟨13651511651264146175867731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18202015535018861567823641 13651511651264146175867731)
        ·
          refine ⟨20477267476896219263801597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651511651264146175867731 20477267476896219263801597)
          ·
            refine ⟨7678975303836082223925599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20477267476896219263801597 7678975303836082223925599)
            ·
              refine ⟨11518462955754123335888399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678975303836082223925599 11518462955754123335888399)
              ·
                refine ⟨17277694433631185003832599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518462955754123335888399 17277694433631185003832599)
                ·
                  refine ⟨25916541650446777505748899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17277694433631185003832599 25916541650446777505748899)
                  ·
                    refine ⟨38874812475670166258623349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25916541650446777505748899 38874812475670166258623349)
                    ·
                      refine ⟨3644513669594078086745939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38874812475670166258623349 3644513669594078086745939)
                      ·
                        rfl

theorem cell23_7097665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7097665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097665 prefixEnd_7097665 := by exact prefixLift 7097665
  have htrace : WordTrace (prefixWord ++ tailWord_7097665) baseStart_7097665 baseEnd_7097665 := by
    simpa [prefixWord, tailWord_7097665, baseEnd_7097665] using wordTrace_append hprefix tailTrace_7097665
  have hstable : (prefixWord ++ tailWord_7097665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097665).length < 2 ^ (prefixWord ++ tailWord_7097665).sum := by decide
  have hdescent : baseEnd_7097665 < baseStart_7097665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097688 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_7097688 : Nat := 118140960795 + 7097688 * 2 ^ 59
def prefixEnd_7097688 : Nat := 4983230072969 + 3 ^ 40 * 7097688 * 2
def baseEnd_7097688 : Nat := 3644525479649131496758333

theorem tailTrace_7097688 : CollatzResearch.WordTrace tailWord_7097688 prefixEnd_7097688 3644525479649131496758333 := by
  unfold tailWord_7097688
  simp only [CollatzResearch.WordTrace]
  refine ⟨129436974355148019724122859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172582632473530692965497145 129436974355148019724122859)
  ·
    refine ⟨194155461532722029586184289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129436974355148019724122859 194155461532722029586184289)
    ·
      refine ⟨145616596149541522189638217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194155461532722029586184289 145616596149541522189638217)
      ·
        refine ⟨109212447112156141642228663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145616596149541522189638217 109212447112156141642228663)
        ·
          refine ⟨163818670668234212463342995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109212447112156141642228663 163818670668234212463342995)
          ·
            refine ⟨245728006002351318695014493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163818670668234212463342995 245728006002351318695014493)
            ·
              refine ⟨92148002250881744510630435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245728006002351318695014493 92148002250881744510630435)
              ·
                refine ⟨138222003376322616765945653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92148002250881744510630435 138222003376322616765945653)
                ·
                  refine ⟨12958312816530245321807405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138222003376322616765945653 12958312816530245321807405)
                  ·
                    refine ⟨4859367306198841995677777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12958312816530245321807405 4859367306198841995677777)
                    ·
                      refine ⟨3644525479649131496758333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859367306198841995677777 3644525479649131496758333)
                      ·
                        rfl

theorem cell23_7097688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_7097688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097688 prefixEnd_7097688 := by exact prefixLift 7097688
  have htrace : WordTrace (prefixWord ++ tailWord_7097688) baseStart_7097688 baseEnd_7097688 := by
    simpa [prefixWord, tailWord_7097688, baseEnd_7097688] using wordTrace_append hprefix tailTrace_7097688
  have hstable : (prefixWord ++ tailWord_7097688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097688).length < 2 ^ (prefixWord ++ tailWord_7097688).sum := by decide
  have hdescent : baseEnd_7097688 < baseStart_7097688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097701 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7097701 : Nat := 118140960795 + 7097701 * 2 ^ 59
def prefixEnd_7097701 : Nat := 4983230072969 + 3 ^ 40 * 7097701 * 2
def baseEnd_7097701 : Nat := 3644532154897639945895773

theorem tailTrace_7097701 : CollatzResearch.WordTrace tailWord_7097701 prefixEnd_7097701 3644532154897639945895773 := by
  unfold tailWord_7097701
  simp only [CollatzResearch.WordTrace]
  refine ⟨258874422859248942668468957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172582948572832628445645971 258874422859248942668468957)
  ·
    refine ⟨97077908572218353500675859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258874422859248942668468957 97077908572218353500675859)
    ·
      refine ⟨145616862858327530251013789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97077908572218353500675859 145616862858327530251013789)
      ·
        refine ⟨54606323571872823844130171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145616862858327530251013789 54606323571872823844130171)
        ·
          refine ⟨81909485357809235766195257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54606323571872823844130171 81909485357809235766195257)
          ·
            refine ⟨61432114018356926824646443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81909485357809235766195257 61432114018356926824646443)
            ·
              refine ⟨92148171027535390236969665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61432114018356926824646443 92148171027535390236969665)
              ·
                refine ⟨69111128270651542677727249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92148171027535390236969665 69111128270651542677727249)
                ·
                  refine ⟨51833346202988657008295437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69111128270651542677727249 51833346202988657008295437)
                  ·
                    refine ⟨19437504826120746378110789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51833346202988657008295437 19437504826120746378110789)
                    ·
                      refine ⟨3644532154897639945895773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19437504826120746378110789 3644532154897639945895773)
                      ·
                        rfl

theorem cell23_7097701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7097701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097701 prefixEnd_7097701 := by exact prefixLift 7097701
  have htrace : WordTrace (prefixWord ++ tailWord_7097701) baseStart_7097701 baseEnd_7097701 := by
    simpa [prefixWord, tailWord_7097701, baseEnd_7097701] using wordTrace_append hprefix tailTrace_7097701
  have hstable : (prefixWord ++ tailWord_7097701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097701).length < 2 ^ (prefixWord ++ tailWord_7097701).sum := by decide
  have hdescent : baseEnd_7097701 < baseStart_7097701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097721 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7097721 : Nat := 118140960795 + 7097721 * 2 ^ 59
def prefixEnd_7097721 : Nat := 4983230072969 + 3 ^ 40 * 7097721 * 2
def baseEnd_7097721 : Nat := 3644542424510729867645681

theorem tailTrace_7097721 : CollatzResearch.WordTrace tailWord_7097721 prefixEnd_7097721 3644542424510729867645681 := by
  unfold tailWord_7097721
  simp only [CollatzResearch.WordTrace]
  refine ⟨258875152319176486084197017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172583434879450990722798011 258875152319176486084197017)
  ·
    refine ⟨194156364239382364563147763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258875152319176486084197017 194156364239382364563147763)
    ·
      refine ⟨291234546359073546844721645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194156364239382364563147763 291234546359073546844721645)
      ·
        refine ⟨109212954884652580066770617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291234546359073546844721645 109212954884652580066770617)
        ·
          refine ⟨81909716163489435050077963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109212954884652580066770617 81909716163489435050077963)
          ·
            refine ⟨122864574245234152575116945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81909716163489435050077963 122864574245234152575116945)
            ·
              refine ⟨92148430683925614431337709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122864574245234152575116945 92148430683925614431337709)
              ·
                refine ⟨34555661506472105411751641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92148430683925614431337709 34555661506472105411751641)
                ·
                  refine ⟨25916746129854079058813731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34555661506472105411751641 25916746129854079058813731)
                  ·
                    refine ⟨38875119194781118588220597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25916746129854079058813731 38875119194781118588220597)
                    ·
                      refine ⟨3644542424510729867645681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38875119194781118588220597 3644542424510729867645681)
                      ·
                        rfl

theorem cell23_7097721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7097721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097721 prefixEnd_7097721 := by exact prefixLift 7097721
  have htrace : WordTrace (prefixWord ++ tailWord_7097721) baseStart_7097721 baseEnd_7097721 := by
    simpa [prefixWord, tailWord_7097721, baseEnd_7097721] using wordTrace_append hprefix tailTrace_7097721
  have hstable : (prefixWord ++ tailWord_7097721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097721).length < 2 ^ (prefixWord ++ tailWord_7097721).sum := by decide
  have hdescent : baseEnd_7097721 < baseStart_7097721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097729 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7097729 : Nat := 118140960795 + 7097729 * 2 ^ 59
def prefixEnd_7097729 : Nat := 4983230072969 + 3 ^ 40 * 7097729 * 2
def baseEnd_7097729 : Nat := 3644546532355965836345645

theorem tailTrace_7097729 : CollatzResearch.WordTrace tailWord_7097729 prefixEnd_7097729 3644546532355965836345645 := by
  unfold tailWord_7097729
  simp only [CollatzResearch.WordTrace]
  refine ⟨258875444103147503450488241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172583629402098335633658827 258875444103147503450488241)
  ·
    refine ⟨194156583077360627587866181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258875444103147503450488241 194156583077360627587866181)
    ·
      refine ⟨36404359327005117672724909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194156583077360627587866181 36404359327005117672724909)
      ·
        refine ⟨13651634747626919127271841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36404359327005117672724909 13651634747626919127271841)
        ·
          refine ⟨10238726060720189345453881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13651634747626919127271841 10238726060720189345453881)
          ·
            refine ⟨7679044545540142009090411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10238726060720189345453881 7679044545540142009090411)
            ·
              refine ⟨11518566818310213013635617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679044545540142009090411 11518566818310213013635617)
              ·
                refine ⟨8638925113732659760226713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11518566818310213013635617 8638925113732659760226713)
                ·
                  refine ⟨6479193835299494820170035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638925113732659760226713 6479193835299494820170035)
                  ·
                    refine ⟨9718790752949242230255053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6479193835299494820170035 9718790752949242230255053)
                    ·
                      refine ⟨3644546532355965836345645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718790752949242230255053 3644546532355965836345645)
                      ·
                        rfl

theorem cell23_7097729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7097729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097729 prefixEnd_7097729 := by exact prefixLift 7097729
  have htrace : WordTrace (prefixWord ++ tailWord_7097729) baseStart_7097729 baseEnd_7097729 := by
    simpa [prefixWord, tailWord_7097729, baseEnd_7097729] using wordTrace_append hprefix tailTrace_7097729
  have hstable : (prefixWord ++ tailWord_7097729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097729).length < 2 ^ (prefixWord ++ tailWord_7097729).sum := by decide
  have hdescent : baseEnd_7097729 < baseStart_7097729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097746 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7097746 : Nat := 118140960795 + 7097746 * 2 ^ 59
def prefixEnd_7097746 : Nat := 4983230072969 + 3 ^ 40 * 7097746 * 2
def baseEnd_7097746 : Nat := 3644555261527092269833067

theorem tailTrace_7097746 : CollatzResearch.WordTrace tailWord_7097746 prefixEnd_7097746 3644555261527092269833067 := by
  unfold tailWord_7097746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64719016036021478838464273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172584042762723943569238061 64719016036021478838464273)
  ·
    refine ⟨48539262027016109128848205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64719016036021478838464273 48539262027016109128848205)
    ·
      refine ⟨18202223260131040923318077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48539262027016109128848205 18202223260131040923318077)
      ·
        refine ⟨6825833722549140346244279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18202223260131040923318077 6825833722549140346244279)
        ·
          refine ⟨10238750583823710519366419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825833722549140346244279 10238750583823710519366419)
          ·
            refine ⟨15358125875735565779049629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238750583823710519366419 15358125875735565779049629)
            ·
              refine ⟨5759297203400837167143611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15358125875735565779049629 5759297203400837167143611)
              ·
                refine ⟨8638945805101255750715417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759297203400837167143611 8638945805101255750715417)
                ·
                  refine ⟨6479209353825941813036563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638945805101255750715417 6479209353825941813036563)
                  ·
                    refine ⟨9718814030738912719554845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6479209353825941813036563 9718814030738912719554845)
                    ·
                      refine ⟨3644555261527092269833067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718814030738912719554845 3644555261527092269833067)
                      ·
                        rfl

theorem cell23_7097746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7097746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097746 prefixEnd_7097746 := by exact prefixLift 7097746
  have htrace : WordTrace (prefixWord ++ tailWord_7097746) baseStart_7097746 baseEnd_7097746 := by
    simpa [prefixWord, tailWord_7097746, baseEnd_7097746] using wordTrace_append hprefix tailTrace_7097746
  have hstable : (prefixWord ++ tailWord_7097746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097746).length < 2 ^ (prefixWord ++ tailWord_7097746).sum := by decide
  have hdescent : baseEnd_7097746 < baseStart_7097746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097825 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_7097825 : Nat := 118140960795 + 7097825 * 2 ^ 59
def prefixEnd_7097825 : Nat := 4983230072969 + 3 ^ 40 * 7097825 * 2
def baseEnd_7097825 : Nat := 3644595826498797460745203

theorem tailTrace_7097825 : CollatzResearch.WordTrace tailWord_7097825 prefixEnd_7097825 3644595826498797460745203 := by
  unfold tailWord_7097825
  simp only [CollatzResearch.WordTrace]
  refine ⟨258878945510799711845982929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172585963673866474563988619 258878945510799711845982929)
  ·
    refine ⟨194159209133099783884487197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258878945510799711845982929 194159209133099783884487197)
    ·
      refine ⟨72809703424912418956682699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194159209133099783884487197 72809703424912418956682699)
      ·
        refine ⟨109214555137368628435024049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72809703424912418956682699 109214555137368628435024049)
        ·
          refine ⟨81910916353026471326268037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109214555137368628435024049 81910916353026471326268037)
          ·
            refine ⟨15358296816192463373675257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81910916353026471326268037 15358296816192463373675257)
            ·
              refine ⟨11518722612144347530256443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15358296816192463373675257 11518722612144347530256443)
              ·
                refine ⟨17278083918216521295384665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518722612144347530256443 17278083918216521295384665)
                ·
                  refine ⟨12958562938662390971538499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17278083918216521295384665 12958562938662390971538499)
                  ·
                    refine ⟨19437844407993586457307749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12958562938662390971538499 19437844407993586457307749)
                    ·
                      refine ⟨3644595826498797460745203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19437844407993586457307749 3644595826498797460745203)
                      ·
                        rfl

theorem cell23_7097825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_7097825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097825 prefixEnd_7097825 := by exact prefixLift 7097825
  have htrace : WordTrace (prefixWord ++ tailWord_7097825) baseStart_7097825 baseEnd_7097825 := by
    simpa [prefixWord, tailWord_7097825, baseEnd_7097825] using wordTrace_append hprefix tailTrace_7097825
  have hstable : (prefixWord ++ tailWord_7097825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097825).length < 2 ^ (prefixWord ++ tailWord_7097825).sum := by decide
  have hdescent : baseEnd_7097825 < baseStart_7097825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097828 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_7097828 : Nat := 118140960795 + 7097828 * 2 ^ 59
def prefixEnd_7097828 : Nat := 4983230072969 + 3 ^ 40 * 7097828 * 2
def baseEnd_7097828 : Nat := 3644597366940760949007689

theorem tailTrace_7097828 : CollatzResearch.WordTrace tailWord_7097828 prefixEnd_7097828 3644597366940760949007689 := by
  unfold tailWord_7097828
  simp only [CollatzResearch.WordTrace]
  refine ⟨129439527464894421679171069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172586036619859228905561425 129439527464894421679171069)
  ·
    refine ⟨48539822799335408129689151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129439527464894421679171069 48539822799335408129689151)
    ·
      refine ⟨72809734199003112194533727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48539822799335408129689151 72809734199003112194533727)
      ·
        refine ⟨109214601298504668291800591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72809734199003112194533727 109214601298504668291800591)
        ·
          refine ⟨163821901947757002437700887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109214601298504668291800591 163821901947757002437700887)
          ·
            refine ⟨245732852921635503656551331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163821901947757002437700887 245732852921635503656551331)
            ·
              refine ⟨368599279382453255484826997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245732852921635503656551331 368599279382453255484826997)
              ·
                refine ⟨34556182442104992701702531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368599279382453255484826997 34556182442104992701702531)
                ·
                  refine ⟨51834273663157489052553797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34556182442104992701702531 51834273663157489052553797)
                  ·
                    refine ⟨9718926311842029197353837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51834273663157489052553797 9718926311842029197353837)
                    ·
                      refine ⟨3644597366940760949007689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718926311842029197353837 3644597366940760949007689)
                      ·
                        rfl

theorem cell23_7097828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_7097828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097828 prefixEnd_7097828 := by exact prefixLift 7097828
  have htrace : WordTrace (prefixWord ++ tailWord_7097828) baseStart_7097828 baseEnd_7097828 := by
    simpa [prefixWord, tailWord_7097828, baseEnd_7097828] using wordTrace_append hprefix tailTrace_7097828
  have hstable : (prefixWord ++ tailWord_7097828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097828).length < 2 ^ (prefixWord ++ tailWord_7097828).sum := by decide
  have hdescent : baseEnd_7097828 < baseStart_7097828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097838 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7097838 : Nat := 118140960795 + 7097838 * 2 ^ 59
def prefixEnd_7097838 : Nat := 4983230072969 + 3 ^ 40 * 7097838 * 2
def baseEnd_7097838 : Nat := 3644602501747305909882643

theorem tailTrace_7097838 : CollatzResearch.WordTrace tailWord_7097838 prefixEnd_7097838 3644602501747305909882643 := by
  unfold tailWord_7097838
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359927457469076883275771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172586279773168410044137445 32359927457469076883275771)
  ·
    refine ⟨48539891186203615324913657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32359927457469076883275771 48539891186203615324913657)
    ·
      refine ⟨36404918389652711493685243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48539891186203615324913657 36404918389652711493685243)
      ·
        refine ⟨54607377584479067240527865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36404918389652711493685243 54607377584479067240527865)
        ·
          refine ⟨40955533188359300430395899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54607377584479067240527865 40955533188359300430395899)
          ·
            refine ⟨61433299782538950645593849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40955533188359300430395899 61433299782538950645593849)
            ·
              refine ⟨46074974836904212984195387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61433299782538950645593849 46074974836904212984195387)
              ·
                refine ⟨69112462255356319476293081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46074974836904212984195387 69112462255356319476293081)
                ·
                  refine ⟨51834346691517239607219811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69112462255356319476293081 51834346691517239607219811)
                  ·
                    refine ⟨77751520037275859410829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51834346691517239607219811 77751520037275859410829717)
                    ·
                      refine ⟨3644602501747305909882643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77751520037275859410829717 3644602501747305909882643)
                      ·
                        rfl

theorem cell23_7097838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7097838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097838 prefixEnd_7097838 := by exact prefixLift 7097838
  have htrace : WordTrace (prefixWord ++ tailWord_7097838) baseStart_7097838 baseEnd_7097838 := by
    simpa [prefixWord, tailWord_7097838, baseEnd_7097838] using wordTrace_append hprefix tailTrace_7097838
  have hstable : (prefixWord ++ tailWord_7097838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097838).length < 2 ^ (prefixWord ++ tailWord_7097838).sum := by decide
  have hdescent : baseEnd_7097838 < baseStart_7097838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097848 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 6]
def baseStart_7097848 : Nat := 118140960795 + 7097848 * 2 ^ 59
def prefixEnd_7097848 : Nat := 4983230072969 + 3 ^ 40 * 7097848 * 2
def baseEnd_7097848 : Nat := 404956404061538985639733

theorem tailTrace_7097848 : CollatzResearch.WordTrace tailWord_7097848 prefixEnd_7097848 404956404061538985639733 := by
  unfold tailWord_7097848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129439892194858193387035099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172586522926477591182713465 129439892194858193387035099)
  ·
    refine ⟨194159838292287290080552649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129439892194858193387035099 194159838292287290080552649)
    ·
      refine ⟨145619878719215467560414487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194159838292287290080552649 145619878719215467560414487)
      ·
        refine ⟨218429818078823201340621731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145619878719215467560414487 218429818078823201340621731)
        ·
          refine ⟨327644727118234802010932597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218429818078823201340621731 327644727118234802010932597)
          ·
            refine ⟨30716693167334512688524931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327644727118234802010932597 30716693167334512688524931)
            ·
              refine ⟨46075039751001769032787397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30716693167334512688524931 46075039751001769032787397)
              ·
                refine ⟨8639069953312831693647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46075039751001769032787397 8639069953312831693647637)
                ·
                  refine ⟨404956404061538985639733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8639069953312831693647637 404956404061538985639733)
                  ·
                    rfl

theorem cell23_7097848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_7097848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097848 prefixEnd_7097848 := by exact prefixLift 7097848
  have htrace : WordTrace (prefixWord ++ tailWord_7097848) baseStart_7097848 baseEnd_7097848 := by
    simpa [prefixWord, tailWord_7097848, baseEnd_7097848] using wordTrace_append hprefix tailTrace_7097848
  have hstable : (prefixWord ++ tailWord_7097848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097848).length < 2 ^ (prefixWord ++ tailWord_7097848).sum := by decide
  have hdescent : baseEnd_7097848 < baseStart_7097848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_7097851 : Nat := 118140960795 + 7097851 * 2 ^ 59
def prefixEnd_7097851 : Nat := 4983230072969 + 3 ^ 40 * 7097851 * 2
def baseEnd_7097851 : Nat := 3644609176995814359020083

theorem tailTrace_7097851 : CollatzResearch.WordTrace tailWord_7097851 prefixEnd_7097851 3644609176995814359020083 := by
  unfold tailWord_7097851
  simp only [CollatzResearch.WordTrace]
  refine ⟨258879893808705518286429407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172586595872470345524286271 258879893808705518286429407)
  ·
    refine ⟨388319840713058277429644111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258879893808705518286429407 388319840713058277429644111)
    ·
      refine ⟨582479761069587416144466167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388319840713058277429644111 582479761069587416144466167)
      ·
        refine ⟨873719641604381124216699251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582479761069587416144466167 873719641604381124216699251)
        ·
          refine ⟨1310579462406571686325048877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873719641604381124216699251 1310579462406571686325048877)
          ·
            refine ⟨491467298402464382371893329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1310579462406571686325048877 491467298402464382371893329)
            ·
              refine ⟨368600473801848286778919997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491467298402464382371893329 368600473801848286778919997)
              ·
                refine ⟨138225177675693107542094999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368600473801848286778919997 138225177675693107542094999)
                ·
                  refine ⟨207337766513539661313142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138225177675693107542094999 207337766513539661313142499)
                  ·
                    refine ⟨311006649770309491969713749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207337766513539661313142499 311006649770309491969713749)
                    ·
                      refine ⟨3644609176995814359020083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311006649770309491969713749 3644609176995814359020083)
                      ·
                        rfl

theorem cell23_7097851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_7097851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097851 prefixEnd_7097851 := by exact prefixLift 7097851
  have htrace : WordTrace (prefixWord ++ tailWord_7097851) baseStart_7097851 baseEnd_7097851 := by
    simpa [prefixWord, tailWord_7097851, baseEnd_7097851] using wordTrace_append hprefix tailTrace_7097851
  have hstable : (prefixWord ++ tailWord_7097851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097851).length < 2 ^ (prefixWord ++ tailWord_7097851).sum := by decide
  have hdescent : baseEnd_7097851 < baseStart_7097851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097875 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 3]
def baseStart_7097875 : Nat := 118140960795 + 7097875 * 2 ^ 59
def prefixEnd_7097875 : Nat := 4983230072969 + 3 ^ 40 * 7097875 * 2
def baseEnd_7097875 : Nat := 3644621500531522265119973

theorem tailTrace_7097875 : CollatzResearch.WordTrace tailWord_7097875 prefixEnd_7097875 3644621500531522265119973 := by
  unfold tailWord_7097875
  simp only [CollatzResearch.WordTrace]
  refine ⟨258880769160618570385303079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172587179440412380256868719 258880769160618570385303079)
  ·
    refine ⟨388321153740927855577954619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258880769160618570385303079 388321153740927855577954619)
    ·
      refine ⟨582481730611391783366931929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388321153740927855577954619 582481730611391783366931929)
      ·
        refine ⟨436861297958543837525198947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582481730611391783366931929 436861297958543837525198947)
        ·
          refine ⟨655291946937815756287798421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436861297958543837525198947 655291946937815756287798421)
          ·
            refine ⟨30716810012710113575990551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 655291946937815756287798421 30716810012710113575990551)
            ·
              refine ⟨46075215019065170363985827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30716810012710113575990551 46075215019065170363985827)
              ·
                refine ⟨69112822528597755545978741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46075215019065170363985827 69112822528597755545978741)
                ·
                  refine ⟨6479327112056039582435507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69112822528597755545978741 6479327112056039582435507)
                  ·
                    refine ⟨9718990668084059373653261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6479327112056039582435507 9718990668084059373653261)
                    ·
                      refine ⟨3644621500531522265119973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9718990668084059373653261 3644621500531522265119973)
                      ·
                        rfl

theorem cell23_7097875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_7097875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097875 prefixEnd_7097875 := by exact prefixLift 7097875
  have htrace : WordTrace (prefixWord ++ tailWord_7097875) baseStart_7097875 baseEnd_7097875 := by
    simpa [prefixWord, tailWord_7097875, baseEnd_7097875] using wordTrace_append hprefix tailTrace_7097875
  have hstable : (prefixWord ++ tailWord_7097875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097875).length < 2 ^ (prefixWord ++ tailWord_7097875).sum := by decide
  have hdescent : baseEnd_7097875 < baseStart_7097875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097876 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7097876 : Nat := 118140960795 + 7097876 * 2 ^ 59
def prefixEnd_7097876 : Nat := 4983230072969 + 3 ^ 40 * 7097876 * 2
def baseEnd_7097876 : Nat := 3644622014012176761207469

theorem tailTrace_7097876 : CollatzResearch.WordTrace tailWord_7097876 prefixEnd_7097876 3644622014012176761207469 := by
  unfold tailWord_7097876
  simp only [CollatzResearch.WordTrace]
  refine ⟨129440402816807473778044741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172587203755743298370726321 129440402816807473778044741)
  ·
    refine ⟨24270075528151401333383389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129440402816807473778044741 24270075528151401333383389)
    ·
      refine ⟨9101278323056775500018771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24270075528151401333383389 9101278323056775500018771)
      ·
        refine ⟨13651917484585163250028157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101278323056775500018771 13651917484585163250028157)
        ·
          refine ⟨5119469056719436218760559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13651917484585163250028157 5119469056719436218760559)
          ·
            refine ⟨7679203585079154328140839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119469056719436218760559 7679203585079154328140839)
            ·
              refine ⟨11518805377618731492211259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679203585079154328140839 11518805377618731492211259)
              ·
                refine ⟨17278208066428097238316889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518805377618731492211259 17278208066428097238316889)
                ·
                  refine ⟨12958656049821072928737667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17278208066428097238316889 12958656049821072928737667)
                  ·
                    refine ⟨19437984074731609393106501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12958656049821072928737667 19437984074731609393106501)
                    ·
                      refine ⟨3644622014012176761207469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19437984074731609393106501 3644622014012176761207469)
                      ·
                        rfl

theorem cell23_7097876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7097876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097876 prefixEnd_7097876 := by exact prefixLift 7097876
  have htrace : WordTrace (prefixWord ++ tailWord_7097876) baseStart_7097876 baseEnd_7097876 := by
    simpa [prefixWord, tailWord_7097876, baseEnd_7097876] using wordTrace_append hprefix tailTrace_7097876
  have hstable : (prefixWord ++ tailWord_7097876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097876).length < 2 ^ (prefixWord ++ tailWord_7097876).sum := by decide
  have hdescent : baseEnd_7097876 < baseStart_7097876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097909 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_7097909 : Nat := 118140960795 + 7097909 * 2 ^ 59
def prefixEnd_7097909 : Nat := 4983230072969 + 3 ^ 40 * 7097909 * 2
def baseEnd_7097909 : Nat := 3644638958873775132094817

theorem tailTrace_7097909 : CollatzResearch.WordTrace tailWord_7097909 prefixEnd_7097909 3644638958873775132094817 := by
  unfold tailWord_7097909
  simp only [CollatzResearch.WordTrace]
  refine ⟨258882009242495394192040781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172588006161663596128027187 258882009242495394192040781)
  ·
    refine ⟨97080753465935772822015293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258882009242495394192040781 97080753465935772822015293)
    ·
      refine ⟨36405282549725914808255735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97080753465935772822015293 36405282549725914808255735)
      ·
        refine ⟨54607923824588872212383603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36405282549725914808255735 54607923824588872212383603)
        ·
          refine ⟨81911885736883308318575405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54607923824588872212383603 81911885736883308318575405)
          ·
            refine ⟨30716957151331240619465777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81911885736883308318575405 30716957151331240619465777)
            ·
              refine ⟨23037717863498430464599333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30716957151331240619465777 23037717863498430464599333)
              ·
                refine ⟨4319572099405955712112375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23037717863498430464599333 4319572099405955712112375)
                ·
                  refine ⟨6479358149108933568168563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319572099405955712112375 6479358149108933568168563)
                  ·
                    refine ⟨9719037223663400352252845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6479358149108933568168563 9719037223663400352252845)
                    ·
                      refine ⟨3644638958873775132094817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719037223663400352252845 3644638958873775132094817)
                      ·
                        rfl

theorem cell23_7097909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_7097909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097909 prefixEnd_7097909 := by exact prefixLift 7097909
  have htrace : WordTrace (prefixWord ++ tailWord_7097909) baseStart_7097909 baseEnd_7097909 := by
    simpa [prefixWord, tailWord_7097909, baseEnd_7097909] using wordTrace_append hprefix tailTrace_7097909
  have hstable : (prefixWord ++ tailWord_7097909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097909).length < 2 ^ (prefixWord ++ tailWord_7097909).sum := by decide
  have hdescent : baseEnd_7097909 < baseStart_7097909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097932 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7097932 : Nat := 118140960795 + 7097932 * 2 ^ 59
def prefixEnd_7097932 : Nat := 4983230072969 + 3 ^ 40 * 7097932 * 2
def baseEnd_7097932 : Nat := 3644650768928828542107211

theorem tailTrace_7097932 : CollatzResearch.WordTrace tailWord_7097932 prefixEnd_7097932 3644650768928828542107211 := by
  unfold tailWord_7097932
  simp only [CollatzResearch.WordTrace]
  refine ⟨129441424060706034560064025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172588565414274712746752033 129441424060706034560064025)
  ·
    refine ⟨97081068045529525920048019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129441424060706034560064025 97081068045529525920048019)
    ·
      refine ⟨145621602068294288880072029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97081068045529525920048019 145621602068294288880072029)
      ·
        refine ⟨54608100775610358330027011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145621602068294288880072029 54608100775610358330027011)
        ·
          refine ⟨81912151163415537495040517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54608100775610358330027011 81912151163415537495040517)
          ·
            refine ⟨15358528343140413280320097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81912151163415537495040517 15358528343140413280320097)
            ·
              refine ⟨11518896257355309960240073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15358528343140413280320097 11518896257355309960240073)
              ·
                refine ⟨8639172193016482470180055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11518896257355309960240073 8639172193016482470180055)
                ·
                  refine ⟨12958758289524723705270083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639172193016482470180055 12958758289524723705270083)
                  ·
                    refine ⟨19438137434287085557905125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12958758289524723705270083 19438137434287085557905125)
                    ·
                      refine ⟨3644650768928828542107211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19438137434287085557905125 3644650768928828542107211)
                      ·
                        rfl

theorem cell23_7097932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7097932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097932 prefixEnd_7097932 := by exact prefixLift 7097932
  have htrace : WordTrace (prefixWord ++ tailWord_7097932) baseStart_7097932 baseEnd_7097932 := by
    simpa [prefixWord, tailWord_7097932, baseEnd_7097932] using wordTrace_append hprefix tailTrace_7097932
  have hstable : (prefixWord ++ tailWord_7097932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097932).length < 2 ^ (prefixWord ++ tailWord_7097932).sum := by decide
  have hdescent : baseEnd_7097932 < baseStart_7097932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097975 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_7097975 : Nat := 118140960795 + 7097975 * 2 ^ 59
def prefixEnd_7097975 : Nat := 4983230072969 + 3 ^ 40 * 7097975 * 2
def baseEnd_7097975 : Nat := 3644672848596971873869513

theorem tailTrace_7097975 : CollatzResearch.WordTrace tailWord_7097975 prefixEnd_7097975 3644672848596971873869513 := by
  unfold tailWord_7097975
  simp only [CollatzResearch.WordTrace]
  refine ⟨258884416460256287463943379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172589610973504191642628919 258884416460256287463943379)
  ·
    refine ⟨388326624690384431195915069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258884416460256287463943379 388326624690384431195915069)
    ·
      refine ⟨145622484258894161698468151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388326624690384431195915069 145622484258894161698468151)
      ·
        refine ⟨218433726388341242547702227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145622484258894161698468151 218433726388341242547702227)
        ·
          refine ⟨327650589582511863821553341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218433726388341242547702227 327650589582511863821553341)
          ·
            refine ⟨122868971093441948933082503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327650589582511863821553341 122868971093441948933082503)
            ·
              refine ⟨184303456640162923399623755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122868971093441948933082503 184303456640162923399623755)
              ·
                refine ⟨276455184960244385099435633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184303456640162923399623755 276455184960244385099435633)
                ·
                  refine ⟨207341388720183288824576725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276455184960244385099435633 207341388720183288824576725)
                  ·
                    refine ⟨4859563798129295831826017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207341388720183288824576725 4859563798129295831826017)
                    ·
                      refine ⟨3644672848596971873869513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859563798129295831826017 3644672848596971873869513)
                      ·
                        rfl

theorem cell23_7097975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_7097975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097975 prefixEnd_7097975 := by exact prefixLift 7097975
  have htrace : WordTrace (prefixWord ++ tailWord_7097975) baseStart_7097975 baseEnd_7097975 := by
    simpa [prefixWord, tailWord_7097975, baseEnd_7097975] using wordTrace_append hprefix tailTrace_7097975
  have hstable : (prefixWord ++ tailWord_7097975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097975).length < 2 ^ (prefixWord ++ tailWord_7097975).sum := by decide
  have hdescent : baseEnd_7097975 < baseStart_7097975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097978 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_7097978 : Nat := 118140960795 + 7097978 * 2 ^ 59
def prefixEnd_7097978 : Nat := 4983230072969 + 3 ^ 40 * 7097978 * 2
def baseEnd_7097978 : Nat := 3644674389038935362131999

theorem tailTrace_7097978 : CollatzResearch.WordTrace tailWord_7097978 prefixEnd_7097978 3644674389038935362131999 := by
  unfold tailWord_7097978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64721131469811354744075647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172589683919496945984201725 64721131469811354744075647)
  ·
    refine ⟨97081697204717032116113471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64721131469811354744075647 97081697204717032116113471)
    ·
      refine ⟨145622545807075548174170207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97081697204717032116113471 145622545807075548174170207)
      ·
        refine ⟨218433818710613322261255311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145622545807075548174170207 218433818710613322261255311)
        ·
          refine ⟨327650728065919983391882967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218433818710613322261255311 327650728065919983391882967)
          ·
            refine ⟨491476092098879975087824451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327650728065919983391882967 491476092098879975087824451)
            ·
              refine ⟨737214138148319962631736677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491476092098879975087824451 737214138148319962631736677)
              ·
                refine ⟨138227650902809992993450627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737214138148319962631736677 138227650902809992993450627)
                ·
                  refine ⟨207341476354214989490175941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138227650902809992993450627 207341476354214989490175941)
                  ·
                    refine ⟨38876526816415310529407989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207341476354214989490175941 38876526816415310529407989)
                    ·
                      refine ⟨3644674389038935362131999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38876526816415310529407989 3644674389038935362131999)
                      ·
                        rfl

theorem cell23_7097978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_7097978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7097978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7097978 prefixEnd_7097978 := by exact prefixLift 7097978
  have htrace : WordTrace (prefixWord ++ tailWord_7097978) baseStart_7097978 baseEnd_7097978 := by
    simpa [prefixWord, tailWord_7097978, baseEnd_7097978] using wordTrace_append hprefix tailTrace_7097978
  have hstable : (prefixWord ++ tailWord_7097978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097978).length < 2 ^ (prefixWord ++ tailWord_7097978).sum := by decide
  have hdescent : baseEnd_7097978 < baseStart_7097978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098028 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 13]
def baseStart_7098028 : Nat := 118140960795 + 7098028 * 2 ^ 59
def prefixEnd_7098028 : Nat := 4983230072969 + 3 ^ 40 * 7098028 * 2
def baseEnd_7098028 : Nat := 404966673674628907389641

theorem tailTrace_7098028 : CollatzResearch.WordTrace tailWord_7098028 prefixEnd_7098028 404966673674628907389641 := by
  unfold tailWord_7098028
  simp only [CollatzResearch.WordTrace]
  refine ⟨129443174764532138757811369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172590899686042851677081825 129443174764532138757811369)
  ·
    refine ⟨97082381073399104068358527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129443174764532138757811369 97082381073399104068358527)
    ·
      refine ⟨145623571610098656102537791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97082381073399104068358527 145623571610098656102537791)
      ·
        refine ⟨218435357415147984153806687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145623571610098656102537791 218435357415147984153806687)
        ·
          refine ⟨327653036122721976230710031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218435357415147984153806687 327653036122721976230710031)
          ·
            refine ⟨491479554184082964346065047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327653036122721976230710031 491479554184082964346065047)
            ·
              refine ⟨737219331276124446519097571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491479554184082964346065047 737219331276124446519097571)
              ·
                refine ⟨1105828996914186669778646357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737219331276124446519097571 1105828996914186669778646357)
                ·
                  refine ⟨404966673674628907389641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1105828996914186669778646357 404966673674628907389641)
                  ·
                    rfl

theorem cell23_7098028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_7098028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098028 prefixEnd_7098028 := by exact prefixLift 7098028
  have htrace : WordTrace (prefixWord ++ tailWord_7098028) baseStart_7098028 baseEnd_7098028 := by
    simpa [prefixWord, tailWord_7098028, baseEnd_7098028] using wordTrace_append hprefix tailTrace_7098028
  have hstable : (prefixWord ++ tailWord_7098028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098028).length < 2 ^ (prefixWord ++ tailWord_7098028).sum := by decide
  have hdescent : baseEnd_7098028 < baseStart_7098028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098035 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_7098035 : Nat := 118140960795 + 7098035 * 2 ^ 59
def prefixEnd_7098035 : Nat := 4983230072969 + 3 ^ 40 * 7098035 * 2
def baseEnd_7098035 : Nat := 3644703657436241639119237

theorem tailTrace_7098035 : CollatzResearch.WordTrace tailWord_7098035 prefixEnd_7098035 3644703657436241639119237 := by
  unfold tailWord_7098035
  simp only [CollatzResearch.WordTrace]
  refine ⟨258886604840038917711127559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172591069893359278474085039 258886604840038917711127559)
  ·
    refine ⟨388329907260058376566691339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258886604840038917711127559 388329907260058376566691339)
    ·
      refine ⟨582494860890087564850037009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388329907260058376566691339 582494860890087564850037009)
      ·
        refine ⟨436871145667565673637527757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582494860890087564850037009 436871145667565673637527757)
        ·
          refine ⟨163826679625337127614072909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436871145667565673637527757 163826679625337127614072909)
          ·
            refine ⟨61435004859501422855277341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163826679625337127614072909 61435004859501422855277341)
            ·
              refine ⟨23038126822313033570729003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61435004859501422855277341 23038126822313033570729003)
              ·
                refine ⟨34557190233469550356093505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23038126822313033570729003 34557190233469550356093505)
                ·
                  refine ⟨25917892675102162767070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34557190233469550356093505 25917892675102162767070129)
                  ·
                    refine ⟨19438419506326622075302597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25917892675102162767070129 19438419506326622075302597)
                    ·
                      refine ⟨3644703657436241639119237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19438419506326622075302597 3644703657436241639119237)
                      ·
                        rfl

theorem cell23_7098035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_7098035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098035 prefixEnd_7098035 := by exact prefixLift 7098035
  have htrace : WordTrace (prefixWord ++ tailWord_7098035) baseStart_7098035 baseEnd_7098035 := by
    simpa [prefixWord, tailWord_7098035, baseEnd_7098035] using wordTrace_append hprefix tailTrace_7098035
  have hstable : (prefixWord ++ tailWord_7098035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098035).length < 2 ^ (prefixWord ++ tailWord_7098035).sum := by decide
  have hdescent : baseEnd_7098035 < baseStart_7098035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098039 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_7098039 : Nat := 118140960795 + 7098039 * 2 ^ 59
def prefixEnd_7098039 : Nat := 4983230072969 + 3 ^ 40 * 7098039 * 2
def baseEnd_7098039 : Nat := 3644705711358859623469219

theorem tailTrace_7098039 : CollatzResearch.WordTrace tailWord_7098039 prefixEnd_7098039 3644705711358859623469219 := by
  unfold tailWord_7098039
  simp only [CollatzResearch.WordTrace]
  refine ⟨258886750732024426394273171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172591167154682950929515447 258886750732024426394273171)
  ·
    refine ⟨388330126098036639591409757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258886750732024426394273171 388330126098036639591409757)
    ·
      refine ⟨145623797286763739846778659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388330126098036639591409757 145623797286763739846778659)
      ·
        refine ⟨218435695930145609770167989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145623797286763739846778659 218435695930145609770167989)
        ·
          refine ⟨20478346493451150915953249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218435695930145609770167989 20478346493451150915953249)
          ·
            refine ⟨15358759870088363186964937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20478346493451150915953249 15358759870088363186964937)
            ·
              refine ⟨11519069902566272390223703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15358759870088363186964937 11519069902566272390223703)
              ·
                refine ⟨17278604853849408585335555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519069902566272390223703 17278604853849408585335555)
                ·
                  refine ⟨25917907280774112878003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17278604853849408585335555 25917907280774112878003333)
                  ·
                    refine ⟨4859607615145146164625625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25917907280774112878003333 4859607615145146164625625)
                    ·
                      refine ⟨3644705711358859623469219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859607615145146164625625 3644705711358859623469219)
                      ·
                        rfl

theorem cell23_7098039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_7098039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098039 prefixEnd_7098039 := by exact prefixLift 7098039
  have htrace : WordTrace (prefixWord ++ tailWord_7098039) baseStart_7098039 baseEnd_7098039 := by
    simpa [prefixWord, tailWord_7098039, baseEnd_7098039] using wordTrace_append hprefix tailTrace_7098039
  have hstable : (prefixWord ++ tailWord_7098039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098039).length < 2 ^ (prefixWord ++ tailWord_7098039).sum := by decide
  have hdescent : baseEnd_7098039 < baseStart_7098039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098045 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 7]
def baseStart_7098045 : Nat := 118140960795 + 7098045 * 2 ^ 59
def prefixEnd_7098045 : Nat := 4983230072969 + 3 ^ 40 * 7098045 * 2
def baseEnd_7098045 : Nat := 404967643582531844443799

theorem tailTrace_7098045 : CollatzResearch.WordTrace tailWord_7098045 prefixEnd_7098045 404967643582531844443799 := by
  unfold tailWord_7098045
  simp only [CollatzResearch.WordTrace]
  refine ⟨258886969570002689418991589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172591313046668459612661059 258886969570002689418991589)
  ·
    refine ⟨48541306794375504266060923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258886969570002689418991589 48541306794375504266060923)
    ·
      refine ⟨72811960191563256399091385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48541306794375504266060923 72811960191563256399091385)
      ·
        refine ⟨54608970143672442299318539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72811960191563256399091385 54608970143672442299318539)
        ·
          refine ⟨81913455215508663448977809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54608970143672442299318539 81913455215508663448977809)
          ·
            refine ⟨61435091411631497586733357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81913455215508663448977809 61435091411631497586733357)
            ·
              refine ⟨23038159279361811595025009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61435091411631497586733357 23038159279361811595025009)
              ·
                refine ⟨17278619459521358696268757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23038159279361811595025009 17278619459521358696268757)
                ·
                  refine ⟨404967643582531844443799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17278619459521358696268757 404967643582531844443799)
                  ·
                    rfl

theorem cell23_7098045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_7098045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098045 prefixEnd_7098045 := by exact prefixLift 7098045
  have htrace : WordTrace (prefixWord ++ tailWord_7098045) baseStart_7098045 baseEnd_7098045 := by
    simpa [prefixWord, tailWord_7098045, baseEnd_7098045] using wordTrace_append hprefix tailTrace_7098045
  have hstable : (prefixWord ++ tailWord_7098045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098045).length < 2 ^ (prefixWord ++ tailWord_7098045).sum := by decide
  have hdescent : baseEnd_7098045 < baseStart_7098045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098055 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_7098055 : Nat := 118140960795 + 7098055 * 2 ^ 59
def prefixEnd_7098055 : Nat := 4983230072969 + 3 ^ 40 * 7098055 * 2
def baseEnd_7098055 : Nat := 3644713927049331560869145

theorem tailTrace_7098055 : CollatzResearch.WordTrace tailWord_7098055 prefixEnd_7098055 3644713927049331560869145 := by
  unfold tailWord_7098055
  simp only [CollatzResearch.WordTrace]
  refine ⟨258887334299966461126855619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172591556199977640751237079 258887334299966461126855619)
  ·
    refine ⟨388331001449949691690283429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258887334299966461126855619 388331001449949691690283429)
    ·
      refine ⟨72812062771865567191928143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388331001449949691690283429 72812062771865567191928143)
      ·
        refine ⟨109218094157798350787892215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72812062771865567191928143 109218094157798350787892215)
        ·
          refine ⟨163827141236697526181838323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109218094157798350787892215 163827141236697526181838323)
          ·
            refine ⟨245740711855046289272757485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163827141236697526181838323 245740711855046289272757485)
            ·
              refine ⟨92152766945642358477284057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245740711855046289272757485 92152766945642358477284057)
              ·
                refine ⟨69114575209231768857963043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92152766945642358477284057 69114575209231768857963043)
                ·
                  refine ⟨103671862813847653286944565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69114575209231768857963043 103671862813847653286944565)
                  ·
                    refine ⟨9719237138798217495651053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103671862813847653286944565 9719237138798217495651053)
                    ·
                      refine ⟨3644713927049331560869145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719237138798217495651053 3644713927049331560869145)
                      ·
                        rfl

theorem cell23_7098055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_7098055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098055 prefixEnd_7098055 := by exact prefixLift 7098055
  have htrace : WordTrace (prefixWord ++ tailWord_7098055) baseStart_7098055 baseEnd_7098055 := by
    simpa [prefixWord, tailWord_7098055, baseEnd_7098055] using wordTrace_append hprefix tailTrace_7098055
  have hstable : (prefixWord ++ tailWord_7098055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098055).length < 2 ^ (prefixWord ++ tailWord_7098055).sum := by decide
  have hdescent : baseEnd_7098055 < baseStart_7098055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098060 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7098060 : Nat := 118140960795 + 7098060 * 2 ^ 59
def prefixEnd_7098060 : Nat := 4983230072969 + 3 ^ 40 * 7098060 * 2
def baseEnd_7098060 : Nat := 3644716494452604041306623

theorem tailTrace_7098060 : CollatzResearch.WordTrace tailWord_7098060 prefixEnd_7098060 3644716494452604041306623 := by
  unfold tailWord_7098060
  simp only [CollatzResearch.WordTrace]
  refine ⟨129443758332474173490393817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172591677776632231320525089 129443758332474173490393817)
  ·
    refine ⟨97082818749355630117795363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129443758332474173490393817 97082818749355630117795363)
    ·
      refine ⟨145624228124033445176693045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97082818749355630117795363 145624228124033445176693045)
      ·
        refine ⟨13652271386628135485314973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145624228124033445176693045 13652271386628135485314973)
        ·
          refine ⟨5119601769985550806993115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13652271386628135485314973 5119601769985550806993115)
          ·
            refine ⟨7679402654978326210489673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119601769985550806993115 7679402654978326210489673)
            ·
              refine ⟨5759551991233744657867255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7679402654978326210489673 5759551991233744657867255)
              ·
                refine ⟨8639327986850616986800883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759551991233744657867255 8639327986850616986800883)
                ·
                  refine ⟨12958991980275925480201325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639327986850616986800883 12958991980275925480201325)
                  ·
                    refine ⟨4859621992603472055075497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12958991980275925480201325 4859621992603472055075497)
                    ·
                      refine ⟨3644716494452604041306623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859621992603472055075497 3644716494452604041306623)
                      ·
                        rfl

theorem cell23_7098060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7098060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098060 prefixEnd_7098060 := by exact prefixLift 7098060
  have htrace : WordTrace (prefixWord ++ tailWord_7098060) baseStart_7098060 baseEnd_7098060 := by
    simpa [prefixWord, tailWord_7098060, baseEnd_7098060] using wordTrace_append hprefix tailTrace_7098060
  have hstable : (prefixWord ++ tailWord_7098060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098060).length < 2 ^ (prefixWord ++ tailWord_7098060).sum := by decide
  have hdescent : baseEnd_7098060 < baseStart_7098060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098085 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7098085 : Nat := 118140960795 + 7098085 * 2 ^ 59
def prefixEnd_7098085 : Nat := 4983230072969 + 3 ^ 40 * 7098085 * 2
def baseEnd_7098085 : Nat := 3644729331468966443494007

theorem tailTrace_7098085 : CollatzResearch.WordTrace tailWord_7098085 prefixEnd_7098085 3644729331468966443494007 := by
  unfold tailWord_7098085
  simp only [CollatzResearch.WordTrace]
  refine ⟨258888428489857776250447709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172592285659905184166965139 258888428489857776250447709)
  ·
    refine ⟨97083160683696666093917891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258888428489857776250447709 97083160683696666093917891)
    ·
      refine ⟨145624741025544999140876837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97083160683696666093917891 145624741025544999140876837)
      ·
        refine ⟨27304638942289687338914407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145624741025544999140876837 27304638942289687338914407)
        ·
          refine ⟨40956958413434531008371611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27304638942289687338914407 40956958413434531008371611)
          ·
            refine ⟨61435437620151796512557417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40956958413434531008371611 61435437620151796512557417)
            ·
              refine ⟨46076578215113847384418063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61435437620151796512557417 46076578215113847384418063)
              ·
                refine ⟨69114867322670771076627095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46076578215113847384418063 69114867322670771076627095)
                ·
                  refine ⟨103672300984006156614940643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69114867322670771076627095 103672300984006156614940643)
                  ·
                    refine ⟨155508451476009234922410965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103672300984006156614940643 155508451476009234922410965)
                    ·
                      refine ⟨3644729331468966443494007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155508451476009234922410965 3644729331468966443494007)
                      ·
                        rfl

theorem cell23_7098085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7098085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098085 prefixEnd_7098085 := by exact prefixLift 7098085
  have htrace : WordTrace (prefixWord ++ tailWord_7098085) baseStart_7098085 baseEnd_7098085 := by
    simpa [prefixWord, tailWord_7098085, baseEnd_7098085] using wordTrace_append hprefix tailTrace_7098085
  have hstable : (prefixWord ++ tailWord_7098085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098085).length < 2 ^ (prefixWord ++ tailWord_7098085).sum := by decide
  have hdescent : baseEnd_7098085 < baseStart_7098085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098095 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_7098095 : Nat := 118140960795 + 7098095 * 2 ^ 59
def prefixEnd_7098095 : Nat := 4983230072969 + 3 ^ 40 * 7098095 * 2
def baseEnd_7098095 : Nat := 3644734466275511404368961

theorem tailTrace_7098095 : CollatzResearch.WordTrace tailWord_7098095 prefixEnd_7098095 3644734466275511404368961 := by
  unfold tailWord_7098095
  simp only [CollatzResearch.WordTrace]
  refine ⟨258888793219821547958311739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172592528813214365305541159 258888793219821547958311739)
  ·
    refine ⟨388333189829732321937467609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258888793219821547958311739 388333189829732321937467609)
    ·
      refine ⟨291249892372299241453100707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388333189829732321937467609 291249892372299241453100707)
      ·
        refine ⟨436874838558448862179651061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291249892372299241453100707 436874838558448862179651061)
        ·
          refine ⟨40957016114854580829342287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 436874838558448862179651061 40957016114854580829342287)
          ·
            refine ⟨61435524172281871244013431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40957016114854580829342287 61435524172281871244013431)
            ·
              refine ⟨92153286258422806866020147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61435524172281871244013431 92153286258422806866020147)
              ·
                refine ⟨138229929387634210299030221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92153286258422806866020147 138229929387634210299030221)
                ·
                  refine ⟨51836223520362828862136333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138229929387634210299030221 51836223520362828862136333)
                  ·
                    refine ⟨19438583820136060823301125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51836223520362828862136333 19438583820136060823301125)
                    ·
                      refine ⟨3644734466275511404368961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19438583820136060823301125 3644734466275511404368961)
                      ·
                        rfl

theorem cell23_7098095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_7098095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098095 prefixEnd_7098095 := by exact prefixLift 7098095
  have htrace : WordTrace (prefixWord ++ tailWord_7098095) baseStart_7098095 baseEnd_7098095 := by
    simpa [prefixWord, tailWord_7098095, baseEnd_7098095] using wordTrace_append hprefix tailTrace_7098095
  have hstable : (prefixWord ++ tailWord_7098095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098095).length < 2 ^ (prefixWord ++ tailWord_7098095).sum := by decide
  have hdescent : baseEnd_7098095 < baseStart_7098095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098166 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7098166 : Nat := 118140960795 + 7098166 * 2 ^ 59
def prefixEnd_7098166 : Nat := 4983230072969 + 3 ^ 40 * 7098166 * 2
def baseEnd_7098166 : Nat := 3644770923401980626581135

theorem tailTrace_7098166 : CollatzResearch.WordTrace tailWord_7098166 prefixEnd_7098166 3644770923401980626581135 := by
  unfold tailWord_7098166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180711425160270442759147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172594255201709551389430901 16180711425160270442759147)
  ·
    refine ⟨24271067137740405664138721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16180711425160270442759147 24271067137740405664138721)
    ·
      refine ⟨18203300353305304248104041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24271067137740405664138721 18203300353305304248104041)
      ·
        refine ⟨13652475264978978186078031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18203300353305304248104041 13652475264978978186078031)
        ·
          refine ⟨20478712897468467279117047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13652475264978978186078031 20478712897468467279117047)
          ·
            refine ⟨30718069346202700918675571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20478712897468467279117047 30718069346202700918675571)
            ·
              refine ⟨46077104019304051378013357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30718069346202700918675571 46077104019304051378013357)
              ·
                refine ⟨17278914007239019266755009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46077104019304051378013357 17278914007239019266755009)
                ·
                  refine ⟨12959185505429264450066257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17278914007239019266755009 12959185505429264450066257)
                  ·
                    refine ⟨9719389129071948337549693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12959185505429264450066257 9719389129071948337549693)
                    ·
                      refine ⟨3644770923401980626581135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719389129071948337549693 3644770923401980626581135)
                      ·
                        rfl

theorem cell23_7098166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7098166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098166 prefixEnd_7098166 := by exact prefixLift 7098166
  have htrace : WordTrace (prefixWord ++ tailWord_7098166) baseStart_7098166 baseEnd_7098166 := by
    simpa [prefixWord, tailWord_7098166, baseEnd_7098166] using wordTrace_append hprefix tailTrace_7098166
  have hstable : (prefixWord ++ tailWord_7098166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098166).length < 2 ^ (prefixWord ++ tailWord_7098166).sum := by decide
  have hdescent : baseEnd_7098166 < baseStart_7098166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098202 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_7098202 : Nat := 118140960795 + 7098202 * 2 ^ 59
def prefixEnd_7098202 : Nat := 4983230072969 + 3 ^ 40 * 7098202 * 2
def baseEnd_7098202 : Nat := 3644789408705542485730969

theorem tailTrace_7098202 : CollatzResearch.WordTrace tailWord_7098202 prefixEnd_7098202 3644789408705542485730969 := by
  unfold tailWord_7098202
  simp only [CollatzResearch.WordTrace]
  refine ⟨64723173957608476308114215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172595130553622603488304573 64723173957608476308114215)
  ·
    refine ⟨97084760936412714462171323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64723173957608476308114215 97084760936412714462171323)
    ·
      refine ⟨145627141404619071693256985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97084760936412714462171323 145627141404619071693256985)
      ·
        refine ⟨109220356053464303769942739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145627141404619071693256985 109220356053464303769942739)
        ·
          refine ⟨163830534080196455654914109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109220356053464303769942739 163830534080196455654914109)
          ·
            refine ⟨61436450280073670870592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163830534080196455654914109 61436450280073670870592791)
            ·
              refine ⟨92154675420110506305889187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61436450280073670870592791 92154675420110506305889187)
              ·
                refine ⟨138232013130165759458833781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92154675420110506305889187 138232013130165759458833781)
                ·
                  refine ⟨12959251230953039949265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138232013130165759458833781 12959251230953039949265667)
                  ·
                    refine ⟨19438876846429559923898501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12959251230953039949265667 19438876846429559923898501)
                    ·
                      refine ⟨3644789408705542485730969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19438876846429559923898501 3644789408705542485730969)
                      ·
                        rfl

theorem cell23_7098202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_7098202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098202 prefixEnd_7098202 := by exact prefixLift 7098202
  have htrace : WordTrace (prefixWord ++ tailWord_7098202) baseStart_7098202 baseEnd_7098202 := by
    simpa [prefixWord, tailWord_7098202, baseEnd_7098202] using wordTrace_append hprefix tailTrace_7098202
  have hstable : (prefixWord ++ tailWord_7098202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098202).length < 2 ^ (prefixWord ++ tailWord_7098202).sum := by decide
  have hdescent : baseEnd_7098202 < baseStart_7098202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098229 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7098229 : Nat := 118140960795 + 7098229 * 2 ^ 59
def prefixEnd_7098229 : Nat := 4983230072969 + 3 ^ 40 * 7098229 * 2
def baseEnd_7098229 : Nat := 1214934424227737960031115

theorem tailTrace_7098229 : CollatzResearch.WordTrace tailWord_7098229 prefixEnd_7098229 1214934424227737960031115 := by
  unfold tailWord_7098229
  simp only [CollatzResearch.WordTrace]
  refine ⟨258893680601336088843689741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172595787067557392562459827 258893680601336088843689741)
  ·
    refine ⟨97085130225501033316383653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258893680601336088843689741 97085130225501033316383653)
    ·
      refine ⟨18203461917281443746821935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97085130225501033316383653 18203461917281443746821935)
      ·
        refine ⟨27305192875922165620232903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18203461917281443746821935 27305192875922165620232903)
        ·
          refine ⟨40957789313883248430349355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27305192875922165620232903 40957789313883248430349355)
          ·
            refine ⟨61436683970824872645524033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40957789313883248430349355 61436683970824872645524033)
            ·
              refine ⟨46077512978118654484143025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61436683970824872645524033 46077512978118654484143025)
              ·
                refine ⟨34558134733588990863107269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46077512978118654484143025 34558134733588990863107269)
                ·
                  refine ⟨6479650262547935786832613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34558134733588990863107269 6479650262547935786832613)
                  ·
                    refine ⟨1214934424227737960031115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479650262547935786832613 1214934424227737960031115)
                    ·
                      rfl

theorem cell23_7098229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7098229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098229 prefixEnd_7098229 := by exact prefixLift 7098229
  have htrace : WordTrace (prefixWord ++ tailWord_7098229) baseStart_7098229 baseEnd_7098229 := by
    simpa [prefixWord, tailWord_7098229, baseEnd_7098229] using wordTrace_append hprefix tailTrace_7098229
  have hstable : (prefixWord ++ tailWord_7098229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098229).length < 2 ^ (prefixWord ++ tailWord_7098229).sum := by decide
  have hdescent : baseEnd_7098229 < baseStart_7098229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098266 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7098266 : Nat := 118140960795 + 7098266 * 2 ^ 59
def prefixEnd_7098266 : Nat := 4983230072969 + 3 ^ 40 * 7098266 * 2
def baseEnd_7098266 : Nat := 3644822271467430235330675

theorem tailTrace_7098266 : CollatzResearch.WordTrace tailWord_7098266 prefixEnd_7098266 3644822271467430235330675 := by
  unfold tailWord_7098266
  simp only [CollatzResearch.WordTrace]
  refine ⟨64723757525550511040696663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172596686734801362775191101 64723757525550511040696663)
  ·
    refine ⟨97085636288325766561044995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64723757525550511040696663 97085636288325766561044995)
    ·
      refine ⟨145628454432488649841567493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97085636288325766561044995 145628454432488649841567493)
      ·
        refine ⟨27305335206091621845293905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145628454432488649841567493 27305335206091621845293905)
        ·
          refine ⟨20479001404568716383970429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27305335206091621845293905 20479001404568716383970429)
          ·
            refine ⟨7679625526713268643988911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20479001404568716383970429 7679625526713268643988911)
            ·
              refine ⟨11519438290069902965983367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679625526713268643988911 11519438290069902965983367)
              ·
                refine ⟨17279157435104854448975051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519438290069902965983367 17279157435104854448975051)
                ·
                  refine ⟨25918736152657281673462577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17279157435104854448975051 25918736152657281673462577)
                  ·
                    refine ⟨19439052114492961255096933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25918736152657281673462577 19439052114492961255096933)
                    ·
                      refine ⟨3644822271467430235330675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19439052114492961255096933 3644822271467430235330675)
                      ·
                        rfl

theorem cell23_7098266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7098266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098266 prefixEnd_7098266 := by exact prefixLift 7098266
  have htrace : WordTrace (prefixWord ++ tailWord_7098266) baseStart_7098266 baseEnd_7098266 := by
    simpa [prefixWord, tailWord_7098266, baseEnd_7098266] using wordTrace_append hprefix tailTrace_7098266
  have hstable : (prefixWord ++ tailWord_7098266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098266).length < 2 ^ (prefixWord ++ tailWord_7098266).sum := by decide
  have hdescent : baseEnd_7098266 < baseStart_7098266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098270 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7098270 : Nat := 118140960795 + 7098270 * 2 ^ 59
def prefixEnd_7098270 : Nat := 4983230072969 + 3 ^ 40 * 7098270 * 2
def baseEnd_7098270 : Nat := 3644824325390048219680657

theorem tailTrace_7098270 : CollatzResearch.WordTrace tailWord_7098270 prefixEnd_7098270 3644824325390048219680657 := by
  unfold tailWord_7098270
  simp only [CollatzResearch.WordTrace]
  refine ⟨32361896999273444105741533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172596783996125035230621509 32361896999273444105741533)
  ·
    refine ⟨12135711374727541539653075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32361896999273444105741533 12135711374727541539653075)
    ·
      refine ⟨18203567062091312309479613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12135711374727541539653075 18203567062091312309479613)
      ·
        refine ⟨6826337648284242116054855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18203567062091312309479613 6826337648284242116054855)
        ·
          refine ⟨10239506472426363174082283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826337648284242116054855 10239506472426363174082283)
          ·
            refine ⟨15359259708639544761123425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239506472426363174082283 15359259708639544761123425)
            ·
              refine ⟨11519444781479658570842569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15359259708639544761123425 11519444781479658570842569)
              ·
                refine ⟨8639583586109743928131927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11519444781479658570842569 8639583586109743928131927)
                ·
                  refine ⟨12959375379164615892197891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639583586109743928131927 12959375379164615892197891)
                  ·
                    refine ⟨19439063068746923838296837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12959375379164615892197891 19439063068746923838296837)
                    ·
                      refine ⟨3644824325390048219680657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19439063068746923838296837 3644824325390048219680657)
                      ·
                        rfl

theorem cell23_7098270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7098270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098270 prefixEnd_7098270 := by exact prefixLift 7098270
  have htrace : WordTrace (prefixWord ++ tailWord_7098270) baseStart_7098270 baseEnd_7098270 := by
    simpa [prefixWord, tailWord_7098270, baseEnd_7098270] using wordTrace_append hprefix tailTrace_7098270
  have hstable : (prefixWord ++ tailWord_7098270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098270).length < 2 ^ (prefixWord ++ tailWord_7098270).sum := by decide
  have hdescent : baseEnd_7098270 < baseStart_7098270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098273 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7098273 : Nat := 118140960795 + 7098273 * 2 ^ 59
def prefixEnd_7098273 : Nat := 4983230072969 + 3 ^ 40 * 7098273 * 2
def baseEnd_7098273 : Nat := 3644825865832011707943143

theorem tailTrace_7098273 : CollatzResearch.WordTrace tailWord_7098273 prefixEnd_7098273 3644825865832011707943143 := by
  unfold tailWord_7098273
  simp only [CollatzResearch.WordTrace]
  refine ⟨258895285413176684358291473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172596856942117789572194315 258895285413176684358291473)
  ·
    refine ⟨194171464059882513268718605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258895285413176684358291473 194171464059882513268718605)
    ·
      refine ⟨72814299022455942475769477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194171464059882513268718605 72814299022455942475769477)
      ·
        refine ⟨13652681066710489214206777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72814299022455942475769477 13652681066710489214206777)
        ·
          refine ⟨10239510800032866910655083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13652681066710489214206777 10239510800032866910655083)
          ·
            refine ⟨15359266200049300365982625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239510800032866910655083 15359266200049300365982625)
            ·
              refine ⟨11519449650036975274486969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15359266200049300365982625 11519449650036975274486969)
              ·
                refine ⟨8639587237527731455865227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11519449650036975274486969 8639587237527731455865227)
                ·
                  refine ⟨12959380856291597183797841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639587237527731455865227 12959380856291597183797841)
                  ·
                    refine ⟨9719535642218697887848381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12959380856291597183797841 9719535642218697887848381)
                    ·
                      refine ⟨3644825865832011707943143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719535642218697887848381 3644825865832011707943143)
                      ·
                        rfl

theorem cell23_7098273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7098273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098273 prefixEnd_7098273 := by exact prefixLift 7098273
  have htrace : WordTrace (prefixWord ++ tailWord_7098273) baseStart_7098273 baseEnd_7098273 := by
    simpa [prefixWord, tailWord_7098273, baseEnd_7098273] using wordTrace_append hprefix tailTrace_7098273
  have hstable : (prefixWord ++ tailWord_7098273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098273).length < 2 ^ (prefixWord ++ tailWord_7098273).sum := by decide
  have hdescent : baseEnd_7098273 < baseStart_7098273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098296 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_7098296 : Nat := 118140960795 + 7098296 * 2 ^ 59
def prefixEnd_7098296 : Nat := 4983230072969 + 3 ^ 40 * 7098296 * 2
def baseEnd_7098296 : Nat := 3644837675887065117955537

theorem tailTrace_7098296 : CollatzResearch.WordTrace tailWord_7098296 prefixEnd_7098296 3644837675887065117955537 := by
  unfold tailWord_7098296
  simp only [CollatzResearch.WordTrace]
  refine ⟨129448062146046679643189371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172597416194728906190919161 129448062146046679643189371)
  ·
    refine ⟨194172093219070019464784057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129448062146046679643189371 194172093219070019464784057)
    ·
      refine ⟨145629069914302514598588043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194172093219070019464784057 145629069914302514598588043)
      ·
        refine ⟨218443604871453771897882065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145629069914302514598588043 218443604871453771897882065)
        ·
          refine ⟨163832703653590328923411549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218443604871453771897882065 163832703653590328923411549)
          ·
            refine ⟨61437263870096373346279331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163832703653590328923411549 61437263870096373346279331)
            ·
              refine ⟨92155895805144560019418997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61437263870096373346279331 92155895805144560019418997)
              ·
                refine ⟨8639615231732302501820531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92155895805144560019418997 8639615231732302501820531)
                ·
                  refine ⟨12959422847598453752730797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639615231732302501820531 12959422847598453752730797)
                  ·
                    refine ⟨4859783567849420157274049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12959422847598453752730797 4859783567849420157274049)
                    ·
                      refine ⟨3644837675887065117955537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859783567849420157274049 3644837675887065117955537)
                      ·
                        rfl

theorem cell23_7098296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_7098296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098296 prefixEnd_7098296 := by exact prefixLift 7098296
  have htrace : WordTrace (prefixWord ++ tailWord_7098296) baseStart_7098296 baseEnd_7098296 := by
    simpa [prefixWord, tailWord_7098296, baseEnd_7098296] using wordTrace_append hprefix tailTrace_7098296
  have hstable : (prefixWord ++ tailWord_7098296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098296).length < 2 ^ (prefixWord ++ tailWord_7098296).sum := by decide
  have hdescent : baseEnd_7098296 < baseStart_7098296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_7098309 : Nat := 118140960795 + 7098309 * 2 ^ 59
def prefixEnd_7098309 : Nat := 4983230072969 + 3 ^ 40 * 7098309 * 2
def baseEnd_7098309 : Nat := 3644844351135573567092977

theorem tailTrace_7098309 : CollatzResearch.WordTrace tailWord_7098309 prefixEnd_7098309 3644844351135573567092977 := by
  unfold tailWord_7098309
  simp only [CollatzResearch.WordTrace]
  refine ⟨258896598441046262506601981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172597732294030841671067987 258896598441046262506601981)
  ·
    refine ⟨97086224415392348439975743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258896598441046262506601981 97086224415392348439975743)
    ·
      refine ⟨145629336623088522659963615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97086224415392348439975743 145629336623088522659963615)
      ·
        refine ⟨218444004934632783989945423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145629336623088522659963615 218444004934632783989945423)
        ·
          refine ⟨327666007401949175984918135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218444004934632783989945423 327666007401949175984918135)
          ·
            refine ⟨491499011102923763977377203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327666007401949175984918135 491499011102923763977377203)
            ·
              refine ⟨737248516654385645966065805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491499011102923763977377203 737248516654385645966065805)
              ·
                refine ⟨276468193745394617237274677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737248516654385645966065805 276468193745394617237274677)
                ·
                  refine ⟨25918893163630745365994501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276468193745394617237274677 25918893163630745365994501)
                  ·
                    refine ⟨4859792468180764756123969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25918893163630745365994501 4859792468180764756123969)
                    ·
                      refine ⟨3644844351135573567092977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859792468180764756123969 3644844351135573567092977)
                      ·
                        rfl

theorem cell23_7098309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_7098309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098309 prefixEnd_7098309 := by exact prefixLift 7098309
  have htrace : WordTrace (prefixWord ++ tailWord_7098309) baseStart_7098309 baseEnd_7098309 := by
    simpa [prefixWord, tailWord_7098309, baseEnd_7098309] using wordTrace_append hprefix tailTrace_7098309
  have hstable : (prefixWord ++ tailWord_7098309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098309).length < 2 ^ (prefixWord ++ tailWord_7098309).sum := by decide
  have hdescent : baseEnd_7098309 < baseStart_7098309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098330 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_7098330 : Nat := 118140960795 + 7098330 * 2 ^ 59
def prefixEnd_7098330 : Nat := 4983230072969 + 3 ^ 40 * 7098330 * 2
def baseEnd_7098330 : Nat := 3644855134229317984930381

theorem tailTrace_7098330 : CollatzResearch.WordTrace tailWord_7098330 prefixEnd_7098330 3644855134229317984930381 := by
  unfold tailWord_7098330
  simp only [CollatzResearch.WordTrace]
  refine ⟨64724341093492545773279111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172598242915980122062077629 64724341093492545773279111)
  ·
    refine ⟨97086511640238818659918667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64724341093492545773279111 97086511640238818659918667)
    ·
      refine ⟨145629767460358227989878001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97086511640238818659918667 145629767460358227989878001)
      ·
        refine ⟨109222325595268670992408501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145629767460358227989878001 109222325595268670992408501)
        ·
          refine ⟨10239593024556437905538297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109222325595268670992408501 10239593024556437905538297)
          ·
            refine ⟨7679694768417328429153723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10239593024556437905538297 7679694768417328429153723)
            ·
              refine ⟨11519542152625992643730585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679694768417328429153723 11519542152625992643730585)
              ·
                refine ⟨8639656614469494482797939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11519542152625992643730585 8639656614469494482797939)
                ·
                  refine ⟨12959484921704241724196909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639656614469494482797939 12959484921704241724196909)
                  ·
                    refine ⟨4859806845639090646573841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12959484921704241724196909 4859806845639090646573841)
                    ·
                      refine ⟨3644855134229317984930381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859806845639090646573841 3644855134229317984930381)
                      ·
                        rfl

theorem cell23_7098330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_7098330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098330 prefixEnd_7098330 := by exact prefixLift 7098330
  have htrace : WordTrace (prefixWord ++ tailWord_7098330) baseStart_7098330 baseEnd_7098330 := by
    simpa [prefixWord, tailWord_7098330, baseEnd_7098330] using wordTrace_append hprefix tailTrace_7098330
  have hstable : (prefixWord ++ tailWord_7098330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098330).length < 2 ^ (prefixWord ++ tailWord_7098330).sum := by decide
  have hdescent : baseEnd_7098330 < baseStart_7098330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098343 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7098343 : Nat := 118140960795 + 7098343 * 2 ^ 59
def prefixEnd_7098343 : Nat := 4983230072969 + 3 ^ 40 * 7098343 * 2
def baseEnd_7098343 : Nat := 3644861809477826434067821

theorem tailTrace_7098343 : CollatzResearch.WordTrace tailWord_7098343 prefixEnd_7098343 3644861809477826434067821 := by
  unfold tailWord_7098343
  simp only [CollatzResearch.WordTrace]
  refine ⟨258897838522923086313339683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172598559015282057542226455 258897838522923086313339683)
  ·
    refine ⟨388346757784384629470009525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258897838522923086313339683 388346757784384629470009525)
    ·
      refine ⟨36407508542286059012813393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388346757784384629470009525 36407508542286059012813393)
      ·
        refine ⟨27305631406714544259610045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36407508542286059012813393 27305631406714544259610045)
        ·
          refine ⟨10239611777517954097353767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27305631406714544259610045 10239611777517954097353767)
          ·
            refine ⟨15359417666276931146030651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239611777517954097353767 15359417666276931146030651)
            ·
              refine ⟨23039126499415396719045977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15359417666276931146030651 23039126499415396719045977)
              ·
                refine ⟨17279344874561547539284483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23039126499415396719045977 17279344874561547539284483)
                ·
                  refine ⟨25919017311842321308926725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17279344874561547539284483 25919017311842321308926725)
                  ·
                    refine ⟨4859815745970435245423761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25919017311842321308926725 4859815745970435245423761)
                    ·
                      refine ⟨3644861809477826434067821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859815745970435245423761 3644861809477826434067821)
                      ·
                        rfl

theorem cell23_7098343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7098343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098343 prefixEnd_7098343 := by exact prefixLift 7098343
  have htrace : WordTrace (prefixWord ++ tailWord_7098343) baseStart_7098343 baseEnd_7098343 := by
    simpa [prefixWord, tailWord_7098343, baseEnd_7098343] using wordTrace_append hprefix tailTrace_7098343
  have hstable : (prefixWord ++ tailWord_7098343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098343).length < 2 ^ (prefixWord ++ tailWord_7098343).sum := by decide
  have hdescent : baseEnd_7098343 < baseStart_7098343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098362 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_7098362 : Nat := 118140960795 + 7098362 * 2 ^ 59
def prefixEnd_7098362 : Nat := 4983230072969 + 3 ^ 40 * 7098362 * 2
def baseEnd_7098362 : Nat := 1214957188536753953243411

theorem tailTrace_7098362 : CollatzResearch.WordTrace tailWord_7098362 prefixEnd_7098362 1214957188536753953243411 := by
  unfold tailWord_7098362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64724632877463563139570335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172599021006569501705520893 64724632877463563139570335)
  ·
    refine ⟨97086949316195344709355503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64724632877463563139570335 97086949316195344709355503)
    ·
      refine ⟨145630423974293017064033255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97086949316195344709355503 145630423974293017064033255)
      ·
        refine ⟨218445635961439525596049883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145630423974293017064033255 218445635961439525596049883)
        ·
          refine ⟨327668453942159288394074825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218445635961439525596049883 327668453942159288394074825)
          ·
            refine ⟨245751340456619466295556119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327668453942159288394074825 245751340456619466295556119)
            ·
              refine ⟨368627010684929199443334179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245751340456619466295556119 368627010684929199443334179)
              ·
                refine ⟨552940516027393799165001269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368627010684929199443334179 552940516027393799165001269)
                ·
                  refine ⟨51838173377568168671718869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 552940516027393799165001269 51838173377568168671718869)
                  ·
                    refine ⟨1214957188536753953243411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51838173377568168671718869 1214957188536753953243411)
                    ·
                      rfl

theorem cell23_7098362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_7098362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098362 prefixEnd_7098362 := by exact prefixLift 7098362
  have htrace : WordTrace (prefixWord ++ tailWord_7098362) baseStart_7098362 baseEnd_7098362 := by
    simpa [prefixWord, tailWord_7098362, baseEnd_7098362] using wordTrace_append hprefix tailTrace_7098362
  have hstable : (prefixWord ++ tailWord_7098362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098362).length < 2 ^ (prefixWord ++ tailWord_7098362).sum := by decide
  have hdescent : baseEnd_7098362 < baseStart_7098362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098396 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7098396 : Nat := 118140960795 + 7098396 * 2 ^ 59
def prefixEnd_7098396 : Nat := 4983230072969 + 3 ^ 40 * 7098396 * 2
def baseEnd_7098396 : Nat := 1214963007984171575568359

theorem tailTrace_7098396 : CollatzResearch.WordTrace tailWord_7098396 prefixEnd_7098396 1214963007984171575568359 := by
  unfold tailWord_7098396
  simp only [CollatzResearch.WordTrace]
  refine ⟨129449885795865538182509521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172599847727820717576679361 129449885795865538182509521)
  ·
    refine ⟨97087414346899153636882141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129449885795865538182509521 97087414346899153636882141)
    ·
      refine ⟨36407780380087182613830803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97087414346899153636882141 36407780380087182613830803)
      ·
        refine ⟨54611670570130773920746205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36407780380087182613830803 54611670570130773920746205)
        ·
          refine ⟨20479376463799040220279827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54611670570130773920746205 20479376463799040220279827)
          ·
            refine ⟨30719064695698560330419741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20479376463799040220279827 30719064695698560330419741)
            ·
              refine ⟨11519649260886960123907403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30719064695698560330419741 11519649260886960123907403)
              ·
                refine ⟨17279473891330440185861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519649260886960123907403 17279473891330440185861105)
                ·
                  refine ⟨12959605418497830139395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17279473891330440185861105 12959605418497830139395829)
                  ·
                    refine ⟨1214963007984171575568359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12959605418497830139395829 1214963007984171575568359)
                    ·
                      rfl

theorem cell23_7098396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7098396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098396 prefixEnd_7098396 := by exact prefixLift 7098396
  have htrace : WordTrace (prefixWord ++ tailWord_7098396) baseStart_7098396 baseEnd_7098396 := by
    simpa [prefixWord, tailWord_7098396, baseEnd_7098396] using wordTrace_append hprefix tailTrace_7098396
  have hstable : (prefixWord ++ tailWord_7098396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098396).length < 2 ^ (prefixWord ++ tailWord_7098396).sum := by decide
  have hdescent : baseEnd_7098396 < baseStart_7098396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098399 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_7098399 : Nat := 118140960795 + 7098399 * 2 ^ 59
def prefixEnd_7098399 : Nat := 4983230072969 + 3 ^ 40 * 7098399 * 2
def baseEnd_7098399 : Nat := 3644890564394478214967563

theorem tailTrace_7098399 : CollatzResearch.WordTrace tailWord_7098399 prefixEnd_7098399 3644890564394478214967563 := by
  unfold tailWord_7098399
  simp only [CollatzResearch.WordTrace]
  refine ⟨258899881010720207877378251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172599920673813471918252167 258899881010720207877378251)
  ·
    refine ⟨388349821516080311816067377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258899881010720207877378251 388349821516080311816067377)
    ·
      refine ⟨291262366137060233862050533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388349821516080311816067377 291262366137060233862050533)
      ·
        refine ⟨54611693650698793849134475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291262366137060233862050533 54611693650698793849134475)
        ·
          refine ⟨81917540476048190773701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54611693650698793849134475 81917540476048190773701713)
          ·
            refine ⟨61438155357036143080276285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81917540476048190773701713 61438155357036143080276285)
            ·
              refine ⟨23039308258888553655103607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61438155357036143080276285 23039308258888553655103607)
              ·
                refine ⟨34558962388332830482655411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23039308258888553655103607 34558962388332830482655411)
                ·
                  refine ⟨51838443582499245723983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34558962388332830482655411 51838443582499245723983117)
                  ·
                    refine ⟨19439416343437217146493669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51838443582499245723983117 19439416343437217146493669)
                    ·
                      refine ⟨3644890564394478214967563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19439416343437217146493669 3644890564394478214967563)
                      ·
                        rfl

theorem cell23_7098399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_7098399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098399 prefixEnd_7098399 := by exact prefixLift 7098399
  have htrace : WordTrace (prefixWord ++ tailWord_7098399) baseStart_7098399 baseEnd_7098399 := by
    simpa [prefixWord, tailWord_7098399, baseEnd_7098399] using wordTrace_append hprefix tailTrace_7098399
  have hstable : (prefixWord ++ tailWord_7098399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098399).length < 2 ^ (prefixWord ++ tailWord_7098399).sum := by decide
  have hdescent : baseEnd_7098399 < baseStart_7098399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098416 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2]
def baseStart_7098416 : Nat := 118140960795 + 7098416 * 2 ^ 59
def prefixEnd_7098416 : Nat := 4983230072969 + 3 ^ 40 * 7098416 * 2
def baseEnd_7098416 : Nat := 3644899293565604648454985

theorem tailTrace_7098416 : CollatzResearch.WordTrace tailWord_7098416 prefixEnd_7098416 3644899293565604648454985 := by
  unfold tailWord_7098416
  simp only [CollatzResearch.WordTrace]
  refine ⟨129450250525829309890373551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172600334034439079853831401 129450250525829309890373551)
  ·
    refine ⟨194175375788743964835560327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129450250525829309890373551 194175375788743964835560327)
    ·
      refine ⟨291263063683115947253340491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194175375788743964835560327 291263063683115947253340491)
      ·
        refine ⟨436894595524673920880010737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291263063683115947253340491 436894595524673920880010737)
        ·
          refine ⟨327670946643505440660008053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436894595524673920880010737 327670946643505440660008053)
          ·
            refine ⟨30719151247828635061875755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327670946643505440660008053 30719151247828635061875755)
            ·
              refine ⟨46078726871742952592813633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30719151247828635061875755 46078726871742952592813633)
              ·
                refine ⟨34559045153807214444610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46078726871742952592813633 34559045153807214444610225)
                ·
                  refine ⟨25919283865355410833457669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34559045153807214444610225 25919283865355410833457669)
                  ·
                    refine ⟨4859865724754139531273313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25919283865355410833457669 4859865724754139531273313)
                    ·
                      refine ⟨3644899293565604648454985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859865724754139531273313 3644899293565604648454985)
                      ·
                        rfl

theorem cell23_7098416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 4, 2].length) (baseStart_7098416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098416 prefixEnd_7098416 := by exact prefixLift 7098416
  have htrace : WordTrace (prefixWord ++ tailWord_7098416) baseStart_7098416 baseEnd_7098416 := by
    simpa [prefixWord, tailWord_7098416, baseEnd_7098416] using wordTrace_append hprefix tailTrace_7098416
  have hstable : (prefixWord ++ tailWord_7098416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098416).length < 2 ^ (prefixWord ++ tailWord_7098416).sum := by decide
  have hdescent : baseEnd_7098416 < baseStart_7098416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098429 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7098429 : Nat := 118140960795 + 7098429 * 2 ^ 59
def prefixEnd_7098429 : Nat := 4983230072969 + 3 ^ 40 * 7098429 * 2
def baseEnd_7098429 : Nat := 3644905968814113097592425

theorem tailTrace_7098429 : CollatzResearch.WordTrace tailWord_7098429 prefixEnd_7098429 3644905968814113097592425 := by
  unfold tailWord_7098429
  simp only [CollatzResearch.WordTrace]
  refine ⟨258900975200611523000970341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172600650133741015333980227 258900975200611523000970341)
  ·
    refine ⟨48543932850114660562681939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258900975200611523000970341 48543932850114660562681939)
    ·
      refine ⟨72815899275171990844022909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48543932850114660562681939 72815899275171990844022909)
      ·
        refine ⟨27305962228189496566508591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72815899275171990844022909 27305962228189496566508591)
        ·
          refine ⟨40958943342284244849762887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27305962228189496566508591 40958943342284244849762887)
          ·
            refine ⟨61438415013426367274644331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40958943342284244849762887 61438415013426367274644331)
            ·
              refine ⟨92157622520139550911966497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61438415013426367274644331 92157622520139550911966497)
              ·
                refine ⟨69118216890104663183974873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92157622520139550911966497 69118216890104663183974873)
                ·
                  refine ⟨51838662667578497387981155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69118216890104663183974873 51838662667578497387981155)
                  ·
                    refine ⟨77757994001367746081971733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51838662667578497387981155 77757994001367746081971733)
                    ·
                      refine ⟨3644905968814113097592425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77757994001367746081971733 3644905968814113097592425)
                      ·
                        rfl

theorem cell23_7098429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7098429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098429 prefixEnd_7098429 := by exact prefixLift 7098429
  have htrace : WordTrace (prefixWord ++ tailWord_7098429) baseStart_7098429 baseEnd_7098429 := by
    simpa [prefixWord, tailWord_7098429, baseEnd_7098429] using wordTrace_append hprefix tailTrace_7098429
  have hstable : (prefixWord ++ tailWord_7098429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098429).length < 2 ^ (prefixWord ++ tailWord_7098429).sum := by decide
  have hdescent : baseEnd_7098429 < baseStart_7098429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098433 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7098433 : Nat := 118140960795 + 7098433 * 2 ^ 59
def prefixEnd_7098433 : Nat := 4983230072969 + 3 ^ 40 * 7098433 * 2
def baseEnd_7098433 : Nat := 3644908022736731081942407

theorem tailTrace_7098433 : CollatzResearch.WordTrace tailWord_7098433 prefixEnd_7098433 3644908022736731081942407 := by
  unfold tailWord_7098433
  simp only [CollatzResearch.WordTrace]
  refine ⟨258901121092597031684115953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172600747395064687789410635 258901121092597031684115953)
  ·
    refine ⟨194175840819447773763086965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258901121092597031684115953 194175840819447773763086965)
    ·
      refine ⟨18203985076823228790289403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194175840819447773763086965 18203985076823228790289403)
      ·
        refine ⟨27305977615234843185434105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18203985076823228790289403 27305977615234843185434105)
        ·
          refine ⟨20479483211426132389075579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27305977615234843185434105 20479483211426132389075579)
          ·
            refine ⟨30719224817139198583613369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20479483211426132389075579 30719224817139198583613369)
            ·
              refine ⟨23039418612854398937710027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30719224817139198583613369 23039418612854398937710027)
              ·
                refine ⟨34559127919281598406565041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23039418612854398937710027 34559127919281598406565041)
                ·
                  refine ⟨25919345939461198804923781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34559127919281598406565041 25919345939461198804923781)
                  ·
                    refine ⟨4859877363648974775923209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25919345939461198804923781 4859877363648974775923209)
                    ·
                      refine ⟨3644908022736731081942407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859877363648974775923209 3644908022736731081942407)
                      ·
                        rfl

theorem cell23_7098433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7098433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098433 prefixEnd_7098433 := by exact prefixLift 7098433
  have htrace : WordTrace (prefixWord ++ tailWord_7098433) baseStart_7098433 baseEnd_7098433 := by
    simpa [prefixWord, tailWord_7098433, baseEnd_7098433] using wordTrace_append hprefix tailTrace_7098433
  have hstable : (prefixWord ++ tailWord_7098433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098433).length < 2 ^ (prefixWord ++ tailWord_7098433).sum := by decide
  have hdescent : baseEnd_7098433 < baseStart_7098433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098449 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_7098449 : Nat := 118140960795 + 7098449 * 2 ^ 59
def prefixEnd_7098449 : Nat := 4983230072969 + 3 ^ 40 * 7098449 * 2
def baseEnd_7098449 : Nat := 3644916238427203019342333

theorem tailTrace_7098449 : CollatzResearch.WordTrace tailWord_7098449 prefixEnd_7098449 3644916238427203019342333 := by
  unfold tailWord_7098449
  simp only [CollatzResearch.WordTrace]
  refine ⟨258901704660539066416698401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172601136440359377611132267 258901704660539066416698401)
  ·
    refine ⟨194176278495404299812523801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258901704660539066416698401 194176278495404299812523801)
    ·
      refine ⟨145632208871553224859392851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194176278495404299812523801 145632208871553224859392851)
      ·
        refine ⟨218448313307329837289089277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145632208871553224859392851 218448313307329837289089277)
        ·
          refine ⟨81918117490248688983408479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218448313307329837289089277 81918117490248688983408479)
          ·
            refine ⟨122877176235373033475112719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81918117490248688983408479 122877176235373033475112719)
            ·
              refine ⟨184315764353059550212669079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122877176235373033475112719 184315764353059550212669079)
              ·
                refine ⟨276473646529589325319003619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184315764353059550212669079 276473646529589325319003619)
                ·
                  refine ⟨414710469794383987978505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276473646529589325319003619 414710469794383987978505429)
                  ·
                    refine ⟨9719776635805874718246221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 414710469794383987978505429 9719776635805874718246221)
                    ·
                      refine ⟨3644916238427203019342333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719776635805874718246221 3644916238427203019342333)
                      ·
                        rfl

theorem cell23_7098449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_7098449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098449 prefixEnd_7098449 := by exact prefixLift 7098449
  have htrace : WordTrace (prefixWord ++ tailWord_7098449) baseStart_7098449 baseEnd_7098449 := by
    simpa [prefixWord, tailWord_7098449, baseEnd_7098449] using wordTrace_append hprefix tailTrace_7098449
  have hstable : (prefixWord ++ tailWord_7098449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098449).length < 2 ^ (prefixWord ++ tailWord_7098449).sum := by decide
  have hdescent : baseEnd_7098449 < baseStart_7098449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098460 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7098460 : Nat := 118140960795 + 7098460 * 2 ^ 59
def prefixEnd_7098460 : Nat := 4983230072969 + 3 ^ 40 * 7098460 * 2
def baseEnd_7098460 : Nat := 1214973962238134158768261

theorem tailTrace_7098460 : CollatzResearch.WordTrace tailWord_7098460 prefixEnd_7098460 1214973962238134158768261 := by
  unfold tailWord_7098460
  simp only [CollatzResearch.WordTrace]
  refine ⟨129451052931749607647674417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172601403908999476863565889 129451052931749607647674417)
  ·
    refine ⟨97088289698812205735755813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129451052931749607647674417 97088289698812205735755813)
    ·
      refine ⟨18204054318527288575454215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97088289698812205735755813 18204054318527288575454215)
      ·
        refine ⟨27306081477790932863181323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18204054318527288575454215 27306081477790932863181323)
        ·
          refine ⟨40959122216686399294771985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27306081477790932863181323 40959122216686399294771985)
          ·
            refine ⟨30719341662514799471078989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40959122216686399294771985 30719341662514799471078989)
            ·
              refine ⟨11519753123443049801654621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30719341662514799471078989 11519753123443049801654621)
              ·
                refine ⟨4319907421291143675620483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11519753123443049801654621 4319907421291143675620483)
                ·
                  refine ⟨6479861131936715513430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319907421291143675620483 6479861131936715513430725)
                  ·
                    refine ⟨1214973962238134158768261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479861131936715513430725 1214973962238134158768261)
                    ·
                      rfl

theorem cell23_7098460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7098460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098460 prefixEnd_7098460 := by exact prefixLift 7098460
  have htrace : WordTrace (prefixWord ++ tailWord_7098460) baseStart_7098460 baseEnd_7098460 := by
    simpa [prefixWord, tailWord_7098460, baseEnd_7098460] using wordTrace_append hprefix tailTrace_7098460
  have hstable : (prefixWord ++ tailWord_7098460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098460).length < 2 ^ (prefixWord ++ tailWord_7098460).sum := by decide
  have hdescent : baseEnd_7098460 < baseStart_7098460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098520 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_7098520 : Nat := 118140960795 + 7098520 * 2 ^ 59
def prefixEnd_7098520 : Nat := 4983230072969 + 3 ^ 40 * 7098520 * 2
def baseEnd_7098520 : Nat := 1214984231851224080518169

theorem tailTrace_7098520 : CollatzResearch.WordTrace tailWord_7098520 prefixEnd_7098520 1214984231851224080518169 := by
  unfold tailWord_7098520
  simp only [CollatzResearch.WordTrace]
  refine ⟨129452147121640922771266507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172602862828854563695022009 129452147121640922771266507)
  ·
    refine ⟨194178220682461384156899761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129452147121640922771266507 194178220682461384156899761)
    ·
      refine ⟨145633665511846038117674821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194178220682461384156899761 145633665511846038117674821)
      ·
        refine ⟨27306312283471132147064029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145633665511846038117674821 27306312283471132147064029)
        ·
          refine ⟨10239867106301674555149011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27306312283471132147064029 10239867106301674555149011)
          ·
            refine ⟨15359800659452511832723517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10239867106301674555149011 15359800659452511832723517)
            ·
              refine ⟨5759925247294691937271319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15359800659452511832723517 5759925247294691937271319)
              ·
                refine ⟨8639887870942037905906979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759925247294691937271319 8639887870942037905906979)
                ·
                  refine ⟨12959831806413056858860469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639887870942037905906979 12959831806413056858860469)
                  ·
                    refine ⟨1214984231851224080518169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12959831806413056858860469 1214984231851224080518169)
                    ·
                      rfl

theorem cell23_7098520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_7098520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098520 prefixEnd_7098520 := by exact prefixLift 7098520
  have htrace : WordTrace (prefixWord ++ tailWord_7098520) baseStart_7098520 baseEnd_7098520 := by
    simpa [prefixWord, tailWord_7098520, baseEnd_7098520] using wordTrace_append hprefix tailTrace_7098520
  have hstable : (prefixWord ++ tailWord_7098520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098520).length < 2 ^ (prefixWord ++ tailWord_7098520).sum := by decide
  have hdescent : baseEnd_7098520 < baseStart_7098520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098529 : List Nat := [1, 2, 3, 3, 1, 13]
def baseStart_7098529 : Nat := 118140960795 + 7098529 * 2 ^ 59
def prefixEnd_7098529 : Nat := 4983230072969 + 3 ^ 40 * 7098529 * 2
def baseEnd_7098529 : Nat := 14999824349298611960255

theorem tailTrace_7098529 : CollatzResearch.WordTrace tailWord_7098529 prefixEnd_7098529 14999824349298611960255 := by
  unfold tailWord_7098529
  simp only [CollatzResearch.WordTrace]
  refine ⟨258904622500249240079610641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172603081666832826719740427 258904622500249240079610641)
  ·
    refine ⟨194178466875186930059707981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258904622500249240079610641 194178466875186930059707981)
    ·
      refine ⟨72816925078195098772390493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194178466875186930059707981 72816925078195098772390493)
      ·
        refine ⟨27306346904323162039646435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72816925078195098772390493 27306346904323162039646435)
        ·
          refine ⟨40959520356484743059469653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27306346904323162039646435 40959520356484743059469653)
          ·
            refine ⟨14999824349298611960255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40959520356484743059469653 14999824349298611960255)
            ·
              rfl

theorem cell23_7098529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 13].length) (baseStart_7098529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098529 prefixEnd_7098529 := by exact prefixLift 7098529
  have htrace : WordTrace (prefixWord ++ tailWord_7098529) baseStart_7098529 baseEnd_7098529 := by
    simpa [prefixWord, tailWord_7098529, baseEnd_7098529] using wordTrace_append hprefix tailTrace_7098529
  have hstable : (prefixWord ++ tailWord_7098529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098529).length < 2 ^ (prefixWord ++ tailWord_7098529).sum := by decide
  have hdescent : baseEnd_7098529 < baseStart_7098529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098533 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_7098533 : Nat := 118140960795 + 7098533 * 2 ^ 59
def prefixEnd_7098533 : Nat := 4983230072969 + 3 ^ 40 * 7098533 * 2
def baseEnd_7098533 : Nat := 1214986456934060230230649

theorem tailTrace_7098533 : CollatzResearch.WordTrace tailWord_7098533 prefixEnd_7098533 1214986456934060230230649 := by
  unfold tailWord_7098533
  simp only [CollatzResearch.WordTrace]
  refine ⟨258904768392234748762756253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172603178928156499175170835 258904768392234748762756253)
  ·
    refine ⟨97089288147088030786033595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258904768392234748762756253 97089288147088030786033595)
    ·
      refine ⟨145633932220632046179050393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97089288147088030786033595 145633932220632046179050393)
      ·
        refine ⟨109225449165474034634287795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145633932220632046179050393 109225449165474034634287795)
        ·
          refine ⟨163838173748211051951431693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109225449165474034634287795 163838173748211051951431693)
          ·
            refine ⟨61439315155579144481786885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163838173748211051951431693 61439315155579144481786885)
            ·
              refine ⟨11519871591671089590335041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61439315155579144481786885 11519871591671089590335041)
              ·
                refine ⟨8639903693753317192751281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11519871591671089590335041 8639903693753317192751281)
                ·
                  refine ⟨6479927770314987894563461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8639903693753317192751281 6479927770314987894563461)
                  ·
                    refine ⟨1214986456934060230230649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6479927770314987894563461 1214986456934060230230649)
                    ·
                      rfl

theorem cell23_7098533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_7098533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098533 prefixEnd_7098533 := by exact prefixLift 7098533
  have htrace : WordTrace (prefixWord ++ tailWord_7098533) baseStart_7098533 baseEnd_7098533 := by
    simpa [prefixWord, tailWord_7098533, baseEnd_7098533] using wordTrace_append hprefix tailTrace_7098533
  have hstable : (prefixWord ++ tailWord_7098533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098533).length < 2 ^ (prefixWord ++ tailWord_7098533).sum := by decide
  have hdescent : baseEnd_7098533 < baseStart_7098533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098559 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 7]
def baseStart_7098559 : Nat := 118140960795 + 7098559 * 2 ^ 59
def prefixEnd_7098559 : Nat := 4983230072969 + 3 ^ 40 * 7098559 * 2
def baseEnd_7098559 : Nat := 1214990907099732529655609

theorem tailTrace_7098559 : CollatzResearch.WordTrace tailWord_7098559 prefixEnd_7098559 1214990907099732529655609 := by
  unfold tailWord_7098559
  simp only [CollatzResearch.WordTrace]
  refine ⟨258905716690140555203202731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172603811126760370135468487 258905716690140555203202731)
  ·
    refine ⟨388358575035210832804804097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258905716690140555203202731 388358575035210832804804097)
    ·
      refine ⟨291268931276408124603603073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388358575035210832804804097 291268931276408124603603073)
      ·
        refine ⟨218451698457306093452702305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291268931276408124603603073 218451698457306093452702305)
        ·
          refine ⟨163838773842979570089526729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218451698457306093452702305 163838773842979570089526729)
          ·
            refine ⟨122879080382234677567145047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163838773842979570089526729 122879080382234677567145047)
            ·
              refine ⟨184318620573352016350717571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122879080382234677567145047 184318620573352016350717571)
              ·
                refine ⟨276477930860028024526076357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184318620573352016350717571 276477930860028024526076357)
                ·
                  refine ⟨51839612036255254598639317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276477930860028024526076357 51839612036255254598639317)
                  ·
                    refine ⟨1214990907099732529655609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51839612036255254598639317 1214990907099732529655609)
                    ·
                      rfl

theorem cell23_7098559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_7098559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098559 prefixEnd_7098559 := by exact prefixLift 7098559
  have htrace : WordTrace (prefixWord ++ tailWord_7098559) baseStart_7098559 baseEnd_7098559 := by
    simpa [prefixWord, tailWord_7098559, baseEnd_7098559] using wordTrace_append hprefix tailTrace_7098559
  have hstable : (prefixWord ++ tailWord_7098559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098559).length < 2 ^ (prefixWord ++ tailWord_7098559).sum := by decide
  have hdescent : baseEnd_7098559 < baseStart_7098559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098574 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_7098574 : Nat := 118140960795 + 7098574 * 2 ^ 59
def prefixEnd_7098574 : Nat := 4983230072969 + 3 ^ 40 * 7098574 * 2
def baseEnd_7098574 : Nat := 3644980423509015030279259

theorem tailTrace_7098574 : CollatzResearch.WordTrace tailWord_7098574 prefixEnd_7098574 3644980423509015030279259 := by
  unfold tailWord_7098574
  simp only [CollatzResearch.WordTrace]
  refine ⟨32363282973135776595624847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172604175856724141843332517 32363282973135776595624847)
  ·
    refine ⟨48544924459703664893437271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32363282973135776595624847 48544924459703664893437271)
    ·
      refine ⟨72817386689555497340155907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48544924459703664893437271 72817386689555497340155907)
      ·
        refine ⟨109226080034333246010233861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72817386689555497340155907 109226080034333246010233861)
        ·
          refine ⟨20479890006437483626918849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109226080034333246010233861 20479890006437483626918849)
          ·
            refine ⟨15359917504828112720189137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20479890006437483626918849 15359917504828112720189137)
            ·
              refine ⟨11519938128621084540141853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15359917504828112720189137 11519938128621084540141853)
              ·
                refine ⟨4319976798232906702553195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11519938128621084540141853 4319976798232906702553195)
                ·
                  refine ⟨6479965197349360053829793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319976798232906702553195 6479965197349360053829793)
                  ·
                    refine ⟨4859973898012020040372345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6479965197349360053829793 4859973898012020040372345)
                    ·
                      refine ⟨3644980423509015030279259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4859973898012020040372345 3644980423509015030279259)
                      ·
                        rfl

theorem cell23_7098574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_7098574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098574 prefixEnd_7098574 := by exact prefixLift 7098574
  have htrace : WordTrace (prefixWord ++ tailWord_7098574) baseStart_7098574 baseEnd_7098574 := by
    simpa [prefixWord, tailWord_7098574, baseEnd_7098574] using wordTrace_append hprefix tailTrace_7098574
  have hstable : (prefixWord ++ tailWord_7098574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098574).length < 2 ^ (prefixWord ++ tailWord_7098574).sum := by decide
  have hdescent : baseEnd_7098574 < baseStart_7098574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098607 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 2, 1, 3]
def baseStart_7098607 : Nat := 118140960795 + 7098607 * 2 ^ 59
def prefixEnd_7098607 : Nat := 4983230072969 + 3 ^ 40 * 7098607 * 2
def baseEnd_7098607 : Nat := 3644997368370613401166607

theorem tailTrace_7098607 : CollatzResearch.WordTrace tailWord_7098607 prefixEnd_7098607 3644997368370613401166607 := by
  unfold tailWord_7098607
  simp only [CollatzResearch.WordTrace]
  refine ⟨258907467393966659400950075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172604978262644439600633383 258907467393966659400950075)
  ·
    refine ⟨388361201090949989101425113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258907467393966659400950075 388361201090949989101425113)
    ·
      refine ⟨291270900818212491826068835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388361201090949989101425113 291270900818212491826068835)
      ·
        refine ⟨436906351227318737739103253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291270900818212491826068835 436906351227318737739103253)
        ·
          refine ⟨20479985213780565831520465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 436906351227318737739103253 20479985213780565831520465)
          ·
            refine ⟨15359988910335424373640349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20479985213780565831520465 15359988910335424373640349)
            ·
              refine ⟨5759995841375784140115131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15359988910335424373640349 5759995841375784140115131)
              ·
                refine ⟨8639993762063676210172697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759995841375784140115131 8639993762063676210172697)
                ·
                  refine ⟨6479995321547757157629523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8639993762063676210172697 6479995321547757157629523)
                  ·
                    refine ⟨9719992982321635736444285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6479995321547757157629523 9719992982321635736444285)
                    ·
                      refine ⟨3644997368370613401166607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9719992982321635736444285 3644997368370613401166607)
                      ·
                        rfl

theorem cell23_7098607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 1, 3].length) (baseStart_7098607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098607 prefixEnd_7098607 := by exact prefixLift 7098607
  have htrace : WordTrace (prefixWord ++ tailWord_7098607) baseStart_7098607 baseEnd_7098607 := by
    simpa [prefixWord, tailWord_7098607, baseEnd_7098607] using wordTrace_append hprefix tailTrace_7098607
  have hstable : (prefixWord ++ tailWord_7098607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098607).length < 2 ^ (prefixWord ++ tailWord_7098607).sum := by decide
  have hdescent : baseEnd_7098607 < baseStart_7098607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098616 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_7098616 : Nat := 118140960795 + 7098616 * 2 ^ 59
def prefixEnd_7098616 : Nat := 4983230072969 + 3 ^ 40 * 7098616 * 2
def baseEnd_7098616 : Nat := 3645001989696503865954065

theorem tailTrace_7098616 : CollatzResearch.WordTrace tailWord_7098616 prefixEnd_7098616 3645001989696503865954065 := by
  unfold tailWord_7098616
  simp only [CollatzResearch.WordTrace]
  refine ⟨129453897825467026969013851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172605197100622702625351801 129453897825467026969013851)
  ·
    refine ⟨194180846738200540453520777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129453897825467026969013851 194180846738200540453520777)
    ·
      refine ⟨145635635053650405340140583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194180846738200540453520777 145635635053650405340140583)
      ·
        refine ⟨218453452580475608010210875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145635635053650405340140583 218453452580475608010210875)
        ·
          refine ⟨327680178870713412015316313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218453452580475608010210875 327680178870713412015316313)
          ·
            refine ⟨245760134153035059011487235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327680178870713412015316313 245760134153035059011487235)
            ·
              refine ⟨368640201229552588517230853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245760134153035059011487235 368640201229552588517230853)
              ·
                refine ⟨69120037730541110346980785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368640201229552588517230853 69120037730541110346980785)
                ·
                  refine ⟨51840028297905832760235589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69120037730541110346980785 51840028297905832760235589)
                  ·
                    refine ⟨9720005305857343642544173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51840028297905832760235589 9720005305857343642544173)
                    ·
                      refine ⟨3645001989696503865954065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720005305857343642544173 3645001989696503865954065)
                      ·
                        rfl

theorem cell23_7098616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_7098616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098616 prefixEnd_7098616 := by exact prefixLift 7098616
  have htrace : WordTrace (prefixWord ++ tailWord_7098616) baseStart_7098616 baseEnd_7098616 := by
    simpa [prefixWord, tailWord_7098616, baseEnd_7098616] using wordTrace_append hprefix tailTrace_7098616
  have hstable : (prefixWord ++ tailWord_7098616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098616).length < 2 ^ (prefixWord ++ tailWord_7098616).sum := by decide
  have hdescent : baseEnd_7098616 < baseStart_7098616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098664 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7098664 : Nat := 118140960795 + 7098664 * 2 ^ 59
def prefixEnd_7098664 : Nat := 4983230072969 + 3 ^ 40 * 7098664 * 2
def baseEnd_7098664 : Nat := 3645026636767919678153845

theorem tailTrace_7098664 : CollatzResearch.WordTrace tailWord_7098664 prefixEnd_7098664 3645026636767919678153845 := by
  unfold tailWord_7098664
  simp only [CollatzResearch.WordTrace]
  refine ⟨129454773177380079067887523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172606364236506772090516697 129454773177380079067887523)
  ·
    refine ⟨194182159766070118601831285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129454773177380079067887523 194182159766070118601831285)
    ·
      refine ⟨18204577478069073618921683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194182159766070118601831285 18204577478069073618921683)
      ·
        refine ⟨27306866217103610428382525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18204577478069073618921683 27306866217103610428382525)
        ·
          refine ⟨10240074831413853910643447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27306866217103610428382525 10240074831413853910643447)
          ·
            refine ⟨15360112247120780865965171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240074831413853910643447 15360112247120780865965171)
            ·
              refine ⟨23040168370681171298947757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15360112247120780865965171 23040168370681171298947757)
              ·
                refine ⟨8640063139005439237105409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23040168370681171298947757 8640063139005439237105409)
                ·
                  refine ⟨6480047354254079427829057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640063139005439237105409 6480047354254079427829057)
                  ·
                    refine ⟨4860035515690559570871793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480047354254079427829057 4860035515690559570871793)
                    ·
                      refine ⟨3645026636767919678153845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860035515690559570871793 3645026636767919678153845)
                      ·
                        rfl

theorem cell23_7098664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7098664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098664 prefixEnd_7098664 := by exact prefixLift 7098664
  have htrace : WordTrace (prefixWord ++ tailWord_7098664) baseStart_7098664 baseEnd_7098664 := by
    simpa [prefixWord, tailWord_7098664, baseEnd_7098664] using wordTrace_append hprefix tailTrace_7098664
  have hstable : (prefixWord ++ tailWord_7098664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098664).length < 2 ^ (prefixWord ++ tailWord_7098664).sum := by decide
  have hdescent : baseEnd_7098664 < baseStart_7098664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098713 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_7098713 : Nat := 118140960795 + 7098713 * 2 ^ 59
def prefixEnd_7098713 : Nat := 4983230072969 + 3 ^ 40 * 7098713 * 2
def baseEnd_7098713 : Nat := 1215017265773329995480373

theorem tailTrace_7098713 : CollatzResearch.WordTrace tailWord_7098713 prefixEnd_7098713 1215017265773329995480373 := by
  unfold tailWord_7098713
  simp only [CollatzResearch.WordTrace]
  refine ⟨258911333531582639504308793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172607555687721759669539195 258911333531582639504308793)
  ·
    refine ⟨194183500148686979628231595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258911333531582639504308793 194183500148686979628231595)
    ·
      refine ⟨291275250223030469442347393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194183500148686979628231595 291275250223030469442347393)
      ·
        refine ⟨218456437667272852081760545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291275250223030469442347393 218456437667272852081760545)
        ·
          refine ⟨163842328250454639061320409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218456437667272852081760545 163842328250454639061320409)
          ·
            refine ⟨122881746187840979295990307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163842328250454639061320409 122881746187840979295990307)
            ·
              refine ⟨184322619281761468943985461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122881746187840979295990307 184322619281761468943985461)
              ·
                refine ⟨17280245557665137713498637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184322619281761468943985461 17280245557665137713498637)
                ·
                  refine ⟨6480092084124426642561989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17280245557665137713498637 6480092084124426642561989)
                  ·
                    refine ⟨1215017265773329995480373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480092084124426642561989 1215017265773329995480373)
                    ·
                      rfl

theorem cell23_7098713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_7098713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098713 prefixEnd_7098713 := by exact prefixLift 7098713
  have htrace : WordTrace (prefixWord ++ tailWord_7098713) baseStart_7098713 baseEnd_7098713 := by
    simpa [prefixWord, tailWord_7098713, baseEnd_7098713] using wordTrace_append hprefix tailTrace_7098713
  have hstable : (prefixWord ++ tailWord_7098713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098713).length < 2 ^ (prefixWord ++ tailWord_7098713).sum := by decide
  have hdescent : baseEnd_7098713 < baseStart_7098713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098723 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3]
def baseStart_7098723 : Nat := 118140960795 + 7098723 * 2 ^ 59
def prefixEnd_7098723 : Nat := 4983230072969 + 3 ^ 40 * 7098723 * 2
def baseEnd_7098723 : Nat := 3645056932126534947316073

theorem tailTrace_7098723 : CollatzResearch.WordTrace tailWord_7098723 prefixEnd_7098723 3645056932126534947316073 := by
  unfold tailWord_7098723
  simp only [CollatzResearch.WordTrace]
  refine ⟨258911698261546411212172823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172607798841030940808115215 258911698261546411212172823)
  ·
    refine ⟨388367547392319616818259235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258911698261546411212172823 388367547392319616818259235)
    ·
      refine ⟨582551321088479425227388853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388367547392319616818259235 582551321088479425227388853)
      ·
        refine ⟨54614186352044946115067705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 582551321088479425227388853 54614186352044946115067705)
        ·
          refine ⟨40960639764033709586300779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54614186352044946115067705 40960639764033709586300779)
          ·
            refine ⟨61440959646050564379451169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40960639764033709586300779 61440959646050564379451169)
            ·
              refine ⟨46080719734537923284588377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61440959646050564379451169 46080719734537923284588377)
              ·
                refine ⟨34560539800903442463441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46080719734537923284588377 34560539800903442463441283)
                ·
                  refine ⟨51840809701355163695161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34560539800903442463441283 51840809701355163695161925)
                  ·
                    refine ⟨9720151819004093192842861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51840809701355163695161925 9720151819004093192842861)
                    ·
                      refine ⟨3645056932126534947316073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720151819004093192842861 3645056932126534947316073)
                      ·
                        rfl

theorem cell23_7098723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_7098723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098723 prefixEnd_7098723 := by exact prefixLift 7098723
  have htrace : WordTrace (prefixWord ++ tailWord_7098723) baseStart_7098723 baseEnd_7098723 := by
    simpa [prefixWord, tailWord_7098723, baseEnd_7098723] using wordTrace_append hprefix tailTrace_7098723
  have hstable : (prefixWord ++ tailWord_7098723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098723).length < 2 ^ (prefixWord ++ tailWord_7098723).sum := by decide
  have hdescent : baseEnd_7098723 < baseStart_7098723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098730 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_7098730 : Nat := 118140960795 + 7098730 * 2 ^ 59
def prefixEnd_7098730 : Nat := 4983230072969 + 3 ^ 40 * 7098730 * 2
def baseEnd_7098730 : Nat := 1215020175497038806642847

theorem tailTrace_7098730 : CollatzResearch.WordTrace tailWord_7098730 prefixEnd_7098730 1215020175497038806642847 := by
  unfold tailWord_7098730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64727988393130262851919411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172607969048347367605118429 64727988393130262851919411)
  ·
    refine ⟨97091982589695394277879117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64727988393130262851919411 97091982589695394277879117)
    ·
      refine ⟨36409493471135772854204669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97091982589695394277879117 36409493471135772854204669)
      ·
        refine ⟨13653560051675914820326751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36409493471135772854204669 13653560051675914820326751)
        ·
          refine ⟨20480340077513872230490127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13653560051675914820326751 20480340077513872230490127)
          ·
            refine ⟨30720510116270808345735191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480340077513872230490127 30720510116270808345735191)
            ·
              refine ⟨46080765174406212518602787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720510116270808345735191 46080765174406212518602787)
              ·
                refine ⟨69121147761609318777904181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46080765174406212518602787 69121147761609318777904181)
                ·
                  refine ⟨6480107602650873635428517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69121147761609318777904181 6480107602650873635428517)
                  ·
                    refine ⟨1215020175497038806642847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480107602650873635428517 1215020175497038806642847)
                    ·
                      rfl

theorem cell23_7098730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_7098730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098730 prefixEnd_7098730 := by exact prefixLift 7098730
  have htrace : WordTrace (prefixWord ++ tailWord_7098730) baseStart_7098730 baseEnd_7098730 := by
    simpa [prefixWord, tailWord_7098730, baseEnd_7098730] using wordTrace_append hprefix tailTrace_7098730
  have hstable : (prefixWord ++ tailWord_7098730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098730).length < 2 ^ (prefixWord ++ tailWord_7098730).sum := by decide
  have hdescent : baseEnd_7098730 < baseStart_7098730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098746 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_7098746 : Nat := 118140960795 + 7098746 * 2 ^ 59
def prefixEnd_7098746 : Nat := 4983230072969 + 3 ^ 40 * 7098746 * 2
def baseEnd_7098746 : Nat := 3645068742181588357328467

theorem tailTrace_7098746 : CollatzResearch.WordTrace tailWord_7098746 prefixEnd_7098746 3645068742181588357328467 := by
  unfold tailWord_7098746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64728134285115771535065023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172608358093642057426840061 64728134285115771535065023)
  ·
    refine ⟨97092201427673657302597535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64728134285115771535065023 97092201427673657302597535)
    ·
      refine ⟨145638302141510485953896303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97092201427673657302597535 145638302141510485953896303)
      ·
        refine ⟨218457453212265728930844455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145638302141510485953896303 218457453212265728930844455)
        ·
          refine ⟨327686179818398593396266683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218457453212265728930844455 327686179818398593396266683)
          ·
            refine ⟨491529269727597890094400025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327686179818398593396266683 491529269727597890094400025)
            ·
              refine ⟨368646952295698417570800019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491529269727597890094400025 368646952295698417570800019)
              ·
                refine ⟨552970428443547626356200029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368646952295698417570800019 552970428443547626356200029)
                ·
                  refine ⟨207363910666330359883575011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552970428443547626356200029 207363910666330359883575011)
                  ·
                    refine ⟨311045865999495539825362517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207363910666330359883575011 311045865999495539825362517)
                    ·
                      refine ⟨3645068742181588357328467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311045865999495539825362517 3645068742181588357328467)
                      ·
                        rfl

theorem cell23_7098746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_7098746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098746 prefixEnd_7098746 := by exact prefixLift 7098746
  have htrace : WordTrace (prefixWord ++ tailWord_7098746) baseStart_7098746 baseEnd_7098746 := by
    simpa [prefixWord, tailWord_7098746, baseEnd_7098746] using wordTrace_append hprefix tailTrace_7098746
  have hstable : (prefixWord ++ tailWord_7098746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098746).length < 2 ^ (prefixWord ++ tailWord_7098746).sum := by decide
  have hdescent : baseEnd_7098746 < baseStart_7098746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098747 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 1, 4]
def baseStart_7098747 : Nat := 118140960795 + 7098747 * 2 ^ 59
def prefixEnd_7098747 : Nat := 4983230072969 + 3 ^ 40 * 7098747 * 2
def baseEnd_7098747 : Nat := 1215023085220747617805321

theorem tailTrace_7098747 : CollatzResearch.WordTrace tailWord_7098747 prefixEnd_7098747 1215023085220747617805321 := by
  unfold tailWord_7098747
  simp only [CollatzResearch.WordTrace]
  refine ⟨258912573613459463311046495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172608382408972975540697663 258912573613459463311046495)
  ·
    refine ⟨388368860420189194966569743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258912573613459463311046495 388368860420189194966569743)
    ·
      refine ⟨582553290630283792449854615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388368860420189194966569743 582553290630283792449854615)
      ·
        refine ⟨873829935945425688674781923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582553290630283792449854615 873829935945425688674781923)
        ·
          refine ⟨1310744903918138533012172885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873829935945425688674781923 1310744903918138533012172885)
          ·
            refine ⟨15360291842790685933736401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1310744903918138533012172885 15360291842790685933736401)
            ·
              refine ⟨11520218882093014450302301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15360291842790685933736401 11520218882093014450302301)
              ·
                refine ⟨4320082080784880418863363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11520218882093014450302301 4320082080784880418863363)
                ·
                  refine ⟨6480123121177320628295045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320082080784880418863363 6480123121177320628295045)
                  ·
                    refine ⟨1215023085220747617805321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480123121177320628295045 1215023085220747617805321)
                    ·
                      rfl

theorem cell23_7098747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 4].length) (baseStart_7098747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098747 prefixEnd_7098747 := by exact prefixLift 7098747
  have htrace : WordTrace (prefixWord ++ tailWord_7098747) baseStart_7098747 baseEnd_7098747 := by
    simpa [prefixWord, tailWord_7098747, baseEnd_7098747] using wordTrace_append hprefix tailTrace_7098747
  have hstable : (prefixWord ++ tailWord_7098747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098747).length < 2 ^ (prefixWord ++ tailWord_7098747).sum := by decide
  have hdescent : baseEnd_7098747 < baseStart_7098747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098793 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_7098793 : Nat := 118140960795 + 7098793 * 2 ^ 59
def prefixEnd_7098793 : Nat := 4983230072969 + 3 ^ 40 * 7098793 * 2
def baseEnd_7098793 : Nat := 3645092875772349673440751

theorem tailTrace_7098793 : CollatzResearch.WordTrace tailWord_7098793 prefixEnd_7098793 3645092875772349673440751 := by
  unfold tailWord_7098793
  simp only [CollatzResearch.WordTrace]
  refine ⟨258914251371292813167221033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172609500914195208778147355 258914251371292813167221033)
  ·
    refine ⟨194185688528469609875415775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258914251371292813167221033 194185688528469609875415775)
    ·
      refine ⟨291278532792704414813123663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194185688528469609875415775 291278532792704414813123663)
      ·
        refine ⟨436917799189056622219685495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291278532792704414813123663 436917799189056622219685495)
        ·
          refine ⟨655376698783584933329528243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436917799189056622219685495 655376698783584933329528243)
          ·
            refine ⟨983065048175377399994292365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655376698783584933329528243 983065048175377399994292365)
            ·
              refine ⟨368649393065766524997859637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 983065048175377399994292365 368649393065766524997859637)
              ·
                refine ⟨34560880599915611718549341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368649393065766524997859637 34560880599915611718549341)
                ·
                  refine ⟨12960330224968354394456003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34560880599915611718549341 12960330224968354394456003)
                  ·
                    refine ⟨19440495337452531591684005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12960330224968354394456003 19440495337452531591684005)
                    ·
                      refine ⟨3645092875772349673440751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19440495337452531591684005 3645092875772349673440751)
                      ·
                        rfl

theorem cell23_7098793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_7098793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098793 prefixEnd_7098793 := by exact prefixLift 7098793
  have htrace : WordTrace (prefixWord ++ tailWord_7098793) baseStart_7098793 baseEnd_7098793 := by
    simpa [prefixWord, tailWord_7098793, baseEnd_7098793] using wordTrace_append hprefix tailTrace_7098793
  have hstable : (prefixWord ++ tailWord_7098793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098793).length < 2 ^ (prefixWord ++ tailWord_7098793).sum := by decide
  have hdescent : baseEnd_7098793 < baseStart_7098793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098823 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_7098823 : Nat := 118140960795 + 7098823 * 2 ^ 59
def prefixEnd_7098823 : Nat := 4983230072969 + 3 ^ 40 * 7098823 * 2
def baseEnd_7098823 : Nat := 3645108280191984556065613

theorem tailTrace_7098823 : CollatzResearch.WordTrace tailWord_7098823 prefixEnd_7098823 3645108280191984556065613 := by
  unfold tailWord_7098823
  simp only [CollatzResearch.WordTrace]
  refine ⟨258915345561184128290813123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172610230374122752193875415 258915345561184128290813123)
  ·
    refine ⟨388373018341776192436219685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258915345561184128290813123 388373018341776192436219685)
    ·
      refine ⟨72819940939083036081791191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388373018341776192436219685 72819940939083036081791191)
      ·
        refine ⟨109229911408624554122686787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72819940939083036081791191 109229911408624554122686787)
        ·
          refine ⟨163844867112936831184030181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109229911408624554122686787 163844867112936831184030181)
          ·
            refine ⟨30720912583675655847005659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163844867112936831184030181 30720912583675655847005659)
            ·
              refine ⟨46081368875513483770508489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720912583675655847005659 46081368875513483770508489)
              ·
                refine ⟨34561026656635112827881367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46081368875513483770508489 34561026656635112827881367)
                ·
                  refine ⟨51841539984952669241822051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34561026656635112827881367 51841539984952669241822051)
                  ·
                    refine ⟨77762309977429003862733077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51841539984952669241822051 77762309977429003862733077)
                    ·
                      refine ⟨3645108280191984556065613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77762309977429003862733077 3645108280191984556065613)
                      ·
                        rfl

theorem cell23_7098823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_7098823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098823 prefixEnd_7098823 := by exact prefixLift 7098823
  have htrace : WordTrace (prefixWord ++ tailWord_7098823) baseStart_7098823 baseEnd_7098823 := by
    simpa [prefixWord, tailWord_7098823, baseEnd_7098823] using wordTrace_append hprefix tailTrace_7098823
  have hstable : (prefixWord ++ tailWord_7098823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098823).length < 2 ^ (prefixWord ++ tailWord_7098823).sum := by decide
  have hdescent : baseEnd_7098823 < baseStart_7098823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098830 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_7098830 : Nat := 118140960795 + 7098830 * 2 ^ 59
def prefixEnd_7098830 : Nat := 4983230072969 + 3 ^ 40 * 7098830 * 2
def baseEnd_7098830 : Nat := 3645111874556566028678081

theorem tailTrace_7098830 : CollatzResearch.WordTrace tailWord_7098830 prefixEnd_7098830 3645111874556566028678081 := by
  unfold tailWord_7098830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364450109019846060789743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172610400581439178990878629 32364450109019846060789743)
  ·
    refine ⟨48546675163529769091184615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364450109019846060789743 48546675163529769091184615)
    ·
      refine ⟨72820012745294653636776923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48546675163529769091184615 72820012745294653636776923)
      ·
        refine ⟨109230019117941980455165385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72820012745294653636776923 109230019117941980455165385)
        ·
          refine ⟨81922514338456485341374039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109230019117941980455165385 81922514338456485341374039)
          ·
            refine ⟨122883771507684728012061059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81922514338456485341374039 122883771507684728012061059)
            ·
              refine ⟨184325657261527092018091589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122883771507684728012061059 184325657261527092018091589)
              ·
                refine ⟨34561060736536329753392173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184325657261527092018091589 34561060736536329753392173)
                ·
                  refine ⟨12960397776201123657522065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34561060736536329753392173 12960397776201123657522065)
                  ·
                    refine ⟨9720298332150842743141549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12960397776201123657522065 9720298332150842743141549)
                    ·
                      refine ⟨3645111874556566028678081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720298332150842743141549 3645111874556566028678081)
                      ·
                        rfl

theorem cell23_7098830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_7098830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098830 prefixEnd_7098830 := by exact prefixLift 7098830
  have htrace : WordTrace (prefixWord ++ tailWord_7098830) baseStart_7098830 baseEnd_7098830 := by
    simpa [prefixWord, tailWord_7098830, baseEnd_7098830] using wordTrace_append hprefix tailTrace_7098830
  have hstable : (prefixWord ++ tailWord_7098830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098830).length < 2 ^ (prefixWord ++ tailWord_7098830).sum := by decide
  have hdescent : baseEnd_7098830 < baseStart_7098830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098837 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_7098837 : Nat := 118140960795 + 7098837 * 2 ^ 59
def prefixEnd_7098837 : Nat := 4983230072969 + 3 ^ 40 * 7098837 * 2
def baseEnd_7098837 : Nat := 1215038489640382500430183

theorem tailTrace_7098837 : CollatzResearch.WordTrace tailWord_7098837 prefixEnd_7098837 1215038489640382500430183 := by
  unfold tailWord_7098837
  simp only [CollatzResearch.WordTrace]
  refine ⟨258915856183133408681822765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172610570788755605787881843 258915856183133408681822765)
  ·
    refine ⟨97093446068675028255683537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258915856183133408681822765 97093446068675028255683537)
    ·
      refine ⟨72820084551506271191762653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97093446068675028255683537 72820084551506271191762653)
      ·
        refine ⟨27307531706814851696910995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72820084551506271191762653 27307531706814851696910995)
        ·
          refine ⟨40961297560222277545366493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27307531706814851696910995 40961297560222277545366493)
          ·
            refine ⟨15360486585083354079512435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40961297560222277545366493 15360486585083354079512435)
            ·
              refine ⟨23040729877625031119268653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15360486585083354079512435 23040729877625031119268653)
              ·
                refine ⟨8640273704109386669725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23040729877625031119268653 8640273704109386669725745)
                ·
                  refine ⟨6480205278082040002294309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640273704109386669725745 6480205278082040002294309)
                  ·
                    refine ⟨1215038489640382500430183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480205278082040002294309 1215038489640382500430183)
                    ·
                      rfl

theorem cell23_7098837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_7098837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098837 prefixEnd_7098837 := by exact prefixLift 7098837
  have htrace : WordTrace (prefixWord ++ tailWord_7098837) baseStart_7098837 baseEnd_7098837 := by
    simpa [prefixWord, tailWord_7098837, baseEnd_7098837] using wordTrace_append hprefix tailTrace_7098837
  have hstable : (prefixWord ++ tailWord_7098837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098837).length < 2 ^ (prefixWord ++ tailWord_7098837).sum := by decide
  have hdescent : baseEnd_7098837 < baseStart_7098837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098847 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_7098847 : Nat := 118140960795 + 7098847 * 2 ^ 59
def prefixEnd_7098847 : Nat := 4983230072969 + 3 ^ 40 * 7098847 * 2
def baseEnd_7098847 : Nat := 3645120603727692462165503

theorem tailTrace_7098847 : CollatzResearch.WordTrace tailWord_7098847 prefixEnd_7098847 3645120603727692462165503 := by
  unfold tailWord_7098847
  simp only [CollatzResearch.WordTrace]
  refine ⟨258916220913097180389686795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172610813942064786926457863 258916220913097180389686795)
  ·
    refine ⟨388374331369645770584530193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258916220913097180389686795 388374331369645770584530193)
    ·
      refine ⟨291280748527234327938397645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388374331369645770584530193 291280748527234327938397645)
      ·
        refine ⟨109230280697712872976899117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291280748527234327938397645 109230280697712872976899117)
        ·
          refine ⟨40961355261642327366337169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109230280697712872976899117 40961355261642327366337169)
          ·
            refine ⟨30721016446231745524752877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40961355261642327366337169 30721016446231745524752877)
            ·
              refine ⟨11520381167336904571782329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30721016446231745524752877 11520381167336904571782329)
              ·
                refine ⟨8640285875502678428836747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11520381167336904571782329 8640285875502678428836747)
                ·
                  refine ⟨12960428813254017643255121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640285875502678428836747 12960428813254017643255121)
                  ·
                    refine ⟨9720321609940513232441341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12960428813254017643255121 9720321609940513232441341)
                    ·
                      refine ⟨3645120603727692462165503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720321609940513232441341 3645120603727692462165503)
                      ·
                        rfl

theorem cell23_7098847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_7098847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098847 prefixEnd_7098847 := by exact prefixLift 7098847
  have htrace : WordTrace (prefixWord ++ tailWord_7098847) baseStart_7098847 baseEnd_7098847 := by
    simpa [prefixWord, tailWord_7098847, baseEnd_7098847] using wordTrace_append hprefix tailTrace_7098847
  have hstable : (prefixWord ++ tailWord_7098847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098847).length < 2 ^ (prefixWord ++ tailWord_7098847).sum := by decide
  have hdescent : baseEnd_7098847 < baseStart_7098847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098860 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_7098860 : Nat := 118140960795 + 7098860 * 2 ^ 59
def prefixEnd_7098860 : Nat := 4983230072969 + 3 ^ 40 * 7098860 * 2
def baseEnd_7098860 : Nat := 3645127278976200911302943

theorem tailTrace_7098860 : CollatzResearch.WordTrace tailWord_7098860 prefixEnd_7098860 3645127278976200911302943 := by
  unfold tailWord_7098860
  simp only [CollatzResearch.WordTrace]
  refine ⟨129458347531025041804955017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172611130041366722406606689 129458347531025041804955017)
  ·
    refine ⟨97093760648268781353716263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129458347531025041804955017 97093760648268781353716263)
    ·
      refine ⟨145640640972403172030574395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97093760648268781353716263 145640640972403172030574395)
      ·
        refine ⟨218460961458604758045861593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145640640972403172030574395 218460961458604758045861593)
        ·
          refine ⟨163845721093953568534396195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218460961458604758045861593 163845721093953568534396195)
          ·
            refine ⟨245768581640930352801594293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163845721093953568534396195 245768581640930352801594293)
            ·
              refine ⟨23040804528837220575149465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245768581640930352801594293 23040804528837220575149465)
              ·
                refine ⟨17280603396627915431362099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23040804528837220575149465 17280603396627915431362099)
                ·
                  refine ⟨25920905094941873147043149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17280603396627915431362099 25920905094941873147043149)
                  ·
                    refine ⟨9720339410603202430141181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25920905094941873147043149 9720339410603202430141181)
                    ·
                      refine ⟨3645127278976200911302943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720339410603202430141181 3645127278976200911302943)
                      ·
                        rfl

theorem cell23_7098860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_7098860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098860 prefixEnd_7098860 := by exact prefixLift 7098860
  have htrace : WordTrace (prefixWord ++ tailWord_7098860) baseStart_7098860 baseEnd_7098860 := by
    simpa [prefixWord, tailWord_7098860, baseEnd_7098860] using wordTrace_append hprefix tailTrace_7098860
  have hstable : (prefixWord ++ tailWord_7098860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098860).length < 2 ^ (prefixWord ++ tailWord_7098860).sum := by decide
  have hdescent : baseEnd_7098860 < baseStart_7098860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098873 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7098873 : Nat := 118140960795 + 7098873 * 2 ^ 59
def prefixEnd_7098873 : Nat := 4983230072969 + 3 ^ 40 * 7098873 * 2
def baseEnd_7098873 : Nat := 3645133954224709360440383

theorem tailTrace_7098873 : CollatzResearch.WordTrace tailWord_7098873 prefixEnd_7098873 3645133954224709360440383 := by
  unfold tailWord_7098873
  simp only [CollatzResearch.WordTrace]
  refine ⟨258917169211002986830133273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172611446140668657886755515 258917169211002986830133273)
  ·
    refine ⟨194187876908252240122599955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258917169211002986830133273 194187876908252240122599955)
    ·
      refine ⟨291281815362378360183899933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194187876908252240122599955 291281815362378360183899933)
      ·
        refine ⟨109230680760891885068962475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291281815362378360183899933 109230680760891885068962475)
        ·
          refine ⟨163846021141337827603443713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109230680760891885068962475 163846021141337827603443713)
          ·
            refine ⟨122884515856003370702582785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163846021141337827603443713 122884515856003370702582785)
            ·
              refine ⟨92163386892002528026937089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122884515856003370702582785 92163386892002528026937089)
              ·
                refine ⟨69122540169001896020202817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92163386892002528026937089 69122540169001896020202817)
                ·
                  refine ⟨51841905126751422015152113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69122540169001896020202817 51841905126751422015152113)
                  ·
                    refine ⟨38881428845063566511364085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51841905126751422015152113 38881428845063566511364085)
                    ·
                      refine ⟨3645133954224709360440383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38881428845063566511364085 3645133954224709360440383)
                      ·
                        rfl

theorem cell23_7098873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7098873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098873 prefixEnd_7098873 := by exact prefixLift 7098873
  have htrace : WordTrace (prefixWord ++ tailWord_7098873) baseStart_7098873 baseEnd_7098873 := by
    simpa [prefixWord, tailWord_7098873, baseEnd_7098873] using wordTrace_append hprefix tailTrace_7098873
  have hstable : (prefixWord ++ tailWord_7098873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098873).length < 2 ^ (prefixWord ++ tailWord_7098873).sum := by decide
  have hdescent : baseEnd_7098873 < baseStart_7098873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098883 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_7098883 : Nat := 118140960795 + 7098883 * 2 ^ 59
def prefixEnd_7098883 : Nat := 4983230072969 + 3 ^ 40 * 7098883 * 2
def baseEnd_7098883 : Nat := 3645139089031254321315337

theorem tailTrace_7098883 : CollatzResearch.WordTrace tailWord_7098883 prefixEnd_7098883 3645139089031254321315337 := by
  unfold tailWord_7098883
  simp only [CollatzResearch.WordTrace]
  refine ⟨258917533940966758537997303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172611689293977839025331535 258917533940966758537997303)
  ·
    refine ⟨388376300911450137806995955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258917533940966758537997303 388376300911450137806995955)
    ·
      refine ⟨582564451367175206710493933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388376300911450137806995955 582564451367175206710493933)
      ·
        refine ⟨218461669262690702516435225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582564451367175206710493933 218461669262690702516435225)
        ·
          refine ⟨163846251947018026887326419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218461669262690702516435225 163846251947018026887326419)
          ·
            refine ⟨245769377920527040330989629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163846251947018026887326419 245769377920527040330989629)
            ·
              refine ⟨92163516720197640124121111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245769377920527040330989629 92163516720197640124121111)
              ·
                refine ⟨138245275080296460186181667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92163516720197640124121111 138245275080296460186181667)
                ·
                  refine ⟨207367912620444690279272501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138245275080296460186181667 207367912620444690279272501)
                  ·
                    refine ⟨19440741808166689713681797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207367912620444690279272501 19440741808166689713681797)
                    ·
                      refine ⟨3645139089031254321315337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19440741808166689713681797 3645139089031254321315337)
                      ·
                        rfl

theorem cell23_7098883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_7098883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098883 prefixEnd_7098883 := by exact prefixLift 7098883
  have htrace : WordTrace (prefixWord ++ tailWord_7098883) baseStart_7098883 baseEnd_7098883 := by
    simpa [prefixWord, tailWord_7098883, baseEnd_7098883] using wordTrace_append hprefix tailTrace_7098883
  have hstable : (prefixWord ++ tailWord_7098883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098883).length < 2 ^ (prefixWord ++ tailWord_7098883).sum := by decide
  have hdescent : baseEnd_7098883 < baseStart_7098883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098894 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7098894 : Nat := 118140960795 + 7098894 * 2 ^ 59
def prefixEnd_7098894 : Nat := 4983230072969 + 3 ^ 40 * 7098894 * 2
def baseEnd_7098894 : Nat := 3645144737318453778277787

theorem tailTrace_7098894 : CollatzResearch.WordTrace tailWord_7098894 prefixEnd_7098894 3645144737318453778277787 := by
  unfold tailWord_7098894
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364741892990863427080967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172611956762617938277765157 32364741892990863427080967)
  ·
    refine ⟨48547112839486295140621451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364741892990863427080967 48547112839486295140621451)
    ·
      refine ⟨72820669259229442710932177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48547112839486295140621451 72820669259229442710932177)
      ·
        refine ⟨54615501944422082033199133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72820669259229442710932177 54615501944422082033199133)
        ·
          refine ⟨20480813229158280762449675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54615501944422082033199133 20480813229158280762449675)
          ·
            refine ⟨30721219843737421143674513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480813229158280762449675 30721219843737421143674513)
            ·
              refine ⟨23040914882803065857755885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30721219843737421143674513 23040914882803065857755885)
              ·
                refine ⟨8640343081051149696658457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23040914882803065857755885 8640343081051149696658457)
                ·
                  refine ⟨6480257310788362272493843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640343081051149696658457 6480257310788362272493843)
                  ·
                    refine ⟨9720385966182543408740765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6480257310788362272493843 9720385966182543408740765)
                    ·
                      refine ⟨3645144737318453778277787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720385966182543408740765 3645144737318453778277787)
                      ·
                        rfl

theorem cell23_7098894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7098894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098894 prefixEnd_7098894 := by exact prefixLift 7098894
  have htrace : WordTrace (prefixWord ++ tailWord_7098894) baseStart_7098894 baseEnd_7098894 := by
    simpa [prefixWord, tailWord_7098894, baseEnd_7098894] using wordTrace_append hprefix tailTrace_7098894
  have hstable : (prefixWord ++ tailWord_7098894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098894).length < 2 ^ (prefixWord ++ tailWord_7098894).sum := by decide
  have hdescent : baseEnd_7098894 < baseStart_7098894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098917 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_7098917 : Nat := 118140960795 + 7098917 * 2 ^ 59
def prefixEnd_7098917 : Nat := 4983230072969 + 3 ^ 40 * 7098917 * 2
def baseEnd_7098917 : Nat := 3645156547373507188290181

theorem tailTrace_7098917 : CollatzResearch.WordTrace tailWord_7098917 prefixEnd_7098917 3645156547373507188290181 := by
  unfold tailWord_7098917
  simp only [CollatzResearch.WordTrace]
  refine ⟨258918774022843582344735005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172612516015229054896490003 258918774022843582344735005)
  ·
    refine ⟨97094540258566343379275627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258918774022843582344735005 97094540258566343379275627)
    ·
      refine ⟨145641810387849515068913441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97094540258566343379275627 145641810387849515068913441)
      ·
        refine ⟨109231357790887136301685081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145641810387849515068913441 109231357790887136301685081)
        ·
          refine ⟨81923518343165352226263811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109231357790887136301685081 81923518343165352226263811)
          ·
            refine ⟨122885277514748028339395717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81923518343165352226263811 122885277514748028339395717)
            ·
              refine ⟨23040989534015255313636697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122885277514748028339395717 23040989534015255313636697)
              ·
                refine ⟨17280742150511441485227523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23040989534015255313636697 17280742150511441485227523)
                ·
                  refine ⟨25921113225767162227841285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17280742150511441485227523 25921113225767162227841285)
                  ·
                    refine ⟨4860208729831342917720241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25921113225767162227841285 4860208729831342917720241)
                    ·
                      refine ⟨3645156547373507188290181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860208729831342917720241 3645156547373507188290181)
                      ·
                        rfl

theorem cell23_7098917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_7098917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098917 prefixEnd_7098917 := by exact prefixLift 7098917
  have htrace : WordTrace (prefixWord ++ tailWord_7098917) baseStart_7098917 baseEnd_7098917 := by
    simpa [prefixWord, tailWord_7098917, baseEnd_7098917] using wordTrace_append hprefix tailTrace_7098917
  have hstable : (prefixWord ++ tailWord_7098917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098917).length < 2 ^ (prefixWord ++ tailWord_7098917).sum := by decide
  have hdescent : baseEnd_7098917 < baseStart_7098917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098930 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7098930 : Nat := 118140960795 + 7098930 * 2 ^ 59
def prefixEnd_7098930 : Nat := 4983230072969 + 3 ^ 40 * 7098930 * 2
def baseEnd_7098930 : Nat := 3645163222622015637427621

theorem tailTrace_7098930 : CollatzResearch.WordTrace tailWord_7098930 prefixEnd_7098930 3645163222622015637427621 := by
  unfold tailWord_7098930
  simp only [CollatzResearch.WordTrace]
  refine ⟨64729812042949121391239561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172612832114530990376638829 64729812042949121391239561)
  ·
    refine ⟨48547359032211841043429671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64729812042949121391239561 48547359032211841043429671)
    ·
      refine ⟨72821038548317761565144507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48547359032211841043429671 72821038548317761565144507)
      ·
        refine ⟨109231557822476642347716761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72821038548317761565144507 109231557822476642347716761)
        ·
          refine ⟨81923668366857481760787571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109231557822476642347716761 81923668366857481760787571)
          ·
            refine ⟨122885502550286222641181357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81923668366857481760787571 122885502550286222641181357)
            ·
              refine ⟨46082063456357333490443009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122885502550286222641181357 46082063456357333490443009)
              ·
                refine ⟨34561547592268000117832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46082063456357333490443009 34561547592268000117832257)
                ·
                  refine ⟨25921160694201000088374193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34561547592268000117832257 25921160694201000088374193)
                  ·
                    refine ⟨19440870520650750066280645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25921160694201000088374193 19440870520650750066280645)
                    ·
                      refine ⟨3645163222622015637427621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19440870520650750066280645 3645163222622015637427621)
                      ·
                        rfl

theorem cell23_7098930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7098930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098930 prefixEnd_7098930 := by exact prefixLift 7098930
  have htrace : WordTrace (prefixWord ++ tailWord_7098930) baseStart_7098930 baseEnd_7098930 := by
    simpa [prefixWord, tailWord_7098930, baseEnd_7098930] using wordTrace_append hprefix tailTrace_7098930
  have hstable : (prefixWord ++ tailWord_7098930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098930).length < 2 ^ (prefixWord ++ tailWord_7098930).sum := by decide
  have hdescent : baseEnd_7098930 < baseStart_7098930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098940 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 7]
def baseStart_7098940 : Nat := 118140960795 + 7098940 * 2 ^ 59
def prefixEnd_7098940 : Nat := 4983230072969 + 3 ^ 40 * 7098940 * 2
def baseEnd_7098940 : Nat := 405018706380951177589175

theorem tailTrace_7098940 : CollatzResearch.WordTrace tailWord_7098940 prefixEnd_7098940 405018706380951177589175 := by
  unfold tailWord_7098940
  simp only [CollatzResearch.WordTrace]
  refine ⟨129459806450880128636411137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172613075267840171515214849 129459806450880128636411137)
  ·
    refine ⟨97094854838160096477308353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129459806450880128636411137 97094854838160096477308353)
    ·
      refine ⟨72821141128620072357981265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97094854838160096477308353 72821141128620072357981265)
      ·
        refine ⟨54615855846465054268485949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72821141128620072357981265 54615855846465054268485949)
        ·
          refine ⟨20480945942424395350682231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54615855846465054268485949 20480945942424395350682231)
          ·
            refine ⟨30721418913636593026023347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480945942424395350682231 30721418913636593026023347)
            ·
              refine ⟨46082128370454889539035021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30721418913636593026023347 46082128370454889539035021)
              ·
                refine ⟨17280798138920583577138133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46082128370454889539035021 17280798138920583577138133)
                ·
                  refine ⟨405018706380951177589175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17280798138920583577138133 405018706380951177589175)
                  ·
                    rfl

theorem cell23_7098940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_7098940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098940 prefixEnd_7098940 := by exact prefixLift 7098940
  have htrace : WordTrace (prefixWord ++ tailWord_7098940) baseStart_7098940 baseEnd_7098940 := by
    simpa [prefixWord, tailWord_7098940, baseEnd_7098940] using wordTrace_append hprefix tailTrace_7098940
  have hstable : (prefixWord ++ tailWord_7098940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098940).length < 2 ^ (prefixWord ++ tailWord_7098940).sum := by decide
  have hdescent : baseEnd_7098940 < baseStart_7098940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098957 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7098957 : Nat := 118140960795 + 7098957 * 2 ^ 59
def prefixEnd_7098957 : Nat := 4983230072969 + 3 ^ 40 * 7098957 * 2
def baseEnd_7098957 : Nat := 405019676288854114643333

theorem tailTrace_7098957 : CollatzResearch.WordTrace tailWord_7098957 prefixEnd_7098957 405019676288854114643333 := by
  unfold tailWord_7098957
  simp only [CollatzResearch.WordTrace]
  refine ⟨258920232942698669176191125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172613488628465779450794083 258920232942698669176191125)
  ·
    refine ⟨12136885919189000117633959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258920232942698669176191125 12136885919189000117633959)
    ·
      refine ⟨18205328878783500176450939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12136885919189000117633959 18205328878783500176450939)
      ·
        refine ⟨27307993318175250264676409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18205328878783500176450939 27307993318175250264676409)
        ·
          refine ⟨20480994988631437698507307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27307993318175250264676409 20480994988631437698507307)
          ·
            refine ⟨30721492482947156547760961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480994988631437698507307 30721492482947156547760961)
            ·
              refine ⟨23041119362210367410820721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30721492482947156547760961 23041119362210367410820721)
              ·
                refine ⟨17280839521657775558115541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23041119362210367410820721 17280839521657775558115541)
                ·
                  refine ⟨405019676288854114643333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17280839521657775558115541 405019676288854114643333)
                  ·
                    rfl

theorem cell23_7098957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7098957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098957 prefixEnd_7098957 := by exact prefixLift 7098957
  have htrace : WordTrace (prefixWord ++ tailWord_7098957) baseStart_7098957 baseEnd_7098957 := by
    simpa [prefixWord, tailWord_7098957, baseEnd_7098957] using wordTrace_append hprefix tailTrace_7098957
  have hstable : (prefixWord ++ tailWord_7098957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098957).length < 2 ^ (prefixWord ++ tailWord_7098957).sum := by decide
  have hdescent : baseEnd_7098957 < baseStart_7098957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7098980 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_7098980 : Nat := 118140960795 + 7098980 * 2 ^ 59
def prefixEnd_7098980 : Nat := 4983230072969 + 3 ^ 40 * 7098980 * 2
def baseEnd_7098980 : Nat := 3645188896654740441802391

theorem tailTrace_7098980 : CollatzResearch.WordTrace tailWord_7098980 prefixEnd_7098980 3645188896654740441802391 := by
  unfold tailWord_7098980
  simp only [CollatzResearch.WordTrace]
  refine ⟨129460535910807672052139197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172614047881076896069518929 129460535910807672052139197)
  ·
    refine ⟨48547700966552877019552199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129460535910807672052139197 48547700966552877019552199)
    ·
      refine ⟨72821551449829315529328299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48547700966552877019552199 72821551449829315529328299)
      ·
        refine ⟨109232327174743973293992449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72821551449829315529328299 109232327174743973293992449)
        ·
          refine ⟨81924245381057979970494337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109232327174743973293992449 81924245381057979970494337)
          ·
            refine ⟨61443184035793484977870753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81924245381057979970494337 61443184035793484977870753)
            ·
              refine ⟨46082388026845113733403065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61443184035793484977870753 46082388026845113733403065)
              ·
                refine ⟨34561791020133835300052299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46082388026845113733403065 34561791020133835300052299)
                ·
                  refine ⟨51842686530200752950078449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34561791020133835300052299 51842686530200752950078449)
                  ·
                    refine ⟨38882014897650564712558837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51842686530200752950078449 38882014897650564712558837)
                    ·
                      refine ⟨3645188896654740441802391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38882014897650564712558837 3645188896654740441802391)
                      ·
                        rfl

theorem cell23_7098980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_7098980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7098980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7098980 prefixEnd_7098980 := by exact prefixLift 7098980
  have htrace : WordTrace (prefixWord ++ tailWord_7098980) baseStart_7098980 baseEnd_7098980 := by
    simpa [prefixWord, tailWord_7098980, baseEnd_7098980] using wordTrace_append hprefix tailTrace_7098980
  have hstable : (prefixWord ++ tailWord_7098980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7098980).length < 2 ^ (prefixWord ++ tailWord_7098980).sum := by decide
  have hdescent : baseEnd_7098980 < baseStart_7098980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7098980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099078 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7099078 : Nat := 118140960795 + 7099078 * 2 ^ 59
def prefixEnd_7099078 : Nat := 4983230072969 + 3 ^ 40 * 7099078 * 2
def baseEnd_7099078 : Nat := 3645239217758881058376941

theorem tailTrace_7099078 : CollatzResearch.WordTrace tailWord_7099078 prefixEnd_7099078 3645239217758881058376941 := by
  unfold tailWord_7099078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091395192976884588792059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172616430783506871227563925 8091395192976884588792059)
  ·
    refine ⟨12137092789465326883188089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8091395192976884588792059 12137092789465326883188089)
    ·
      refine ⟨9102819592098995162391067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12137092789465326883188089 9102819592098995162391067)
      ·
        refine ⟨13654229388148492743586601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102819592098995162391067 13654229388148492743586601)
        ·
          refine ⟨10240672041111369557689951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654229388148492743586601 10240672041111369557689951)
          ·
            refine ⟨15361008061667054336534927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240672041111369557689951 15361008061667054336534927)
            ·
              refine ⟨23041512092500581504802391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15361008061667054336534927 23041512092500581504802391)
              ·
                refine ⟨34562268138750872257203587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23041512092500581504802391 34562268138750872257203587)
                ·
                  refine ⟨51843402208126308385805381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34562268138750872257203587 51843402208126308385805381)
                  ·
                    refine ⟨9720637914023682822338509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51843402208126308385805381 9720637914023682822338509)
                    ·
                      refine ⟨3645239217758881058376941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720637914023682822338509 3645239217758881058376941)
                      ·
                        rfl

theorem cell23_7099078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7099078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099078 prefixEnd_7099078 := by exact prefixLift 7099078
  have htrace : WordTrace (prefixWord ++ tailWord_7099078) baseStart_7099078 baseEnd_7099078 := by
    simpa [prefixWord, tailWord_7099078, baseEnd_7099078] using wordTrace_append hprefix tailTrace_7099078
  have hstable : (prefixWord ++ tailWord_7099078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099078).length < 2 ^ (prefixWord ++ tailWord_7099078).sum := by decide
  have hdescent : baseEnd_7099078 < baseStart_7099078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099085 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7099085 : Nat := 118140960795 + 7099085 * 2 ^ 59
def prefixEnd_7099085 : Nat := 4983230072969 + 3 ^ 40 * 7099085 * 2
def baseEnd_7099085 : Nat := 1215080937374487510329803

theorem tailTrace_7099085 : CollatzResearch.WordTrace tailWord_7099085 prefixEnd_7099085 1215080937374487510329803 := by
  unfold tailWord_7099085
  simp only [CollatzResearch.WordTrace]
  refine ⟨258924901486234947036850709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172616600990823298024567139 258924901486234947036850709)
  ·
    refine ⟨12137104757167263142352377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258924901486234947036850709 12137104757167263142352377)
    ·
      refine ⟨9102828567875447356764283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12137104757167263142352377 9102828567875447356764283)
      ·
        refine ⟨13654242851813171035146425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102828567875447356764283 13654242851813171035146425)
        ·
          refine ⟨10240682138859878276359819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654242851813171035146425 10240682138859878276359819)
          ·
            refine ⟨15361023208289817414539729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240682138859878276359819 15361023208289817414539729)
            ·
              refine ⟨11520767406217363060904797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15361023208289817414539729 11520767406217363060904797)
              ·
                refine ⟨4320287777331511147839299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11520767406217363060904797 4320287777331511147839299)
                ·
                  refine ⟨6480431665997266721758949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320287777331511147839299 6480431665997266721758949)
                  ·
                    refine ⟨1215080937374487510329803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6480431665997266721758949 1215080937374487510329803)
                    ·
                      rfl

theorem cell23_7099085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7099085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099085 prefixEnd_7099085 := by exact prefixLift 7099085
  have htrace : WordTrace (prefixWord ++ tailWord_7099085) baseStart_7099085 baseEnd_7099085 := by
    simpa [prefixWord, tailWord_7099085, baseEnd_7099085] using wordTrace_append hprefix tailTrace_7099085
  have hstable : (prefixWord ++ tailWord_7099085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099085).length < 2 ^ (prefixWord ++ tailWord_7099085).sum := by decide
  have hdescent : baseEnd_7099085 < baseStart_7099085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099120 : List Nat := [2, 1, 1, 1, 3, 1, 4, 10]
def baseStart_7099120 : Nat := 118140960795 + 7099120 * 2 ^ 59
def prefixEnd_7099120 : Nat := 4983230072969 + 3 ^ 40 * 7099120 * 2
def baseEnd_7099120 : Nat := 135009658664680366446361

theorem tailTrace_7099120 : CollatzResearch.WordTrace tailWord_7099120 prefixEnd_7099120 135009658664680366446361 := by
  unfold tailWord_7099120
  simp only [CollatzResearch.WordTrace]
  refine ⟨129463089020554074007187407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172617452027405432009583209 129463089020554074007187407)
  ·
    refine ⟨194194633530831111010781111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129463089020554074007187407 194194633530831111010781111)
    ·
      refine ⟨291291950296246666516171667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194194633530831111010781111 291291950296246666516171667)
      ·
        refine ⟨436937925444369999774257501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291291950296246666516171667 436937925444369999774257501)
        ·
          refine ⟨163851722041638749915346563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436937925444369999774257501 163851722041638749915346563)
          ·
            refine ⟨245777583062458124873019845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163851722041638749915346563 245777583062458124873019845)
            ·
              refine ⟨46083296824210898413691221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245777583062458124873019845 46083296824210898413691221)
              ·
                refine ⟨135009658664680366446361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46083296824210898413691221 135009658664680366446361)
                ·
                  rfl

theorem cell23_7099120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_7099120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099120 prefixEnd_7099120 := by exact prefixLift 7099120
  have htrace : WordTrace (prefixWord ++ tailWord_7099120) baseStart_7099120 baseEnd_7099120 := by
    simpa [prefixWord, tailWord_7099120, baseEnd_7099120] using wordTrace_append hprefix tailTrace_7099120
  have hstable : (prefixWord ++ tailWord_7099120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099120).length < 2 ^ (prefixWord ++ tailWord_7099120).sum := by decide
  have hdescent : baseEnd_7099120 < baseStart_7099120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099147 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3]
def baseStart_7099147 : Nat := 118140960795 + 7099147 * 2 ^ 59
def prefixEnd_7099147 : Nat := 4983230072969 + 3 ^ 40 * 7099147 * 2
def baseEnd_7099147 : Nat := 3645274647924041288414123

theorem tailTrace_7099147 : CollatzResearch.WordTrace tailWord_7099147 prefixEnd_7099147 3645274647924041288414123 := by
  unfold tailWord_7099147
  simp only [CollatzResearch.WordTrace]
  refine ⟨258927162812010331625607695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172618108541340221083738463 258927162812010331625607695)
  ·
    refine ⟨388390744218015497438411543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258927162812010331625607695 388390744218015497438411543)
    ·
      refine ⟨582586116327023246157617315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388390744218015497438411543 582586116327023246157617315)
      ·
        refine ⟨873879174490534869236425973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582586116327023246157617315 873879174490534869236425973)
        ·
          refine ⟨81926172608487643990914935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 873879174490534869236425973 81926172608487643990914935)
          ·
            refine ⟨122889258912731465986372403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81926172608487643990914935 122889258912731465986372403)
            ·
              refine ⟨184333888369097198979558605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122889258912731465986372403 184333888369097198979558605)
              ·
                refine ⟨69125208138411449617334477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184333888369097198979558605 69125208138411449617334477)
                ·
                  refine ⟨25921953051904293606500429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69125208138411449617334477 25921953051904293606500429)
                  ·
                    refine ⟨9720732394464110102437661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25921953051904293606500429 9720732394464110102437661)
                    ·
                      refine ⟨3645274647924041288414123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9720732394464110102437661 3645274647924041288414123)
                      ·
                        rfl

theorem cell23_7099147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].length) (baseStart_7099147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099147 prefixEnd_7099147 := by exact prefixLift 7099147
  have htrace : WordTrace (prefixWord ++ tailWord_7099147) baseStart_7099147 baseEnd_7099147 := by
    simpa [prefixWord, tailWord_7099147, baseEnd_7099147] using wordTrace_append hprefix tailTrace_7099147
  have hstable : (prefixWord ++ tailWord_7099147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099147).length < 2 ^ (prefixWord ++ tailWord_7099147).sum := by decide
  have hdescent : baseEnd_7099147 < baseStart_7099147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099208 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_7099208 : Nat := 118140960795 + 7099208 * 2 ^ 59
def prefixEnd_7099208 : Nat := 4983230072969 + 3 ^ 40 * 7099208 * 2
def baseEnd_7099208 : Nat := 3645305970243965549751343

theorem tailTrace_7099208 : CollatzResearch.WordTrace tailWord_7099208 prefixEnd_7099208 3645305970243965549751343 := by
  unfold tailWord_7099208
  simp only [CollatzResearch.WordTrace]
  refine ⟨129464693832394669521789139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172619591776526226029052185 129464693832394669521789139)
  ·
    refine ⟨194197040748592004282683709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129464693832394669521789139 194197040748592004282683709)
    ·
      refine ⟨72823890280722001606006391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194197040748592004282683709 72823890280722001606006391)
      ·
        refine ⟨109235835421083002409009587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72823890280722001606006391 109235835421083002409009587)
        ·
          refine ⟨163853753131624503613514381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109235835421083002409009587 163853753131624503613514381)
          ·
            refine ⟨61445157424359188855067893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163853753131624503613514381 61445157424359188855067893)
            ·
              refine ⟨5760483508533673955162615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61445157424359188855067893 5760483508533673955162615)
              ·
                refine ⟨8640725262800510932743923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760483508533673955162615 8640725262800510932743923)
                ·
                  refine ⟨12961087894200766399115885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640725262800510932743923 12961087894200766399115885)
                  ·
                    refine ⟨4860407960325287399668457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12961087894200766399115885 4860407960325287399668457)
                    ·
                      refine ⟨3645305970243965549751343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860407960325287399668457 3645305970243965549751343)
                      ·
                        rfl

theorem cell23_7099208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_7099208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099208 prefixEnd_7099208 := by exact prefixLift 7099208
  have htrace : WordTrace (prefixWord ++ tailWord_7099208) baseStart_7099208 baseEnd_7099208 := by
    simpa [prefixWord, tailWord_7099208, baseEnd_7099208] using wordTrace_append hprefix tailTrace_7099208
  have hstable : (prefixWord ++ tailWord_7099208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099208).length < 2 ^ (prefixWord ++ tailWord_7099208).sum := by decide
  have hdescent : baseEnd_7099208 < baseStart_7099208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099264 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2]
def baseStart_7099264 : Nat := 118140960795 + 7099264 * 2 ^ 59
def prefixEnd_7099264 : Nat := 4983230072969 + 3 ^ 40 * 7099264 * 2
def baseEnd_7099264 : Nat := 3645334725160617330651085

theorem tailTrace_7099264 : CollatzResearch.WordTrace tailWord_7099264 prefixEnd_7099264 3645334725160617330651085 := by
  unfold tailWord_7099264
  simp only [CollatzResearch.WordTrace]
  refine ⟨129465715076293230303808423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172620953435057640405077897 129465715076293230303808423)
  ·
    refine ⟨194198572614439845455712635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129465715076293230303808423 194198572614439845455712635)
    ·
      refine ⟨291297858921659768183568953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194198572614439845455712635 291297858921659768183568953)
      ·
        refine ⟨218473394191244826137676715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291297858921659768183568953 218473394191244826137676715)
        ·
          refine ⟨327710091286867239206515073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218473394191244826137676715 327710091286867239206515073)
          ·
            refine ⟨245782568465150429404886305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327710091286867239206515073 245782568465150429404886305)
            ·
              refine ⟨184336926348862822053664729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245782568465150429404886305 184336926348862822053664729)
              ·
                refine ⟨138252694761647116540248547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184336926348862822053664729 138252694761647116540248547)
                ·
                  refine ⟨207379042142470674810372821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138252694761647116540248547 207379042142470674810372821)
                  ·
                    refine ⟨4860446300214156440868113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207379042142470674810372821 4860446300214156440868113)
                    ·
                      refine ⟨3645334725160617330651085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860446300214156440868113 3645334725160617330651085)
                      ·
                        rfl

theorem cell23_7099264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_7099264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099264 prefixEnd_7099264 := by exact prefixLift 7099264
  have htrace : WordTrace (prefixWord ++ tailWord_7099264) baseStart_7099264 baseEnd_7099264 := by
    simpa [prefixWord, tailWord_7099264, baseEnd_7099264] using wordTrace_append hprefix tailTrace_7099264
  have hstable : (prefixWord ++ tailWord_7099264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099264).length < 2 ^ (prefixWord ++ tailWord_7099264).sum := by decide
  have hdescent : baseEnd_7099264 < baseStart_7099264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099284 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7099284 : Nat := 118140960795 + 7099284 * 2 ^ 59
def prefixEnd_7099284 : Nat := 4983230072969 + 3 ^ 40 * 7099284 * 2
def baseEnd_7099284 : Nat := 3645344994773707252400993

theorem tailTrace_7099284 : CollatzResearch.WordTrace tailWord_7099284 prefixEnd_7099284 3645344994773707252400993 := by
  unfold tailWord_7099284
  simp only [CollatzResearch.WordTrace]
  refine ⟨129466079806257002011672453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172621439741676002682229937 129466079806257002011672453)
  ·
    refine ⟨24274889963673187877188585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129466079806257002011672453 24274889963673187877188585)
    ·
      refine ⟨18206167472754890907891439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24274889963673187877188585 18206167472754890907891439)
      ·
        refine ⟨27309251209132336361837159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18206167472754890907891439 27309251209132336361837159)
        ·
          refine ⟨40963876813698504542755739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27309251209132336361837159 40963876813698504542755739)
          ·
            refine ⟨61445815220547756814133609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40963876813698504542755739 61445815220547756814133609)
            ·
              refine ⟨46084361415410817610600207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61445815220547756814133609 46084361415410817610600207)
              ·
                refine ⟨69126542123116226415900311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46084361415410817610600207 69126542123116226415900311)
                ·
                  refine ⟨103689813184674339623850467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69126542123116226415900311 103689813184674339623850467)
                  ·
                    refine ⟨155534719777011509435775701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103689813184674339623850467 155534719777011509435775701)
                    ·
                      refine ⟨3645344994773707252400993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155534719777011509435775701 3645344994773707252400993)
                      ·
                        rfl

theorem cell23_7099284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7099284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099284 prefixEnd_7099284 := by exact prefixLift 7099284
  have htrace : WordTrace (prefixWord ++ tailWord_7099284) baseStart_7099284 baseEnd_7099284 := by
    simpa [prefixWord, tailWord_7099284, baseEnd_7099284] using wordTrace_append hprefix tailTrace_7099284
  have hstable : (prefixWord ++ tailWord_7099284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099284).length < 2 ^ (prefixWord ++ tailWord_7099284).sum := by decide
  have hdescent : baseEnd_7099284 < baseStart_7099284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099307 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_7099307 : Nat := 118140960795 + 7099307 * 2 ^ 59
def prefixEnd_7099307 : Nat := 4983230072969 + 3 ^ 40 * 7099307 * 2
def baseEnd_7099307 : Nat := 3645356804828760662413387

theorem tailTrace_7099307 : CollatzResearch.WordTrace tailWord_7099307 prefixEnd_7099307 3645356804828760662413387 := by
  unfold tailWord_7099307
  simp only [CollatzResearch.WordTrace]
  refine ⟨258932998491430678951432175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172621998994287119300954783 258932998491430678951432175)
  ·
    refine ⟨388399497737146018427148263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258932998491430678951432175 388399497737146018427148263)
    ·
      refine ⟨582599246605719027640722395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388399497737146018427148263 582599246605719027640722395)
      ·
        refine ⟨873898869908578541461083593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582599246605719027640722395 873898869908578541461083593)
        ·
          refine ⟨655424152431433906095812695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873898869908578541461083593 655424152431433906095812695)
          ·
            refine ⟨983136228647150859143719043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655424152431433906095812695 983136228647150859143719043)
            ·
              refine ⟨1474704342970726288715578565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983136228647150859143719043 1474704342970726288715578565)
              ·
                refine ⟨276507064307011179134170981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1474704342970726288715578565 276507064307011179134170981)
                ·
                  refine ⟨51845074557564596087657059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276507064307011179134170981 51845074557564596087657059)
                  ·
                    refine ⟨77767611836346894131485589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51845074557564596087657059 77767611836346894131485589)
                    ·
                      refine ⟨3645356804828760662413387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77767611836346894131485589 3645356804828760662413387)
                      ·
                        rfl

theorem cell23_7099307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_7099307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099307 prefixEnd_7099307 := by exact prefixLift 7099307
  have htrace : WordTrace (prefixWord ++ tailWord_7099307) baseStart_7099307 baseEnd_7099307 := by
    simpa [prefixWord, tailWord_7099307, baseEnd_7099307] using wordTrace_append hprefix tailTrace_7099307
  have hstable : (prefixWord ++ tailWord_7099307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099307).length < 2 ^ (prefixWord ++ tailWord_7099307).sum := by decide
  have hdescent : baseEnd_7099307 < baseStart_7099307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099361 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_7099361 : Nat := 118140960795 + 7099361 * 2 ^ 59
def prefixEnd_7099361 : Nat := 4983230072969 + 3 ^ 40 * 7099361 * 2
def baseEnd_7099361 : Nat := 3645384532784103451138139

theorem tailTrace_7099361 : CollatzResearch.WordTrace tailWord_7099361 prefixEnd_7099361 3645384532784103451138139 := by
  unfold tailWord_7099361
  simp only [CollatzResearch.WordTrace]
  refine ⟨258934968033235046173897937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172623312022156697449265291 258934968033235046173897937)
  ·
    refine ⟨194201226024926284630423453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258934968033235046173897937 194201226024926284630423453)
    ·
      refine ⟨72825459759347356736408795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194201226024926284630423453 72825459759347356736408795)
      ·
        refine ⟨109238189639021035104613193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72825459759347356736408795 109238189639021035104613193)
        ·
          refine ⟨81928642229265776328459895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109238189639021035104613193 81928642229265776328459895)
          ·
            refine ⟨122892963343898664492689843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81928642229265776328459895 122892963343898664492689843)
            ·
              refine ⟨184339445015847996739034765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122892963343898664492689843 184339445015847996739034765)
              ·
                refine ⟨69127291880942998777138037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184339445015847996739034765 69127291880942998777138037)
                ·
                  refine ⟨6480683613838406135356691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69127291880942998777138037 6480683613838406135356691)
                  ·
                    refine ⟨9721025420757609203035037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6480683613838406135356691 9721025420757609203035037)
                    ·
                      refine ⟨3645384532784103451138139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721025420757609203035037 3645384532784103451138139)
                      ·
                        rfl

theorem cell23_7099361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_7099361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099361 prefixEnd_7099361 := by exact prefixLift 7099361
  have htrace : WordTrace (prefixWord ++ tailWord_7099361) baseStart_7099361 baseEnd_7099361 := by
    simpa [prefixWord, tailWord_7099361, baseEnd_7099361] using wordTrace_append hprefix tailTrace_7099361
  have hstable : (prefixWord ++ tailWord_7099361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099361).length < 2 ^ (prefixWord ++ tailWord_7099361).sum := by decide
  have hdescent : baseEnd_7099361 < baseStart_7099361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099365 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7099365 : Nat := 118140960795 + 7099365 * 2 ^ 59
def prefixEnd_7099365 : Nat := 4983230072969 + 3 ^ 40 * 7099365 * 2
def baseEnd_7099365 : Nat := 3645386586706721435488121

theorem tailTrace_7099365 : CollatzResearch.WordTrace tailWord_7099365 prefixEnd_7099365 3645386586706721435488121 := by
  unfold tailWord_7099365
  simp only [CollatzResearch.WordTrace]
  refine ⟨258935113925220554857043549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172623409283480369904695699 258935113925220554857043549)
  ·
    refine ⟨97100667721957708071391331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258935113925220554857043549 97100667721957708071391331)
    ·
      refine ⟨145651001582936562107086997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97100667721957708071391331 145651001582936562107086997)
      ·
        refine ⟨6827390699200151348769703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145651001582936562107086997 6827390699200151348769703)
        ·
          refine ⟨10241086048800227023154555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827390699200151348769703 10241086048800227023154555)
          ·
            refine ⟨15361629073200340534731833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241086048800227023154555 15361629073200340534731833)
            ·
              refine ⟨11521221804900255401048875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15361629073200340534731833 11521221804900255401048875)
              ·
                refine ⟨17281832707350383101573313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521221804900255401048875 17281832707350383101573313)
                ·
                  refine ⟨12961374530512787326179985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17281832707350383101573313 12961374530512787326179985)
                  ·
                    refine ⟨9721030897884590494634989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12961374530512787326179985 9721030897884590494634989)
                    ·
                      refine ⟨3645386586706721435488121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721030897884590494634989 3645386586706721435488121)
                      ·
                        rfl

theorem cell23_7099365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7099365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099365 prefixEnd_7099365 := by exact prefixLift 7099365
  have htrace : WordTrace (prefixWord ++ tailWord_7099365) baseStart_7099365 baseEnd_7099365 := by
    simpa [prefixWord, tailWord_7099365, baseEnd_7099365] using wordTrace_append hprefix tailTrace_7099365
  have hstable : (prefixWord ++ tailWord_7099365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099365).length < 2 ^ (prefixWord ++ tailWord_7099365).sum := by decide
  have hdescent : baseEnd_7099365 < baseStart_7099365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099388 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_7099388 : Nat := 118140960795 + 7099388 * 2 ^ 59
def prefixEnd_7099388 : Nat := 4983230072969 + 3 ^ 40 * 7099388 * 2
def baseEnd_7099388 : Nat := 3645398396761774845500515

theorem tailTrace_7099388 : CollatzResearch.WordTrace tailWord_7099388 prefixEnd_7099388 3645398396761774845500515 := by
  unfold tailWord_7099388
  simp only [CollatzResearch.WordTrace]
  refine ⟨129467976402068614892565409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172623968536091486523420545 129467976402068614892565409)
  ·
    refine ⟨97100982301551461169424057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129467976402068614892565409 97100982301551461169424057)
    ·
      refine ⟨72825736726163595877068043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97100982301551461169424057 72825736726163595877068043)
      ·
        refine ⟨109238605089245393815602065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72825736726163595877068043 109238605089245393815602065)
        ·
          refine ⟨81928953816934045361701549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109238605089245393815602065 81928953816934045361701549)
          ·
            refine ⟨30723357681350267010638081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81928953816934045361701549 30723357681350267010638081)
            ·
              refine ⟨23042518261012700257978561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30723357681350267010638081 23042518261012700257978561)
              ·
                refine ⟨17281888695759525193483921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23042518261012700257978561 17281888695759525193483921)
                ·
                  refine ⟨12961416521819643895112941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17281888695759525193483921 12961416521819643895112941)
                  ·
                    refine ⟨4860531195682366460667353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12961416521819643895112941 4860531195682366460667353)
                    ·
                      refine ⟨3645398396761774845500515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860531195682366460667353 3645398396761774845500515)
                      ·
                        rfl

theorem cell23_7099388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_7099388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099388 prefixEnd_7099388 := by exact prefixLift 7099388
  have htrace : WordTrace (prefixWord ++ tailWord_7099388) baseStart_7099388 baseEnd_7099388 := by
    simpa [prefixWord, tailWord_7099388, baseEnd_7099388] using wordTrace_append hprefix tailTrace_7099388
  have hstable : (prefixWord ++ tailWord_7099388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099388).length < 2 ^ (prefixWord ++ tailWord_7099388).sum := by decide
  have hdescent : baseEnd_7099388 < baseStart_7099388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099452 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_7099452 : Nat := 118140960795 + 7099452 * 2 ^ 59
def prefixEnd_7099452 : Nat := 4983230072969 + 3 ^ 40 * 7099452 * 2
def baseEnd_7099452 : Nat := 3645431259523662595100221

theorem tailTrace_7099452 : CollatzResearch.WordTrace tailWord_7099452 prefixEnd_7099452 3645431259523662595100221 := by
  unfold tailWord_7099452
  simp only [CollatzResearch.WordTrace]
  refine ⟨129469143537952684357730305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172625524717270245810307073 129469143537952684357730305)
  ·
    refine ⟨97101857653464513268297729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129469143537952684357730305 97101857653464513268297729)
    ·
      refine ⟨72826393240098384951223297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97101857653464513268297729 72826393240098384951223297)
      ·
        refine ⟨54619794930073788713417473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72826393240098384951223297 54619794930073788713417473)
        ·
          refine ⟨40964846197555341535063105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54619794930073788713417473 40964846197555341535063105)
          ·
            refine ⟨30723634648166506151297329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40964846197555341535063105 30723634648166506151297329)
            ·
              refine ⟨23042725986124879613472997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30723634648166506151297329 23042725986124879613472997)
              ·
                refine ⟨4320511122398414927526187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23042725986124879613472997 4320511122398414927526187)
                ·
                  refine ⟨6480766683597622391289281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320511122398414927526187 6480766683597622391289281)
                  ·
                    refine ⟨4860575012698216793466961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480766683597622391289281 4860575012698216793466961)
                    ·
                      refine ⟨3645431259523662595100221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860575012698216793466961 3645431259523662595100221)
                      ·
                        rfl

theorem cell23_7099452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_7099452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099452 prefixEnd_7099452 := by exact prefixLift 7099452
  have htrace : WordTrace (prefixWord ++ tailWord_7099452) baseStart_7099452 baseEnd_7099452 := by
    simpa [prefixWord, tailWord_7099452, baseEnd_7099452] using wordTrace_append hprefix tailTrace_7099452
  have hstable : (prefixWord ++ tailWord_7099452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099452).length < 2 ^ (prefixWord ++ tailWord_7099452).sum := by decide
  have hdescent : baseEnd_7099452 < baseStart_7099452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099495 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_7099495 : Nat := 118140960795 + 7099495 * 2 ^ 59
def prefixEnd_7099495 : Nat := 4983230072969 + 3 ^ 40 * 7099495 * 2
def baseEnd_7099495 : Nat := 3645453339191805926862523

theorem tailTrace_7099495 : CollatzResearch.WordTrace tailWord_7099495 prefixEnd_7099495 3645453339191805926862523 := by
  unfold tailWord_7099495
  simp only [CollatzResearch.WordTrace]
  refine ⟨258939855414749587059275939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172626570276499724706183959 258939855414749587059275939)
  ·
    refine ⟨388409783122124380588913909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258939855414749587059275939 388409783122124380588913909)
    ·
      refine ⟨36413417167699160680210679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388409783122124380588913909 36413417167699160680210679)
      ·
        refine ⟨54620125751548741020316019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36413417167699160680210679 54620125751548741020316019)
        ·
          refine ⟨81930188627323111530474029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54620125751548741020316019 81930188627323111530474029)
          ·
            refine ⟨30723820735246166823927761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81930188627323111530474029 30723820735246166823927761)
            ·
              refine ⟨23042865551434625117945821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30723820735246166823927761 23042865551434625117945821)
              ·
                refine ⟨8641074581787984419229683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23042865551434625117945821 8641074581787984419229683)
                ·
                  refine ⟨12961611872681976628844525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641074581787984419229683 12961611872681976628844525)
                  ·
                    refine ⟨4860604452255741235816697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12961611872681976628844525 4860604452255741235816697)
                    ·
                      refine ⟨3645453339191805926862523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860604452255741235816697 3645453339191805926862523)
                      ·
                        rfl

theorem cell23_7099495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_7099495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099495 prefixEnd_7099495 := by exact prefixLift 7099495
  have htrace : WordTrace (prefixWord ++ tailWord_7099495) baseStart_7099495 baseEnd_7099495 := by
    simpa [prefixWord, tailWord_7099495, baseEnd_7099495] using wordTrace_append hprefix tailTrace_7099495
  have hstable : (prefixWord ++ tailWord_7099495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099495).length < 2 ^ (prefixWord ++ tailWord_7099495).sum := by decide
  have hdescent : baseEnd_7099495 < baseStart_7099495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099511 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_7099511 : Nat := 118140960795 + 7099511 * 2 ^ 59
def prefixEnd_7099511 : Nat := 4983230072969 + 3 ^ 40 * 7099511 * 2
def baseEnd_7099511 : Nat := 3645461554882277864262449

theorem tailTrace_7099511 : CollatzResearch.WordTrace tailWord_7099511 prefixEnd_7099511 3645461554882277864262449 := by
  unfold tailWord_7099511
  simp only [CollatzResearch.WordTrace]
  refine ⟨258940438982691621791858387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172626959321794414527905591 258940438982691621791858387)
  ·
    refine ⟨388410658474037432687787581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258940438982691621791858387 388410658474037432687787581)
    ·
      refine ⟨145653996927764037257920343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388410658474037432687787581 145653996927764037257920343)
      ·
        refine ⟨218480995391646055886880515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145653996927764037257920343 218480995391646055886880515)
        ·
          refine ⟨327721493087469083830320773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218480995391646055886880515 327721493087469083830320773)
          ·
            refine ⟨61447779953900453218185145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327721493087469083830320773 61447779953900453218185145)
            ·
              refine ⟨46085834965425339913638859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61447779953900453218185145 46085834965425339913638859)
              ·
                refine ⟨69128752448138009870458289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46085834965425339913638859 69128752448138009870458289)
                ·
                  refine ⟨51846564336103507402843717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69128752448138009870458289 51846564336103507402843717)
                  ·
                    refine ⟨9721230813019407638033197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51846564336103507402843717 9721230813019407638033197)
                    ·
                      refine ⟨3645461554882277864262449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721230813019407638033197 3645461554882277864262449)
                      ·
                        rfl

theorem cell23_7099511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_7099511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099511 prefixEnd_7099511 := by exact prefixLift 7099511
  have htrace : WordTrace (prefixWord ++ tailWord_7099511) baseStart_7099511 baseEnd_7099511 := by
    simpa [prefixWord, tailWord_7099511, baseEnd_7099511] using wordTrace_append hprefix tailTrace_7099511
  have hstable : (prefixWord ++ tailWord_7099511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099511).length < 2 ^ (prefixWord ++ tailWord_7099511).sum := by decide
  have hdescent : baseEnd_7099511 < baseStart_7099511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099541 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_7099541 : Nat := 118140960795 + 7099541 * 2 ^ 59
def prefixEnd_7099541 : Nat := 4983230072969 + 3 ^ 40 * 7099541 * 2
def baseEnd_7099541 : Nat := 3645476959301912746887311

theorem tailTrace_7099541 : CollatzResearch.WordTrace tailWord_7099541 prefixEnd_7099541 3645476959301912746887311 := by
  unfold tailWord_7099541
  simp only [CollatzResearch.WordTrace]
  refine ⟨258941533172582936915450477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172627688781721957943633651 258941533172582936915450477)
  ·
    refine ⟨97103074939718601343293929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258941533172582936915450477 97103074939718601343293929)
    ·
      refine ⟨72827306204788951007470447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97103074939718601343293929 72827306204788951007470447)
      ·
        refine ⟨109240959307183426511205671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72827306204788951007470447 109240959307183426511205671)
        ·
          refine ⟨163861438960775139766808507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109240959307183426511205671 163861438960775139766808507)
          ·
            refine ⟨245792158441162709650212761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163861438960775139766808507 245792158441162709650212761)
            ·
              refine ⟨184344118830872032237659571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245792158441162709650212761 184344118830872032237659571)
              ·
                refine ⟨276516178246308048356489357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184344118830872032237659571 276516178246308048356489357)
                ·
                  refine ⟨103693566842365518133683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276516178246308048356489357 103693566842365518133683509)
                  ·
                    refine ⟨9721271891471767325032829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103693566842365518133683509 9721271891471767325032829)
                    ·
                      refine ⟨3645476959301912746887311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721271891471767325032829 3645476959301912746887311)
                      ·
                        rfl

theorem cell23_7099541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_7099541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099541 prefixEnd_7099541 := by exact prefixLift 7099541
  have htrace : WordTrace (prefixWord ++ tailWord_7099541) baseStart_7099541 baseEnd_7099541 := by
    simpa [prefixWord, tailWord_7099541, baseEnd_7099541] using wordTrace_append hprefix tailTrace_7099541
  have hstable : (prefixWord ++ tailWord_7099541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099541).length < 2 ^ (prefixWord ++ tailWord_7099541).sum := by decide
  have hdescent : baseEnd_7099541 < baseStart_7099541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099559 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7099559 : Nat := 118140960795 + 7099559 * 2 ^ 59
def prefixEnd_7099559 : Nat := 4983230072969 + 3 ^ 40 * 7099559 * 2
def baseEnd_7099559 : Nat := 3645486201953693676462229

theorem tailTrace_7099559 : CollatzResearch.WordTrace tailWord_7099559 prefixEnd_7099559 3645486201953693676462229 := by
  unfold tailWord_7099559
  simp only [CollatzResearch.WordTrace]
  refine ⟨258942189686517725989605731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172628126457678483993070487 258942189686517725989605731)
  ·
    refine ⟨388413284529776588984408597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258942189686517725989605731 388413284529776588984408597)
    ·
      refine ⟨18206872712333277608644153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 388413284529776588984408597 18206872712333277608644153)
      ·
        refine ⟨13655154534249958206483115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18206872712333277608644153 13655154534249958206483115)
        ·
          refine ⟨20482731801374937309724673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13655154534249958206483115 20482731801374937309724673)
          ·
            refine ⟨15362048851031202982293505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20482731801374937309724673 15362048851031202982293505)
            ·
              refine ⟨11521536638273402236720129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15362048851031202982293505 11521536638273402236720129)
              ·
                refine ⟨8641152478705051677540097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11521536638273402236720129 8641152478705051677540097)
                ·
                  refine ⟨6480864359028788758155073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8641152478705051677540097 6480864359028788758155073)
                  ·
                    refine ⟨4860648269271591568616305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480864359028788758155073 4860648269271591568616305)
                    ·
                      refine ⟨3645486201953693676462229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860648269271591568616305 3645486201953693676462229)
                      ·
                        rfl

theorem cell23_7099559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7099559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099559 prefixEnd_7099559 := by exact prefixLift 7099559
  have htrace : WordTrace (prefixWord ++ tailWord_7099559) baseStart_7099559 baseEnd_7099559 := by
    simpa [prefixWord, tailWord_7099559, baseEnd_7099559] using wordTrace_append hprefix tailTrace_7099559
  have hstable : (prefixWord ++ tailWord_7099559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099559).length < 2 ^ (prefixWord ++ tailWord_7099559).sum := by decide
  have hdescent : baseEnd_7099559 < baseStart_7099559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099571 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_7099571 : Nat := 118140960795 + 7099571 * 2 ^ 59
def prefixEnd_7099571 : Nat := 4983230072969 + 3 ^ 40 * 7099571 * 2
def baseEnd_7099571 : Nat := 3645492363721547629512173

theorem tailTrace_7099571 : CollatzResearch.WordTrace tailWord_7099571 prefixEnd_7099571 3645492363721547629512173 := by
  unfold tailWord_7099571
  simp only [CollatzResearch.WordTrace]
  refine ⟨258942627362474252039042567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172628418241649501359361711 258942627362474252039042567)
  ·
    refine ⟨388413941043711378058563851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258942627362474252039042567 388413941043711378058563851)
    ·
      refine ⟨582620911565567067087845777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388413941043711378058563851 582620911565567067087845777)
      ·
        refine ⟨436965683674175300315884333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582620911565567067087845777 436965683674175300315884333)
        ·
          refine ⟨163862131377815737618456625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436965683674175300315884333 163862131377815737618456625)
          ·
            refine ⟨122896598533361803213842469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163862131377815737618456625 122896598533361803213842469)
            ·
              refine ⟨23043112225005338102595463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122896598533361803213842469 23043112225005338102595463)
              ·
                refine ⟨34564668337508007153893195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23043112225005338102595463 34564668337508007153893195)
                ·
                  refine ⟨51847002506262010730839793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34564668337508007153893195 51847002506262010730839793)
                  ·
                    refine ⟨38885251879696508048129845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51847002506262010730839793 38885251879696508048129845)
                    ·
                      refine ⟨3645492363721547629512173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38885251879696508048129845 3645492363721547629512173)
                      ·
                        rfl

theorem cell23_7099571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_7099571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099571 prefixEnd_7099571 := by exact prefixLift 7099571
  have htrace : WordTrace (prefixWord ++ tailWord_7099571) baseStart_7099571 baseEnd_7099571 := by
    simpa [prefixWord, tailWord_7099571, baseEnd_7099571] using wordTrace_append hprefix tailTrace_7099571
  have hstable : (prefixWord ++ tailWord_7099571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099571).length < 2 ^ (prefixWord ++ tailWord_7099571).sum := by decide
  have hdescent : baseEnd_7099571 < baseStart_7099571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099641 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7099641 : Nat := 118140960795 + 7099641 * 2 ^ 59
def prefixEnd_7099641 : Nat := 4983230072969 + 3 ^ 40 * 7099641 * 2
def baseEnd_7099641 : Nat := 3645528307367362355636851

theorem tailTrace_7099641 : CollatzResearch.WordTrace tailWord_7099641 prefixEnd_7099641 3645528307367362355636851 := by
  unfold tailWord_7099641
  simp only [CollatzResearch.WordTrace]
  refine ⟨258945180472220653994090777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172630120314813769329393851 258945180472220653994090777)
  ·
    refine ⟨194208885354165490495568083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258945180472220653994090777 194208885354165490495568083)
    ·
      refine ⟨291313328031248235743352125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194208885354165490495568083 291313328031248235743352125)
      ·
        refine ⟨109242498011718088403757047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291313328031248235743352125 109242498011718088403757047)
        ·
          refine ⟨163863747017577132605635571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109242498011718088403757047 163863747017577132605635571)
          ·
            refine ⟨245795620526365698908453357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163863747017577132605635571 245795620526365698908453357)
            ·
              refine ⟨92173357697387137090670009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245795620526365698908453357 92173357697387137090670009)
              ·
                refine ⟨69130018273040352818002507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92173357697387137090670009 69130018273040352818002507)
                ·
                  refine ⟨103695027409560529227003761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69130018273040352818002507 103695027409560529227003761)
                  ·
                    refine ⟨77771270557170396920252821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103695027409560529227003761 77771270557170396920252821)
                    ·
                      refine ⟨3645528307367362355636851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77771270557170396920252821 3645528307367362355636851)
                      ·
                        rfl

theorem cell23_7099641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7099641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099641 prefixEnd_7099641 := by exact prefixLift 7099641
  have htrace : WordTrace (prefixWord ++ tailWord_7099641) baseStart_7099641 baseEnd_7099641 := by
    simpa [prefixWord, tailWord_7099641, baseEnd_7099641] using wordTrace_append hprefix tailTrace_7099641
  have hstable : (prefixWord ++ tailWord_7099641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099641).length < 2 ^ (prefixWord ++ tailWord_7099641).sum := by decide
  have hdescent : baseEnd_7099641 < baseStart_7099641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099732 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_7099732 : Nat := 118140960795 + 7099732 * 2 ^ 59
def prefixEnd_7099732 : Nat := 4983230072969 + 3 ^ 40 * 7099732 * 2
def baseEnd_7099732 : Nat := 1215191678035640499866311

theorem tailTrace_7099732 : CollatzResearch.WordTrace tailWord_7099732 prefixEnd_7099732 1215191678035640499866311 := by
  unfold tailWord_7099732
  simp only [CollatzResearch.WordTrace]
  refine ⟨129474249757445488267826725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172632333009927317690435633 129474249757445488267826725)
  ·
    refine ⟨24276421829521029050217511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129474249757445488267826725 24276421829521029050217511)
    ·
      refine ⟨36414632744281543575326267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24276421829521029050217511 36414632744281543575326267)
      ·
        refine ⟨54621949116422315362989401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36414632744281543575326267 54621949116422315362989401)
        ·
          refine ⟨40966461837316736522242051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54621949116422315362989401 40966461837316736522242051)
          ·
            refine ⟨61449692755975104783363077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40966461837316736522242051 61449692755975104783363077)
            ·
              refine ⟨11521817391745332146880577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61449692755975104783363077 11521817391745332146880577)
              ·
                refine ⟨8641363043808999110160433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11521817391745332146880577 8641363043808999110160433)
                ·
                  refine ⟨6481022282856749332620325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8641363043808999110160433 6481022282856749332620325)
                  ·
                    refine ⟨1215191678035640499866311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481022282856749332620325 1215191678035640499866311)
                    ·
                      rfl

theorem cell23_7099732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_7099732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099732 prefixEnd_7099732 := by exact prefixLift 7099732
  have htrace : WordTrace (prefixWord ++ tailWord_7099732) baseStart_7099732 baseEnd_7099732 := by
    simpa [prefixWord, tailWord_7099732, baseEnd_7099732] using wordTrace_append hprefix tailTrace_7099732
  have hstable : (prefixWord ++ tailWord_7099732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099732).length < 2 ^ (prefixWord ++ tailWord_7099732).sum := by decide
  have hdescent : baseEnd_7099732 < baseStart_7099732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099752 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7099752 : Nat := 118140960795 + 7099752 * 2 ^ 59
def prefixEnd_7099752 : Nat := 4983230072969 + 3 ^ 40 * 7099752 * 2
def baseEnd_7099752 : Nat := 3645585303720011421348841

theorem tailTrace_7099752 : CollatzResearch.WordTrace tailWord_7099752 prefixEnd_7099752 3645585303720011421348841 := by
  unfold tailWord_7099752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129474614487409259975690755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172632819316545679967587673 129474614487409259975690755)
  ·
    refine ⟨194211921731113889963536133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129474614487409259975690755 194211921731113889963536133)
    ·
      refine ⟨36414735324583854368163025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194211921731113889963536133 36414735324583854368163025)
      ·
        refine ⟨27311051493437890776122269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36414735324583854368163025 27311051493437890776122269)
        ·
          refine ⟨10241644310039209041045851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27311051493437890776122269 10241644310039209041045851)
          ·
            refine ⟨15362466465058813561568777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241644310039209041045851 15362466465058813561568777)
            ·
              refine ⟨11521849848794110171176583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15362466465058813561568777 11521849848794110171176583)
              ·
                refine ⟨17282774773191165256764875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521849848794110171176583 17282774773191165256764875)
                ·
                  refine ⟨25924162159786747885147313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17282774773191165256764875 25924162159786747885147313)
                  ·
                    refine ⟨19443121619840060913860485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25924162159786747885147313 19443121619840060913860485)
                    ·
                      refine ⟨3645585303720011421348841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19443121619840060913860485 3645585303720011421348841)
                      ·
                        rfl

theorem cell23_7099752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7099752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099752 prefixEnd_7099752 := by exact prefixLift 7099752
  have htrace : WordTrace (prefixWord ++ tailWord_7099752) baseStart_7099752 baseEnd_7099752 := by
    simpa [prefixWord, tailWord_7099752, baseEnd_7099752] using wordTrace_append hprefix tailTrace_7099752
  have hstable : (prefixWord ++ tailWord_7099752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099752).length < 2 ^ (prefixWord ++ tailWord_7099752).sum := by decide
  have hdescent : baseEnd_7099752 < baseStart_7099752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099788 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_7099788 : Nat := 118140960795 + 7099788 * 2 ^ 59
def prefixEnd_7099788 : Nat := 4983230072969 + 3 ^ 40 * 7099788 * 2
def baseEnd_7099788 : Nat := 1215201263007857760166225

theorem tailTrace_7099788 : CollatzResearch.WordTrace tailWord_7099788 prefixEnd_7099788 1215201263007857760166225 := by
  unfold tailWord_7099788
  simp only [CollatzResearch.WordTrace]
  refine ⟨129475271001344049049846009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172633694668458732066461345 129475271001344049049846009)
  ·
    refine ⟨97106453251008036787384507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129475271001344049049846009 97106453251008036787384507)
    ·
      refine ⟨145659679876512055181076761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97106453251008036787384507 145659679876512055181076761)
      ·
        refine ⟨109244759907384041385807571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145659679876512055181076761 109244759907384041385807571)
        ·
          refine ⟨163867139861076062078711357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109244759907384041385807571 163867139861076062078711357)
          ·
            refine ⟨61450177447903523279516759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163867139861076062078711357 61450177447903523279516759)
            ·
              refine ⟨92175266171855284919275139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61450177447903523279516759 92175266171855284919275139)
              ·
                refine ⟨138262899257782927378912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92175266171855284919275139 138262899257782927378912709)
                ·
                  refine ⟨25924293610834298883546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138262899257782927378912709 25924293610834298883546133)
                  ·
                    refine ⟨1215201263007857760166225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25924293610834298883546133 1215201263007857760166225)
                    ·
                      rfl

theorem cell23_7099788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_7099788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099788 prefixEnd_7099788 := by exact prefixLift 7099788
  have htrace : WordTrace (prefixWord ++ tailWord_7099788) baseStart_7099788 baseEnd_7099788 := by
    simpa [prefixWord, tailWord_7099788, baseEnd_7099788] using wordTrace_append hprefix tailTrace_7099788
  have hstable : (prefixWord ++ tailWord_7099788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099788).length < 2 ^ (prefixWord ++ tailWord_7099788).sum := by decide
  have hdescent : baseEnd_7099788 < baseStart_7099788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099805 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7099805 : Nat := 118140960795 + 7099805 * 2 ^ 59
def prefixEnd_7099805 : Nat := 4983230072969 + 3 ^ 40 * 7099805 * 2
def baseEnd_7099805 : Nat := 1215204172731566571328699

theorem tailTrace_7099805 : CollatzResearch.WordTrace tailWord_7099805 prefixEnd_7099805 1215204172731566571328699 := by
  unfold tailWord_7099805
  simp only [CollatzResearch.WordTrace]
  refine ⟨258951162043626510003060869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172634108029084340002040579 258951162043626510003060869)
  ·
    refine ⟨48553342883179970625573913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258951162043626510003060869 48553342883179970625573913)
    ·
      refine ⟨36415007162384977969180435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48553342883179970625573913 36415007162384977969180435)
      ·
        refine ⟨54622510743577466953770653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36415007162384977969180435 54622510743577466953770653)
        ·
          refine ⟨20483441528841550107663995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54622510743577466953770653 20483441528841550107663995)
          ·
            refine ⟨30725162293262325161495993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20483441528841550107663995 30725162293262325161495993)
            ·
              refine ⟨23043871719946743871121995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30725162293262325161495993 23043871719946743871121995)
              ·
                refine ⟨34565807579920115806682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23043871719946743871121995 34565807579920115806682993)
                ·
                  refine ⟨25924355684940086855012245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34565807579920115806682993 25924355684940086855012245)
                  ·
                    refine ⟨1215204172731566571328699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25924355684940086855012245 1215204172731566571328699)
                    ·
                      rfl

theorem cell23_7099805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7099805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099805 prefixEnd_7099805 := by exact prefixLift 7099805
  have htrace : WordTrace (prefixWord ++ tailWord_7099805) baseStart_7099805 baseEnd_7099805 := by
    simpa [prefixWord, tailWord_7099805, baseEnd_7099805] using wordTrace_append hprefix tailTrace_7099805
  have hstable : (prefixWord ++ tailWord_7099805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099805).length < 2 ^ (prefixWord ++ tailWord_7099805).sum := by decide
  have hdescent : baseEnd_7099805 < baseStart_7099805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099806 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7099806 : Nat := 118140960795 + 7099806 * 2 ^ 59
def prefixEnd_7099806 : Nat := 4983230072969 + 3 ^ 40 * 7099806 * 2
def baseEnd_7099806 : Nat := 3645613031675354210073593

theorem tailTrace_7099806 : CollatzResearch.WordTrace tailWord_7099806 prefixEnd_7099806 3645613031675354210073593 := by
  unfold tailWord_7099806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32368899814577860896730909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172634132344415258115898181 32368899814577860896730909)
  ·
    refine ⟨12138337430466697836274091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32368899814577860896730909 12138337430466697836274091)
    ·
      refine ⟨18207506145700046754411137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12138337430466697836274091 18207506145700046754411137)
      ·
        refine ⟨13655629609275035065808353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18207506145700046754411137 13655629609275035065808353)
        ·
          refine ⟨10241722206956276299356265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655629609275035065808353 10241722206956276299356265)
          ·
            refine ⟨7681291655217207224517199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10241722206956276299356265 7681291655217207224517199)
            ·
              refine ⟨11521937482825810836775799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681291655217207224517199 11521937482825810836775799)
              ·
                refine ⟨17282906224238716255163699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521937482825810836775799 17282906224238716255163699)
                ·
                  refine ⟨25924359336358074382745549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17282906224238716255163699 25924359336358074382745549)
                  ·
                    refine ⟨9721634751134277893529581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25924359336358074382745549 9721634751134277893529581)
                    ·
                      refine ⟨3645613031675354210073593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721634751134277893529581 3645613031675354210073593)
                      ·
                        rfl

theorem cell23_7099806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7099806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099806 prefixEnd_7099806 := by exact prefixLift 7099806
  have htrace : WordTrace (prefixWord ++ tailWord_7099806) baseStart_7099806 baseEnd_7099806 := by
    simpa [prefixWord, tailWord_7099806, baseEnd_7099806] using wordTrace_append hprefix tailTrace_7099806
  have hstable : (prefixWord ++ tailWord_7099806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099806).length < 2 ^ (prefixWord ++ tailWord_7099806).sum := by decide
  have hdescent : baseEnd_7099806 < baseStart_7099806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099815 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7099815 : Nat := 118140960795 + 7099815 * 2 ^ 59
def prefixEnd_7099815 : Nat := 4983230072969 + 3 ^ 40 * 7099815 * 2
def baseEnd_7099815 : Nat := 3645617653001244674861051

theorem tailTrace_7099815 : CollatzResearch.WordTrace tailWord_7099815 prefixEnd_7099815 3645617653001244674861051 := by
  unfold tailWord_7099815
  simp only [CollatzResearch.WordTrace]
  refine ⟨258951526773590281710924899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172634351182393521140616599 258951526773590281710924899)
  ·
    refine ⟨388427290160385422566387349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258951526773590281710924899 388427290160385422566387349)
    ·
      refine ⟨18207529226268066682799407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 388427290160385422566387349 18207529226268066682799407)
      ·
        refine ⟨27311293839402100024199111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18207529226268066682799407 27311293839402100024199111)
        ·
          refine ⟨40966940759103150036298667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27311293839402100024199111 40966940759103150036298667)
          ·
            refine ⟨61450411138654725054448001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40966940759103150036298667 61450411138654725054448001)
            ·
              refine ⟨46087808353991043790836001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61450411138654725054448001 46087808353991043790836001)
              ·
                refine ⟨34565856265493282843127001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46087808353991043790836001 34565856265493282843127001)
                ·
                  refine ⟨25924392199119962132345251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34565856265493282843127001 25924392199119962132345251)
                  ·
                    refine ⟨38886588298679943198517877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25924392199119962132345251 38886588298679943198517877)
                    ·
                      refine ⟨3645617653001244674861051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38886588298679943198517877 3645617653001244674861051)
                      ·
                        rfl

theorem cell23_7099815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7099815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099815 prefixEnd_7099815 := by exact prefixLift 7099815
  have htrace : WordTrace (prefixWord ++ tailWord_7099815) baseStart_7099815 baseEnd_7099815 := by
    simpa [prefixWord, tailWord_7099815, baseEnd_7099815] using wordTrace_append hprefix tailTrace_7099815
  have hstable : (prefixWord ++ tailWord_7099815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099815).length < 2 ^ (prefixWord ++ tailWord_7099815).sum := by decide
  have hdescent : baseEnd_7099815 < baseStart_7099815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099829 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_7099829 : Nat := 118140960795 + 7099829 * 2 ^ 59
def prefixEnd_7099829 : Nat := 4983230072969 + 3 ^ 40 * 7099829 * 2
def baseEnd_7099829 : Nat := 3645624841730407620085987

theorem tailTrace_7099829 : CollatzResearch.WordTrace tailWord_7099829 prefixEnd_7099829 3645624841730407620085987 := by
  unfold tailWord_7099829
  simp only [CollatzResearch.WordTrace]
  refine ⟨258952037395539562101934541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172634691597026374734623027 258952037395539562101934541)
  ·
    refine ⟨97107014023327335788225453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258952037395539562101934541 97107014023327335788225453)
    ·
      refine ⟨36415130258747750920584545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97107014023327335788225453 36415130258747750920584545)
      ·
        refine ⟨27311347694060813190438409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36415130258747750920584545 27311347694060813190438409)
        ·
          refine ⟨20483510770545609892828807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27311347694060813190438409 20483510770545609892828807)
          ·
            refine ⟨30725266155818414839243211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20483510770545609892828807 30725266155818414839243211)
            ·
              refine ⟨46087899233727622258864817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30725266155818414839243211 46087899233727622258864817)
              ·
                refine ⟨34565924425295716694148613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46087899233727622258864817 34565924425295716694148613)
                ·
                  refine ⟨6481110829742946880152865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34565924425295716694148613 6481110829742946880152865)
                  ·
                    refine ⟨4860833122307210160114649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481110829742946880152865 4860833122307210160114649)
                    ·
                      refine ⟨3645624841730407620085987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860833122307210160114649 3645624841730407620085987)
                      ·
                        rfl

theorem cell23_7099829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_7099829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099829 prefixEnd_7099829 := by exact prefixLift 7099829
  have htrace : WordTrace (prefixWord ++ tailWord_7099829) baseStart_7099829 baseEnd_7099829 := by
    simpa [prefixWord, tailWord_7099829, baseEnd_7099829] using wordTrace_append hprefix tailTrace_7099829
  have hstable : (prefixWord ++ tailWord_7099829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099829).length < 2 ^ (prefixWord ++ tailWord_7099829).sum := by decide
  have hdescent : baseEnd_7099829 < baseStart_7099829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099852 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 7]
def baseStart_7099852 : Nat := 118140960795 + 7099852 * 2 ^ 59
def prefixEnd_7099852 : Nat := 4983230072969 + 3 ^ 40 * 7099852 * 2
def baseEnd_7099852 : Nat := 405070739087273447788709

theorem tailTrace_7099852 : CollatzResearch.WordTrace tailWord_7099852 prefixEnd_7099852 405070739087273447788709 := by
  unfold tailWord_7099852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129476438137228118515010905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172635250849637491353347873 129476438137228118515010905)
  ·
    refine ⟨97107328602921088886258179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129476438137228118515010905 97107328602921088886258179)
    ·
      refine ⟨145660992904381633329387269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97107328602921088886258179 145660992904381633329387269)
      ·
        refine ⟨27311436169571556249260113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145660992904381633329387269 27311436169571556249260113)
        ·
          refine ⟨20483577127178667186945085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27311436169571556249260113 20483577127178667186945085)
          ·
            refine ⟨7681341422692000195104407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20483577127178667186945085 7681341422692000195104407)
            ·
              refine ⟨11522012134038000292656611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681341422692000195104407 11522012134038000292656611)
              ·
                refine ⟨17283018201057000438984917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11522012134038000292656611 17283018201057000438984917)
                ·
                  refine ⟨405070739087273447788709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17283018201057000438984917 405070739087273447788709)
                  ·
                    rfl

theorem cell23_7099852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_7099852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099852 prefixEnd_7099852 := by exact prefixLift 7099852
  have htrace : WordTrace (prefixWord ++ tailWord_7099852) baseStart_7099852 baseEnd_7099852 := by
    simpa [prefixWord, tailWord_7099852, baseEnd_7099852] using wordTrace_append hprefix tailTrace_7099852
  have hstable : (prefixWord ++ tailWord_7099852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099852).length < 2 ^ (prefixWord ++ tailWord_7099852).sum := by decide
  have hdescent : baseEnd_7099852 < baseStart_7099852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099895 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 7, 4]
def baseStart_7099895 : Nat := 118140960795 + 7099895 * 2 ^ 59
def prefixEnd_7099895 : Nat := 4983230072969 + 3 ^ 40 * 7099895 * 2
def baseEnd_7099895 : Nat := 1215219577151201453953561

theorem tailTrace_7099895 : CollatzResearch.WordTrace tailWord_7099895 prefixEnd_7099895 1215219577151201453953561 := by
  unfold tailWord_7099895
  simp only [CollatzResearch.WordTrace]
  refine ⟨258954444613300455373837139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172636296408866970249224759 258954444613300455373837139)
  ·
    refine ⟨388431666919950683060755709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258954444613300455373837139 388431666919950683060755709)
    ·
      refine ⟨145661875094981506147783391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388431666919950683060755709 145661875094981506147783391)
      ·
        refine ⟨218492812642472259221675087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145661875094981506147783391 218492812642472259221675087)
        ·
          refine ⟨327739218963708388832512631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218492812642472259221675087 327739218963708388832512631)
          ·
            refine ⟨491608828445562583248768947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327739218963708388832512631 491608828445562583248768947)
            ·
              refine ⟨737413242668343874873153421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491608828445562583248768947 737413242668343874873153421)
              ·
                refine ⟨276529966000628953077432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 737413242668343874873153421 276529966000628953077432533)
                ·
                  refine ⟨6481171078139741087752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276529966000628953077432533 6481171078139741087752325)
                  ·
                    refine ⟨1215219577151201453953561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481171078139741087752325 1215219577151201453953561)
                    ·
                      rfl

theorem cell23_7099895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_7099895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099895 prefixEnd_7099895 := by exact prefixLift 7099895
  have htrace : WordTrace (prefixWord ++ tailWord_7099895) baseStart_7099895 baseEnd_7099895 := by
    simpa [prefixWord, tailWord_7099895, baseEnd_7099895] using wordTrace_append hprefix tailTrace_7099895
  have hstable : (prefixWord ++ tailWord_7099895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099895).length < 2 ^ (prefixWord ++ tailWord_7099895).sum := by decide
  have hdescent : baseEnd_7099895 < baseStart_7099895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099946 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7099946 : Nat := 118140960795 + 7099946 * 2 ^ 59
def prefixEnd_7099946 : Nat := 4983230072969 + 3 ^ 40 * 7099946 * 2
def baseEnd_7099946 : Nat := 1215228306322327887440983

theorem tailTrace_7099946 : CollatzResearch.WordTrace tailWord_7099946 prefixEnd_7099946 1215228306322327887440983 := by
  unfold tailWord_7099946
  simp only [CollatzResearch.WordTrace]
  refine ⟨64739076184028922770985923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172637536490743794055962461 64739076184028922770985923)
  ·
    refine ⟨97108614276043384156478885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64739076184028922770985923 97108614276043384156478885)
    ·
      refine ⟨18207865176758134529339791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97108614276043384156478885 18207865176758134529339791)
      ·
        refine ⟨27311797765137201794009687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18207865176758134529339791 27311797765137201794009687)
        ·
          refine ⟨40967696647705802691014531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27311797765137201794009687 40967696647705802691014531)
          ·
            refine ⟨61451544971558704036521797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40967696647705802691014531 61451544971558704036521797)
            ·
              refine ⟨11522164682167257006847837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61451544971558704036521797 11522164682167257006847837)
              ·
                refine ⟨4320811755812721377567939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11522164682167257006847837 4320811755812721377567939)
                ·
                  refine ⟨6481217633719082066351909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320811755812721377567939 6481217633719082066351909)
                  ·
                    refine ⟨1215228306322327887440983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481217633719082066351909 1215228306322327887440983)
                    ·
                      rfl

theorem cell23_7099946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7099946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099946 prefixEnd_7099946 := by exact prefixLift 7099946
  have htrace : WordTrace (prefixWord ++ tailWord_7099946) baseStart_7099946 baseEnd_7099946 := by
    simpa [prefixWord, tailWord_7099946, baseEnd_7099946] using wordTrace_append hprefix tailTrace_7099946
  have hstable : (prefixWord ++ tailWord_7099946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099946).length < 2 ^ (prefixWord ++ tailWord_7099946).sum := by decide
  have hdescent : baseEnd_7099946 < baseStart_7099946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099952 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_7099952 : Nat := 118140960795 + 7099952 * 2 ^ 59
def prefixEnd_7099952 : Nat := 4983230072969 + 3 ^ 40 * 7099952 * 2
def baseEnd_7099952 : Nat := 3645687999850910638847921

theorem tailTrace_7099952 : CollatzResearch.WordTrace tailWord_7099952 prefixEnd_7099952 3645687999850910638847921 := by
  unfold tailWord_7099952
  simp only [CollatzResearch.WordTrace]
  refine ⟨129478261787046977054331055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172637682382729302739108073 129478261787046977054331055)
  ·
    refine ⟨194217392680570465581496583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129478261787046977054331055 194217392680570465581496583)
    ·
      refine ⟨291326089020855698372244875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194217392680570465581496583 291326089020855698372244875)
      ·
        refine ⟨436989133531283547558367313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291326089020855698372244875 436989133531283547558367313)
        ·
          refine ⟨327741850148462660668775485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436989133531283547558367313 327741850148462660668775485)
          ·
            refine ⟨122903193805673497750790807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327741850148462660668775485 122903193805673497750790807)
            ·
              refine ⟨184354790708510246626186211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122903193805673497750790807 184354790708510246626186211)
              ·
                refine ⟨276532186062765369939279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184354790708510246626186211 276532186062765369939279317)
                ·
                  refine ⟨6481223110846063357951859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276532186062765369939279317 6481223110846063357951859)
                  ·
                    refine ⟨9721834666269095036927789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6481223110846063357951859 9721834666269095036927789)
                    ·
                      refine ⟨3645687999850910638847921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721834666269095036927789 3645687999850910638847921)
                      ·
                        rfl

theorem cell23_7099952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_7099952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099952 prefixEnd_7099952 := by exact prefixLift 7099952
  have htrace : WordTrace (prefixWord ++ tailWord_7099952) baseStart_7099952 baseEnd_7099952 := by
    simpa [prefixWord, tailWord_7099952, baseEnd_7099952] using wordTrace_append hprefix tailTrace_7099952
  have hstable : (prefixWord ++ tailWord_7099952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099952).length < 2 ^ (prefixWord ++ tailWord_7099952).sum := by decide
  have hdescent : baseEnd_7099952 < baseStart_7099952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099992 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_7099992 : Nat := 118140960795 + 7099992 * 2 ^ 59
def prefixEnd_7099992 : Nat := 4983230072969 + 3 ^ 40 * 7099992 * 2
def baseEnd_7099992 : Nat := 3645708539077090482347737

theorem tailTrace_7099992 : CollatzResearch.WordTrace tailWord_7099992 prefixEnd_7099992 3645708539077090482347737 := by
  unfold tailWord_7099992
  simp only [CollatzResearch.WordTrace]
  refine ⟨129478991246974520470059115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172638654995966027293412153 129478991246974520470059115)
  ·
    refine ⟨194218486870461780705088673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129478991246974520470059115 194218486870461780705088673)
    ·
      refine ⟨145663865152846335528816505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194218486870461780705088673 145663865152846335528816505)
      ·
        refine ⟨109247898864634751646612379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145663865152846335528816505 109247898864634751646612379)
        ·
          refine ⟨163871848296952127469918569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109247898864634751646612379 163871848296952127469918569)
          ·
            refine ⟨122903886222714095602438927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163871848296952127469918569 122903886222714095602438927)
            ·
              refine ⟨184355829334071143403658391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122903886222714095602438927 184355829334071143403658391)
              ·
                refine ⟨276533744001106715105487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184355829334071143403658391 276533744001106715105487587)
                ·
                  refine ⟨414800616001660072658231381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276533744001106715105487587 414800616001660072658231381)
                  ·
                    refine ⟨4860944718769453976463649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 414800616001660072658231381 4860944718769453976463649)
                    ·
                      refine ⟨3645708539077090482347737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860944718769453976463649 3645708539077090482347737)
                      ·
                        rfl

theorem cell23_7099992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_7099992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099992 prefixEnd_7099992 := by exact prefixLift 7099992
  have htrace : WordTrace (prefixWord ++ tailWord_7099992) baseStart_7099992 baseEnd_7099992 := by
    simpa [prefixWord, tailWord_7099992, baseEnd_7099992] using wordTrace_append hprefix tailTrace_7099992
  have hstable : (prefixWord ++ tailWord_7099992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099992).length < 2 ^ (prefixWord ++ tailWord_7099992).sum := by decide
  have hdescent : baseEnd_7099992 < baseStart_7099992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7099997 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7099997 : Nat := 118140960795 + 7099997 * 2 ^ 59
def prefixEnd_7099997 : Nat := 4983230072969 + 3 ^ 40 * 7099997 * 2
def baseEnd_7099997 : Nat := 1215237035493454320928405

theorem tailTrace_7099997 : CollatzResearch.WordTrace tailWord_7099997 prefixEnd_7099997 1215237035493454320928405 := by
  unfold tailWord_7099997
  simp only [CollatzResearch.WordTrace]
  refine ⟨258958164858930926794050245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172638776572620617862700163 258958164858930926794050245)
  ·
    refine ⟨48554655911049548773884421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258958164858930926794050245 48554655911049548773884421)
    ·
      refine ⟨9103997983321790395103329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48554655911049548773884421 9103997983321790395103329)
      ·
        refine ⟨6827998487491342796327497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103997983321790395103329 6827998487491342796327497)
        ·
          refine ⟨5120998865618507097245623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6827998487491342796327497 5120998865618507097245623)
          ·
            refine ⟨7681498298427760645868435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120998865618507097245623 7681498298427760645868435)
            ·
              refine ⟨11522247447641640968802653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681498298427760645868435 11522247447641640968802653)
              ·
                refine ⟨4320842792865615363300995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11522247447641640968802653 4320842792865615363300995)
                ·
                  refine ⟨6481264189298423044951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320842792865615363300995 6481264189298423044951493)
                  ·
                    refine ⟨1215237035493454320928405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481264189298423044951493 1215237035493454320928405)
                    ·
                      rfl

theorem cell23_7099997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7099997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7099997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7099997 prefixEnd_7099997 := by exact prefixLift 7099997
  have htrace : WordTrace (prefixWord ++ tailWord_7099997) baseStart_7099997 baseEnd_7099997 := by
    simpa [prefixWord, tailWord_7099997, baseEnd_7099997] using wordTrace_append hprefix tailTrace_7099997
  have hstable : (prefixWord ++ tailWord_7099997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7099997).length < 2 ^ (prefixWord ++ tailWord_7099997).sum := by decide
  have hdescent : baseEnd_7099997 < baseStart_7099997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7099997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100003 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 1, 1, 3]
def baseStart_7100003 : Nat := 118140960795 + 7100003 * 2 ^ 59
def prefixEnd_7100003 : Nat := 4983230072969 + 3 ^ 40 * 7100003 * 2
def baseEnd_7100003 : Nat := 3645714187364289939310187

theorem tailTrace_7100003 : CollatzResearch.WordTrace tailWord_7100003 prefixEnd_7100003 3645714187364289939310187 := by
  unfold tailWord_7100003
  simp only [CollatzResearch.WordTrace]
  refine ⟨258958383696909189818768663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172638922464606126545845775 258958383696909189818768663)
  ·
    refine ⟨388437575545363784728152995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258958383696909189818768663 388437575545363784728152995)
    ·
      refine ⟨582656363318045677092229493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388437575545363784728152995 582656363318045677092229493)
      ·
        refine ⟨54624034061066782227396515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 582656363318045677092229493 54624034061066782227396515)
        ·
          refine ⟨81936051091600173341094773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54624034061066782227396515 81936051091600173341094773)
          ·
            refine ⟨7681504789837516250727635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81936051091600173341094773 7681504789837516250727635)
            ·
              refine ⟨11522257184756274376091453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681504789837516250727635 11522257184756274376091453)
              ·
                refine ⟨4320846444283602891034295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11522257184756274376091453 4320846444283602891034295)
                ·
                  refine ⟨6481269666425404336551443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320846444283602891034295 6481269666425404336551443)
                  ·
                    refine ⟨9721904499638106504827165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6481269666425404336551443 9721904499638106504827165)
                    ·
                      refine ⟨3645714187364289939310187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721904499638106504827165 3645714187364289939310187)
                      ·
                        rfl

theorem cell23_7100003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_7100003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100003 prefixEnd_7100003 := by exact prefixLift 7100003
  have htrace : WordTrace (prefixWord ++ tailWord_7100003) baseStart_7100003 baseEnd_7100003 := by
    simpa [prefixWord, tailWord_7100003, baseEnd_7100003] using wordTrace_append hprefix tailTrace_7100003
  have hstable : (prefixWord ++ tailWord_7100003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100003).length < 2 ^ (prefixWord ++ tailWord_7100003).sum := by decide
  have hdescent : baseEnd_7100003 < baseStart_7100003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100009 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 5, 2, 2]
def baseStart_7100009 : Nat := 118140960795 + 7100009 * 2 ^ 59
def prefixEnd_7100009 : Nat := 4983230072969 + 3 ^ 40 * 7100009 * 2
def baseEnd_7100009 : Nat := 3645717268248216915835159

theorem tailTrace_7100009 : CollatzResearch.WordTrace tailWord_7100009 prefixEnd_7100009 3645717268248216915835159 := by
  unfold tailWord_7100009
  simp only [CollatzResearch.WordTrace]
  refine ⟨258958602534887452843487081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172639068356591635228991387 258958602534887452843487081)
  ·
    refine ⟨194218951901165589632615311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258958602534887452843487081 194218951901165589632615311)
    ·
      refine ⟨291328427851748384448922967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194218951901165589632615311 291328427851748384448922967)
      ·
        refine ⟨436992641777622576673384451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291328427851748384448922967 436992641777622576673384451)
        ·
          refine ⟨655488962666433865010076677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436992641777622576673384451 655488962666433865010076677)
          ·
            refine ⟨122904180499956349689389377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655488962666433865010076677 122904180499956349689389377)
            ·
              refine ⟨92178135374967262267042033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122904180499956349689389377 92178135374967262267042033)
              ·
                refine ⟨69133601531225446700281525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92178135374967262267042033 69133601531225446700281525)
                ·
                  refine ⟨6481275143552385628151393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69133601531225446700281525 6481275143552385628151393)
                  ·
                    refine ⟨4860956357664289221113545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481275143552385628151393 4860956357664289221113545)
                    ·
                      refine ⟨3645717268248216915835159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4860956357664289221113545 3645717268248216915835159)
                      ·
                        rfl

theorem cell23_7100009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2, 2].length) (baseStart_7100009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100009 prefixEnd_7100009 := by exact prefixLift 7100009
  have htrace : WordTrace (prefixWord ++ tailWord_7100009) baseStart_7100009 baseEnd_7100009 := by
    simpa [prefixWord, tailWord_7100009, baseEnd_7100009] using wordTrace_append hprefix tailTrace_7100009
  have hstable : (prefixWord ++ tailWord_7100009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100009).length < 2 ^ (prefixWord ++ tailWord_7100009).sum := by decide
  have hdescent : baseEnd_7100009 < baseStart_7100009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100012 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_7100012 : Nat := 118140960795 + 7100012 * 2 ^ 59
def prefixEnd_7100012 : Nat := 4983230072969 + 3 ^ 40 * 7100012 * 2
def baseEnd_7100012 : Nat := 3645718808690180404097645

theorem tailTrace_7100012 : CollatzResearch.WordTrace tailWord_7100012 prefixEnd_7100012 3645718808690180404097645 := by
  unfold tailWord_7100012
  simp only [CollatzResearch.WordTrace]
  refine ⟨129479355976938292177923145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172639141302584389570564193 129479355976938292177923145)
  ·
    refine ⟨97109516982703719133442359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129479355976938292177923145 97109516982703719133442359)
    ·
      refine ⟨145664275474055578700163539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97109516982703719133442359 145664275474055578700163539)
      ·
        refine ⟨218496413211083368050245309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145664275474055578700163539 218496413211083368050245309)
        ·
          refine ⟨81936154954156263018841991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218496413211083368050245309 81936154954156263018841991)
          ·
            refine ⟨122904232431234394528262987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81936154954156263018841991 122904232431234394528262987)
            ·
              refine ⟨184356348646851591792394481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122904232431234394528262987 184356348646851591792394481)
              ·
                refine ⟨138267261485138693844295861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184356348646851591792394481 138267261485138693844295861)
                ·
                  refine ⟨12962555764231752547902737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138267261485138693844295861 12962555764231752547902737)
                  ·
                    refine ⟨9721916823173814410927053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12962555764231752547902737 9721916823173814410927053)
                    ·
                      refine ⟨3645718808690180404097645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721916823173814410927053 3645718808690180404097645)
                      ·
                        rfl

theorem cell23_7100012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_7100012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100012 prefixEnd_7100012 := by exact prefixLift 7100012
  have htrace : WordTrace (prefixWord ++ tailWord_7100012) baseStart_7100012 baseEnd_7100012 := by
    simpa [prefixWord, tailWord_7100012, baseEnd_7100012] using wordTrace_append hprefix tailTrace_7100012
  have hstable : (prefixWord ++ tailWord_7100012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100012).length < 2 ^ (prefixWord ++ tailWord_7100012).sum := by decide
  have hdescent : baseEnd_7100012 < baseStart_7100012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_7100035 : Nat := 118140960795 + 7100035 * 2 ^ 59
def prefixEnd_7100035 : Nat := 4983230072969 + 3 ^ 40 * 7100035 * 2
def baseEnd_7100035 : Nat := 3645730618745233814110039

theorem tailTrace_7100035 : CollatzResearch.WordTrace tailWord_7100035 prefixEnd_7100035 3645730618745233814110039 := by
  unfold tailWord_7100035
  simp only [CollatzResearch.WordTrace]
  refine ⟨258959550832793259283933559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172639700555195506189289039 258959550832793259283933559)
  ·
    refine ⟨388439326249189888925900339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258959550832793259283933559 388439326249189888925900339)
    ·
      refine ⟨582658989373784833388850509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388439326249189888925900339 582658989373784833388850509)
      ·
        refine ⟨218497121015169312520818941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582658989373784833388850509 218497121015169312520818941)
        ·
          refine ⟨81936420380688492195307103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218497121015169312520818941 81936420380688492195307103)
          ·
            refine ⟨122904630571032738292960655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81936420380688492195307103 122904630571032738292960655)
            ·
              refine ⟨184356945856549107439440983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122904630571032738292960655 184356945856549107439440983)
              ·
                refine ⟨276535418784823661159161475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184356945856549107439440983 276535418784823661159161475)
                ·
                  refine ⟨414803128177235491738742213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276535418784823661159161475 414803128177235491738742213)
                  ·
                    refine ⟨77775586533231654701014165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414803128177235491738742213 77775586533231654701014165)
                    ·
                      refine ⟨3645730618745233814110039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77775586533231654701014165 3645730618745233814110039)
                      ·
                        rfl

theorem cell23_7100035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_7100035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100035 prefixEnd_7100035 := by exact prefixLift 7100035
  have htrace : WordTrace (prefixWord ++ tailWord_7100035) baseStart_7100035 baseEnd_7100035 := by
    simpa [prefixWord, tailWord_7100035, baseEnd_7100035] using wordTrace_append hprefix tailTrace_7100035
  have hstable : (prefixWord ++ tailWord_7100035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100035).length < 2 ^ (prefixWord ++ tailWord_7100035).sum := by decide
  have hdescent : baseEnd_7100035 < baseStart_7100035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100036 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_7100036 : Nat := 118140960795 + 7100036 * 2 ^ 59
def prefixEnd_7100036 : Nat := 4983230072969 + 3 ^ 40 * 7100036 * 2
def baseEnd_7100036 : Nat := 1215243710741962770065845

theorem tailTrace_7100036 : CollatzResearch.WordTrace tailWord_7100036 prefixEnd_7100036 1215243710741962770065845 := by
  unfold tailWord_7100036
  simp only [CollatzResearch.WordTrace]
  refine ⟨129479793652894818227359981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172639724870526424303146641 129479793652894818227359981)
  ·
    refine ⟨48554922619835556835259993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129479793652894818227359981 48554922619835556835259993)
    ·
      refine ⟨36416191964876667626444995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48554922619835556835259993 36416191964876667626444995)
      ·
        refine ⟨54624287947315001439667493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36416191964876667626444995 54624287947315001439667493)
        ·
          refine ⟨10242053990121562769937655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54624287947315001439667493 10242053990121562769937655)
          ·
            refine ⟨15363080985182344154906483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242053990121562769937655 15363080985182344154906483)
            ·
              refine ⟨23044621477773516232359725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15363080985182344154906483 23044621477773516232359725)
              ·
                refine ⟨8641733054165068587134897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23044621477773516232359725 8641733054165068587134897)
                ·
                  refine ⟨6481299790623801440351173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8641733054165068587134897 6481299790623801440351173)
                  ·
                    refine ⟨1215243710741962770065845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481299790623801440351173 1215243710741962770065845)
                    ·
                      rfl

theorem cell23_7100036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_7100036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100036 prefixEnd_7100036 := by exact prefixLift 7100036
  have htrace : WordTrace (prefixWord ++ tailWord_7100036) baseStart_7100036 baseEnd_7100036 := by
    simpa [prefixWord, tailWord_7100036, baseEnd_7100036] using wordTrace_append hprefix tailTrace_7100036
  have hstable : (prefixWord ++ tailWord_7100036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100036).length < 2 ^ (prefixWord ++ tailWord_7100036).sum := by decide
  have hdescent : baseEnd_7100036 < baseStart_7100036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100046 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7100046 : Nat := 118140960795 + 7100046 * 2 ^ 59
def prefixEnd_7100046 : Nat := 4983230072969 + 3 ^ 40 * 7100046 * 2
def baseEnd_7100046 : Nat := 3645736267032433271072489

theorem tailTrace_7100046 : CollatzResearch.WordTrace tailWord_7100046 prefixEnd_7100046 3645736267032433271072489 := by
  unfold tailWord_7100046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369994004469176020322999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172639968023835605441722661 32369994004469176020322999)
  ·
    refine ⟨48554991006703764030484499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32369994004469176020322999 48554991006703764030484499)
    ·
      refine ⟨72832486510055646045726749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48554991006703764030484499 72832486510055646045726749)
      ·
        refine ⟨27312182441270867267147531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72832486510055646045726749 27312182441270867267147531)
        ·
          refine ⟨40968273661906300900721297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27312182441270867267147531 40968273661906300900721297)
          ·
            refine ⟨30726205246429725675540973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40968273661906300900721297 30726205246429725675540973)
            ·
              refine ⟨11522326967411147128327865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30726205246429725675540973 11522326967411147128327865)
              ·
                refine ⟨8641745225558360346245899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11522326967411147128327865 8641745225558360346245899)
                ·
                  refine ⟨12962617838337540519368849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641745225558360346245899 12962617838337540519368849)
                  ·
                    refine ⟨9721963378753155389526637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12962617838337540519368849 9721963378753155389526637)
                    ·
                      refine ⟨3645736267032433271072489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9721963378753155389526637 3645736267032433271072489)
                      ·
                        rfl

theorem cell23_7100046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7100046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100046 prefixEnd_7100046 := by exact prefixLift 7100046
  have htrace : WordTrace (prefixWord ++ tailWord_7100046) baseStart_7100046 baseEnd_7100046 := by
    simpa [prefixWord, tailWord_7100046, baseEnd_7100046] using wordTrace_append hprefix tailTrace_7100046
  have hstable : (prefixWord ++ tailWord_7100046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100046).length < 2 ^ (prefixWord ++ tailWord_7100046).sum := by decide
  have hdescent : baseEnd_7100046 < baseStart_7100046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100063 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7100063 : Nat := 118140960795 + 7100063 * 2 ^ 59
def prefixEnd_7100063 : Nat := 4983230072969 + 3 ^ 40 * 7100063 * 2
def baseEnd_7100063 : Nat := 3645744996203559704559911

theorem tailTrace_7100063 : CollatzResearch.WordTrace tailWord_7100063 prefixEnd_7100063 3645744996203559704559911 := by
  unfold tailWord_7100063
  simp only [CollatzResearch.WordTrace]
  refine ⟨258960572076691820065952843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172640381384461213377301895 258960572076691820065952843)
  ·
    refine ⟨388440858115037730098929265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258960572076691820065952843 388440858115037730098929265)
    ·
      refine ⟨291330643586278297574196949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388440858115037730098929265 291330643586278297574196949)
      ·
        refine ⟨6828061959053397599395241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 291330643586278297574196949 6828061959053397599395241)
        ·
          refine ⟨5121046469290048199546431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828061959053397599395241 5121046469290048199546431)
          ·
            refine ⟨7681569703935072299319647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121046469290048199546431 7681569703935072299319647)
            ·
              refine ⟨11522354555902608448979471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681569703935072299319647 11522354555902608448979471)
              ·
                refine ⟨17283531833853912673469207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11522354555902608448979471 17283531833853912673469207)
                ·
                  refine ⟨25925297750780869010203811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17283531833853912673469207 25925297750780869010203811)
                  ·
                    refine ⟨38887946626171303515305717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25925297750780869010203811 38887946626171303515305717)
                    ·
                      refine ⟨3645744996203559704559911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38887946626171303515305717 3645744996203559704559911)
                      ·
                        rfl

theorem cell23_7100063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7100063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100063 prefixEnd_7100063 := by exact prefixLift 7100063
  have htrace : WordTrace (prefixWord ++ tailWord_7100063) baseStart_7100063 baseEnd_7100063 := by
    simpa [prefixWord, tailWord_7100063, baseEnd_7100063] using wordTrace_append hprefix tailTrace_7100063
  have hstable : (prefixWord ++ tailWord_7100063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100063).length < 2 ^ (prefixWord ++ tailWord_7100063).sum := by decide
  have hdescent : baseEnd_7100063 < baseStart_7100063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100082 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7100082 : Nat := 118140960795 + 7100082 * 2 ^ 59
def prefixEnd_7100082 : Nat := 4983230072969 + 3 ^ 40 * 7100082 * 2
def baseEnd_7100082 : Nat := 3645754752335995130222323

theorem tailTrace_7100082 : CollatzResearch.WordTrace tailWord_7100082 prefixEnd_7100082 3645754752335995130222323 := by
  unfold tailWord_7100082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740316265905746577723625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172640843375748657540596333 64740316265905746577723625)
  ·
    refine ⟨48555237199429309933292719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64740316265905746577723625 48555237199429309933292719)
    ·
      refine ⟨72832855799143964899939079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48555237199429309933292719 72832855799143964899939079)
      ·
        refine ⟨109249283698715947349908619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72832855799143964899939079 109249283698715947349908619)
        ·
          refine ⟨163873925548073921024862929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109249283698715947349908619 163873925548073921024862929)
          ·
            refine ⟨122905444161055440768647197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163873925548073921024862929 122905444161055440768647197)
            ·
              refine ⟨46089541560395790288242699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122905444161055440768647197 46089541560395790288242699)
              ·
                refine ⟨69134312340593685432364049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46089541560395790288242699 69134312340593685432364049)
                ·
                  refine ⟨51850734255445264074273037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69134312340593685432364049 51850734255445264074273037)
                  ·
                    refine ⟨19444025345791974027852389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51850734255445264074273037 19444025345791974027852389)
                    ·
                      refine ⟨3645754752335995130222323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19444025345791974027852389 3645754752335995130222323)
                      ·
                        rfl

theorem cell23_7100082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7100082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100082 prefixEnd_7100082 := by exact prefixLift 7100082
  have htrace : WordTrace (prefixWord ++ tailWord_7100082) baseStart_7100082 baseEnd_7100082 := by
    simpa [prefixWord, tailWord_7100082, baseEnd_7100082] using wordTrace_append hprefix tailTrace_7100082
  have hstable : (prefixWord ++ tailWord_7100082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100082).length < 2 ^ (prefixWord ++ tailWord_7100082).sum := by decide
  have hdescent : baseEnd_7100082 < baseStart_7100082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100092 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_7100092 : Nat := 118140960795 + 7100092 * 2 ^ 59
def prefixEnd_7100092 : Nat := 4983230072969 + 3 ^ 40 * 7100092 * 2
def baseEnd_7100092 : Nat := 1215253295714180030365759

theorem tailTrace_7100092 : CollatzResearch.WordTrace tailWord_7100092 prefixEnd_7100092 1215253295714180030365759 := by
  unfold tailWord_7100092
  simp only [CollatzResearch.WordTrace]
  refine ⟨129480814896793379009379265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172641086529057838679172353 129480814896793379009379265)
  ·
    refine ⟨97110611172595034257034449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129480814896793379009379265 97110611172595034257034449)
    ·
      refine ⟨72832958379446275692775837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97110611172595034257034449 72832958379446275692775837)
      ·
        refine ⟨27312359392292353384790939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72832958379446275692775837 27312359392292353384790939)
        ·
          refine ⟨40968539088438530077186409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27312359392292353384790939 40968539088438530077186409)
          ·
            refine ⟨30726404316328897557889807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40968539088438530077186409 30726404316328897557889807)
            ·
              refine ⟨46089606474493346336834711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30726404316328897557889807 46089606474493346336834711)
              ·
                refine ⟨69134409711740019505252067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46089606474493346336834711 69134409711740019505252067)
                ·
                  refine ⟨103701614567610029257878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69134409711740019505252067 103701614567610029257878101)
                  ·
                    refine ⟨1215253295714180030365759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103701614567610029257878101 1215253295714180030365759)
                    ·
                      rfl

theorem cell23_7100092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_7100092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100092 prefixEnd_7100092 := by exact prefixLift 7100092
  have htrace : WordTrace (prefixWord ++ tailWord_7100092) baseStart_7100092 baseEnd_7100092 := by
    simpa [prefixWord, tailWord_7100092, baseEnd_7100092] using wordTrace_append hprefix tailTrace_7100092
  have hstable : (prefixWord ++ tailWord_7100092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100092).length < 2 ^ (prefixWord ++ tailWord_7100092).sum := by decide
  have hdescent : baseEnd_7100092 < baseStart_7100092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100139 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 5]
def baseStart_7100139 : Nat := 118140960795 + 7100139 * 2 ^ 59
def prefixEnd_7100139 : Nat := 4983230072969 + 3 ^ 40 * 7100139 * 2
def baseEnd_7100139 : Nat := 405087113414811267467729

theorem tailTrace_7100139 : CollatzResearch.WordTrace tailWord_7100139 prefixEnd_7100139 405087113414811267467729 := by
  unfold tailWord_7100139
  simp only [CollatzResearch.WordTrace]
  refine ⟨258963344024416485045719471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172642229349610990030479647 258963344024416485045719471)
  ·
    refine ⟨388445016036624727568579207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258963344024416485045719471 388445016036624727568579207)
    ·
      refine ⟨582667524054937091352868811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388445016036624727568579207 582667524054937091352868811)
      ·
        refine ⟨874001286082405637029303217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582667524054937091352868811 874001286082405637029303217)
        ·
          refine ⟨655500964561804227771977413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874001286082405637029303217 655500964561804227771977413)
          ·
            refine ⟨122906430855338292707245765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655500964561804227771977413 122906430855338292707245765)
            ·
              refine ⟨23044955785375929882608581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122906430855338292707245765 23044955785375929882608581)
              ·
                refine ⟨4320929209757986852989109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23044955785375929882608581 4320929209757986852989109)
                ·
                  refine ⟨405087113414811267467729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4320929209757986852989109 405087113414811267467729)
                  ·
                    rfl

theorem cell23_7100139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 5].length) (baseStart_7100139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100139 prefixEnd_7100139 := by exact prefixLift 7100139
  have htrace : WordTrace (prefixWord ++ tailWord_7100139) baseStart_7100139 baseEnd_7100139 := by
    simpa [prefixWord, tailWord_7100139, baseEnd_7100139] using wordTrace_append hprefix tailTrace_7100139
  have hstable : (prefixWord ++ tailWord_7100139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100139).length < 2 ^ (prefixWord ++ tailWord_7100139).sum := by decide
  have hdescent : baseEnd_7100139 < baseStart_7100139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100152 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_7100152 : Nat := 118140960795 + 7100152 * 2 ^ 59
def prefixEnd_7100152 : Nat := 4983230072969 + 3 ^ 40 * 7100152 * 2
def baseEnd_7100152 : Nat := 1215263565327269952115667

theorem tailTrace_7100152 : CollatzResearch.WordTrace tailWord_7100152 prefixEnd_7100152 1215263565327269952115667 := by
  unfold tailWord_7100152
  simp only [CollatzResearch.WordTrace]
  refine ⟨129481909086684694132971355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172642545448912925510628473 129481909086684694132971355)
  ·
    refine ⟨194222863630027041199457033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129481909086684694132971355 194222863630027041199457033)
    ·
      refine ⟨145667147722520280899592775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194222863630027041199457033 145667147722520280899592775)
      ·
        refine ⟨218500721583780421349389163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145667147722520280899592775 218500721583780421349389163)
        ·
          refine ⟨327751082375670632024083745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218500721583780421349389163 327751082375670632024083745)
          ·
            refine ⟨245813311781752974018062809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327751082375670632024083745 245813311781752974018062809)
            ·
              refine ⟨184359983836314730513547107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245813311781752974018062809 184359983836314730513547107)
              ·
                refine ⟨276539975754472095770320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184359983836314730513547107 276539975754472095770320661)
                ·
                  refine ⟨12962811363490879489233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276539975754472095770320661 12962811363490879489233781)
                  ·
                    refine ⟨1215263565327269952115667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12962811363490879489233781 1215263565327269952115667)
                    ·
                      rfl

theorem cell23_7100152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_7100152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100152 prefixEnd_7100152 := by exact prefixLift 7100152
  have htrace : WordTrace (prefixWord ++ tailWord_7100152) baseStart_7100152 baseEnd_7100152 := by
    simpa [prefixWord, tailWord_7100152, baseEnd_7100152] using wordTrace_append hprefix tailTrace_7100152
  have hstable : (prefixWord ++ tailWord_7100152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100152).length < 2 ^ (prefixWord ++ tailWord_7100152).sum := by decide
  have hdescent : baseEnd_7100152 < baseStart_7100152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100159 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 5, 2]
def baseStart_7100159 : Nat := 118140960795 + 7100159 * 2 ^ 59
def prefixEnd_7100159 : Nat := 4983230072969 + 3 ^ 40 * 7100159 * 2
def baseEnd_7100159 : Nat := 3645794290346391328959469

theorem tailTrace_7100159 : CollatzResearch.WordTrace tailWord_7100159 prefixEnd_7100159 3645794290346391328959469 := by
  unfold tailWord_7100159
  simp only [CollatzResearch.WordTrace]
  refine ⟨258964073484344028461447531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172642715656229352307631687 258964073484344028461447531)
  ·
    refine ⟨388446110226516042692171297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258964073484344028461447531 388446110226516042692171297)
    ·
      refine ⟨291334582669887032019128473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388446110226516042692171297 291334582669887032019128473)
      ·
        refine ⟨218500937002415274014346355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291334582669887032019128473 218500937002415274014346355)
        ·
          refine ⟨327751405503622911021519533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218500937002415274014346355 327751405503622911021519533)
          ·
            refine ⟨122906777063858591633069825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327751405503622911021519533 122906777063858591633069825)
            ·
              refine ⟨92180082797893943724802369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122906777063858591633069825 92180082797893943724802369)
              ·
                refine ⟨69135062098420457793601777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92180082797893943724802369 69135062098420457793601777)
                ·
                  refine ⟨51851296573815343345201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69135062098420457793601777 51851296573815343345201333)
                  ·
                    refine ⟨4861059053795188438612625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51851296573815343345201333 4861059053795188438612625)
                    ·
                      refine ⟨3645794290346391328959469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861059053795188438612625 3645794290346391328959469)
                      ·
                        rfl

theorem cell23_7100159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_7100159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100159 prefixEnd_7100159 := by exact prefixLift 7100159
  have htrace : WordTrace (prefixWord ++ tailWord_7100159) baseStart_7100159 baseEnd_7100159 := by
    simpa [prefixWord, tailWord_7100159, baseEnd_7100159] using wordTrace_append hprefix tailTrace_7100159
  have hstable : (prefixWord ++ tailWord_7100159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100159).length < 2 ^ (prefixWord ++ tailWord_7100159).sum := by decide
  have hdescent : baseEnd_7100159 < baseStart_7100159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100190 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_7100190 : Nat := 118140960795 + 7100190 * 2 ^ 59
def prefixEnd_7100190 : Nat := 4983230072969 + 3 ^ 40 * 7100190 * 2
def baseEnd_7100190 : Nat := 405090023138520078630203

theorem tailTrace_7100190 : CollatzResearch.WordTrace tailWord_7100190 prefixEnd_7100190 405090023138520078630203 := by
  unfold tailWord_7100190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32370650518403965094478253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172643469431487813837217349 32370650518403965094478253)
  ·
    refine ⟨12138993944401486910429345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32370650518403965094478253 12138993944401486910429345)
    ·
      refine ⟨9104245458301115182822009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12138993944401486910429345 9104245458301115182822009)
      ·
        refine ⟨6828184093725836387116507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9104245458301115182822009 6828184093725836387116507)
        ·
          refine ⟨10242276140588754580674761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828184093725836387116507 10242276140588754580674761)
          ·
            refine ⟨7681707105441565935506071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242276140588754580674761 7681707105441565935506071)
            ·
              refine ⟨11522560658162348903259107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681707105441565935506071 11522560658162348903259107)
              ·
                refine ⟨17283840987243523354888661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11522560658162348903259107 17283840987243523354888661)
                ·
                  refine ⟨405090023138520078630203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17283840987243523354888661 405090023138520078630203)
                  ·
                    rfl

theorem cell23_7100190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_7100190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100190 prefixEnd_7100190 := by exact prefixLift 7100190
  have htrace : WordTrace (prefixWord ++ tailWord_7100190) baseStart_7100190 baseEnd_7100190 := by
    simpa [prefixWord, tailWord_7100190, baseEnd_7100190] using wordTrace_append hprefix tailTrace_7100190
  have hstable : (prefixWord ++ tailWord_7100190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100190).length < 2 ^ (prefixWord ++ tailWord_7100190).sum := by decide
  have hdescent : baseEnd_7100190 < baseStart_7100190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100299 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_7100299 : Nat := 118140960795 + 7100299 * 2 ^ 59
def prefixEnd_7100299 : Nat := 4983230072969 + 3 ^ 40 * 7100299 * 2
def baseEnd_7100299 : Nat := 3645866177638020781208825

theorem tailTrace_7100299 : CollatzResearch.WordTrace tailWord_7100299 prefixEnd_7100299 3645866177638020781208825 := by
  unfold tailWord_7100299
  simp only [CollatzResearch.WordTrace]
  refine ⟨258969179703836832371543951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172646119802557888247695967 258969179703836832371543951)
  ·
    refine ⟨388453769555755248557315927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258969179703836832371543951 388453769555755248557315927)
    ·
      refine ⟨582680654333632872835973891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388453769555755248557315927 582680654333632872835973891)
      ·
        refine ⟨874020981500449309253960837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582680654333632872835973891 874020981500449309253960837)
        ·
          refine ⟨163878934031334245485117657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 874020981500449309253960837 163878934031334245485117657)
          ·
            refine ⟨122909200523500684113838243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163878934031334245485117657 122909200523500684113838243)
            ·
              refine ⟨184363800785251026170757365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122909200523500684113838243 184363800785251026170757365)
              ·
                refine ⟨17284106323617283703508503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184363800785251026170757365 17284106323617283703508503)
                ·
                  refine ⟨25926159485425925555262755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17284106323617283703508503 25926159485425925555262755)
                  ·
                    refine ⟨38889239228138888332894133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25926159485425925555262755 38889239228138888332894133)
                    ·
                      refine ⟨3645866177638020781208825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38889239228138888332894133 3645866177638020781208825)
                      ·
                        rfl

theorem cell23_7100299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_7100299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100299 prefixEnd_7100299 := by exact prefixLift 7100299
  have htrace : WordTrace (prefixWord ++ tailWord_7100299) baseStart_7100299 baseEnd_7100299 := by
    simpa [prefixWord, tailWord_7100299, baseEnd_7100299] using wordTrace_append hprefix tailTrace_7100299
  have hstable : (prefixWord ++ tailWord_7100299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100299).length < 2 ^ (prefixWord ++ tailWord_7100299).sum := by decide
  have hdescent : baseEnd_7100299 < baseStart_7100299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100309 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_7100309 : Nat := 118140960795 + 7100309 * 2 ^ 59
def prefixEnd_7100309 : Nat := 4983230072969 + 3 ^ 40 * 7100309 * 2
def baseEnd_7100309 : Nat := 3645871312444565742083779

theorem tailTrace_7100309 : CollatzResearch.WordTrace tailWord_7100309 prefixEnd_7100309 3645871312444565742083779 := by
  unfold tailWord_7100309
  simp only [CollatzResearch.WordTrace]
  refine ⟨258969544433800604079407981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172646362955867069386271987 258969544433800604079407981)
  ·
    refine ⟨97113579162675226529777993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258969544433800604079407981 97113579162675226529777993)
    ·
      refine ⟨72835184372006419897333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97113579162675226529777993 72835184372006419897333495)
      ·
        refine ⟨109252776558009629846000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72835184372006419897333495 109252776558009629846000243)
        ·
          refine ⟨163879164837014444769000365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109252776558009629846000243 163879164837014444769000365)
          ·
            refine ⟨61454686813880416788375137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163879164837014444769000365 61454686813880416788375137)
            ·
              refine ⟨46091015110410312591281353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61454686813880416788375137 46091015110410312591281353)
              ·
                refine ⟨34568261332807734443461015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46091015110410312591281353 34568261332807734443461015)
                ·
                  refine ⟨51852391999211601665191523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34568261332807734443461015 51852391999211601665191523)
                  ·
                    refine ⟨77778587998817402497787285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51852391999211601665191523 77778587998817402497787285)
                    ·
                      refine ⟨3645871312444565742083779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77778587998817402497787285 3645871312444565742083779)
                      ·
                        rfl

theorem cell23_7100309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_7100309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100309 prefixEnd_7100309 := by exact prefixLift 7100309
  have htrace : WordTrace (prefixWord ++ tailWord_7100309) baseStart_7100309 baseEnd_7100309 := by
    simpa [prefixWord, tailWord_7100309, baseEnd_7100309] using wordTrace_append hprefix tailTrace_7100309
  have hstable : (prefixWord ++ tailWord_7100309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100309).length < 2 ^ (prefixWord ++ tailWord_7100309).sum := by decide
  have hdescent : baseEnd_7100309 < baseStart_7100309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100313 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 3, 2, 2]
def baseStart_7100313 : Nat := 118140960795 + 7100313 * 2 ^ 59
def prefixEnd_7100313 : Nat := 4983230072969 + 3 ^ 40 * 7100313 * 2
def baseEnd_7100313 : Nat := 3645873366367183726433761

theorem tailTrace_7100313 : CollatzResearch.WordTrace tailWord_7100313 prefixEnd_7100313 3645873366367183726433761 := by
  unfold tailWord_7100313
  simp only [CollatzResearch.WordTrace]
  refine ⟨258969690325786112762553593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172646460217190741841702395 258969690325786112762553593)
  ·
    refine ⟨194227267744339584571915195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258969690325786112762553593 194227267744339584571915195)
    ·
      refine ⟨291340901616509376857872793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194227267744339584571915195 291340901616509376857872793)
      ·
        refine ⟨218505676212382032643404595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291340901616509376857872793 218505676212382032643404595)
        ·
          refine ⟨327758514318573048965106893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218505676212382032643404595 327758514318573048965106893)
          ·
            refine ⟨122909442869464893361915085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327758514318573048965106893 122909442869464893361915085)
            ·
              refine ⟨46091041076049335010718157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122909442869464893361915085 46091041076049335010718157)
              ·
                refine ⟨17284140403518500629019309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46091041076049335010718157 17284140403518500629019309)
                ·
                  refine ⟨6481552651319437735882241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17284140403518500629019309 6481552651319437735882241)
                  ·
                    refine ⟨4861164488489578301911681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481552651319437735882241 4861164488489578301911681)
                    ·
                      refine ⟨3645873366367183726433761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861164488489578301911681 3645873366367183726433761)
                      ·
                        rfl

theorem cell23_7100313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_7100313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100313 prefixEnd_7100313 := by exact prefixLift 7100313
  have htrace : WordTrace (prefixWord ++ tailWord_7100313) baseStart_7100313 baseEnd_7100313 := by
    simpa [prefixWord, tailWord_7100313, baseEnd_7100313] using wordTrace_append hprefix tailTrace_7100313
  have hstable : (prefixWord ++ tailWord_7100313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100313).length < 2 ^ (prefixWord ++ tailWord_7100313).sum := by decide
  have hdescent : baseEnd_7100313 < baseStart_7100313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100316 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7100316 : Nat := 118140960795 + 7100316 * 2 ^ 59
def prefixEnd_7100316 : Nat := 4983230072969 + 3 ^ 40 * 7100316 * 2
def baseEnd_7100316 : Nat := 3645874906809147214696247

theorem tailTrace_7100316 : CollatzResearch.WordTrace tailWord_7100316 prefixEnd_7100316 3645874906809147214696247 := by
  unfold tailWord_7100316
  simp only [CollatzResearch.WordTrace]
  refine ⟨129484899872387622137456401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172646533163183496183275201 129484899872387622137456401)
  ·
    refine ⟨97113674904290716603092301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129484899872387622137456401 97113674904290716603092301)
    ·
      refine ⟨36417628089109018726159613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97113674904290716603092301 36417628089109018726159613)
      ·
        refine ⟨13656610533415882022309855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36417628089109018726159613 13656610533415882022309855)
        ·
          refine ⟨20484915800123823033464783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13656610533415882022309855 20484915800123823033464783)
          ·
            refine ⟨30727373700185734550197175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20484915800123823033464783 30727373700185734550197175)
            ·
              refine ⟨46091060550278601825295763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30727373700185734550197175 46091060550278601825295763)
              ·
                refine ⟨69136590825417902737943645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46091060550278601825295763 69136590825417902737943645)
                ·
                  refine ⟨25926221559531713526728867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69136590825417902737943645 25926221559531713526728867)
                  ·
                    refine ⟨38889332339297570290093301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25926221559531713526728867 38889332339297570290093301)
                    ·
                      refine ⟨3645874906809147214696247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38889332339297570290093301 3645874906809147214696247)
                      ·
                        rfl

theorem cell23_7100316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7100316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100316 prefixEnd_7100316 := by exact prefixLift 7100316
  have htrace : WordTrace (prefixWord ++ tailWord_7100316) baseStart_7100316 baseEnd_7100316 := by
    simpa [prefixWord, tailWord_7100316, baseEnd_7100316] using wordTrace_append hprefix tailTrace_7100316
  have hstable : (prefixWord ++ tailWord_7100316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100316).length < 2 ^ (prefixWord ++ tailWord_7100316).sum := by decide
  have hdescent : baseEnd_7100316 < baseStart_7100316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100359 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_7100359 : Nat := 118140960795 + 7100359 * 2 ^ 59
def prefixEnd_7100359 : Nat := 4983230072969 + 3 ^ 40 * 7100359 * 2
def baseEnd_7100359 : Nat := 3645896986477290546458549

theorem tailTrace_7100359 : CollatzResearch.WordTrace tailWord_7100359 prefixEnd_7100359 3645896986477290546458549 := by
  unfold tailWord_7100359
  simp only [CollatzResearch.WordTrace]
  refine ⟨258971368083619462618728131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172647578722412975079152087 258971368083619462618728131)
  ·
    refine ⟨388457052125429193928092197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258971368083619462618728131 388457052125429193928092197)
    ·
      refine ⟨72835697273517973861517287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388457052125429193928092197 72835697273517973861517287)
      ·
        refine ⟨109253545910276960792275931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72835697273517973861517287 109253545910276960792275931)
        ·
          refine ⟨163880318865415441188413897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109253545910276960792275931 163880318865415441188413897)
          ·
            refine ⟨122910239149061580891310423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163880318865415441188413897 122910239149061580891310423)
            ·
              refine ⟨184365358723592371336965635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122910239149061580891310423 184365358723592371336965635)
              ·
                refine ⟨276548038085388557005448453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184365358723592371336965635 276548038085388557005448453)
                ·
                  refine ⟨51852757141010354438521585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276548038085388557005448453 51852757141010354438521585)
                  ·
                    refine ⟨38889567855757765828891189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51852757141010354438521585 38889567855757765828891189)
                    ·
                      refine ⟨3645896986477290546458549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38889567855757765828891189 3645896986477290546458549)
                      ·
                        rfl

theorem cell23_7100359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_7100359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100359 prefixEnd_7100359 := by exact prefixLift 7100359
  have htrace : WordTrace (prefixWord ++ tailWord_7100359) baseStart_7100359 baseEnd_7100359 := by
    simpa [prefixWord, tailWord_7100359, baseEnd_7100359] using wordTrace_append hprefix tailTrace_7100359
  have hstable : (prefixWord ++ tailWord_7100359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100359).length < 2 ^ (prefixWord ++ tailWord_7100359).sum := by decide
  have hdescent : baseEnd_7100359 < baseStart_7100359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100363 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 3]
def baseStart_7100363 : Nat := 118140960795 + 7100363 * 2 ^ 59
def prefixEnd_7100363 : Nat := 4983230072969 + 3 ^ 40 * 7100363 * 2
def baseEnd_7100363 : Nat := 3645899040399908530808531

theorem tailTrace_7100363 : CollatzResearch.WordTrace tailWord_7100363 prefixEnd_7100363 3645899040399908530808531 := by
  unfold tailWord_7100363
  simp only [CollatzResearch.WordTrace]
  refine ⟨258971513975604971301873743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172647675983736647534582495 258971513975604971301873743)
  ·
    refine ⟨388457270963407456952810615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258971513975604971301873743 388457270963407456952810615)
    ·
      refine ⟨582685906445111185429215923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388457270963407456952810615 582685906445111185429215923)
      ·
        refine ⟨874028859667666778143823885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582685906445111185429215923 874028859667666778143823885)
        ·
          refine ⟨327760822375375041803933957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874028859667666778143823885 327760822375375041803933957)
          ·
            refine ⟨61455154195382820338237617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327760822375375041803933957 61455154195382820338237617)
            ·
              refine ⟨46091365646537115253678213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61455154195382820338237617 46091365646537115253678213)
              ·
                refine ⟨8642131058725709110064665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46091365646537115253678213 8642131058725709110064665)
                ·
                  refine ⟨6481598294044281832548499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642131058725709110064665 6481598294044281832548499)
                  ·
                    refine ⟨9722397441066422748822749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6481598294044281832548499 9722397441066422748822749)
                    ·
                      refine ⟨3645899040399908530808531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9722397441066422748822749 3645899040399908530808531)
                      ·
                        rfl

theorem cell23_7100363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 3].length) (baseStart_7100363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100363 prefixEnd_7100363 := by exact prefixLift 7100363
  have htrace : WordTrace (prefixWord ++ tailWord_7100363) baseStart_7100363 baseEnd_7100363 := by
    simpa [prefixWord, tailWord_7100363, baseEnd_7100363] using wordTrace_append hprefix tailTrace_7100363
  have hstable : (prefixWord ++ tailWord_7100363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100363).length < 2 ^ (prefixWord ++ tailWord_7100363).sum := by decide
  have hdescent : baseEnd_7100363 < baseStart_7100363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100364 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7100364 : Nat := 118140960795 + 7100364 * 2 ^ 59
def prefixEnd_7100364 : Nat := 4983230072969 + 3 ^ 40 * 7100364 * 2
def baseEnd_7100364 : Nat := 3645899553880563026896027

theorem tailTrace_7100364 : CollatzResearch.WordTrace tailWord_7100364 prefixEnd_7100364 3645899553880563026896027 := by
  unfold tailWord_7100364
  simp only [CollatzResearch.WordTrace]
  refine ⟨129485775224300674236330073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172647700299067565648440097 129485775224300674236330073)
  ·
    refine ⟨97114331418225505677247555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129485775224300674236330073 97114331418225505677247555)
    ·
      refine ⟨145671497127338258515871333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97114331418225505677247555 145671497127338258515871333)
      ·
        refine ⟨27313405711375923471725875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145671497127338258515871333 27313405711375923471725875)
        ·
          refine ⟨40970108567063885207588813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27313405711375923471725875 40970108567063885207588813)
          ·
            refine ⟨15363790712648956952845805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40970108567063885207588813 15363790712648956952845805)
            ·
              refine ⟨5761421517243358857317177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15363790712648956952845805 5761421517243358857317177)
              ·
                refine ⟨4321066137932519142987883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761421517243358857317177 4321066137932519142987883)
                ·
                  refine ⟨6481599206898778714481825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321066137932519142987883 6481599206898778714481825)
                  ·
                    refine ⟨4861199405174084035861369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481599206898778714481825 4861199405174084035861369)
                    ·
                      refine ⟨3645899553880563026896027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861199405174084035861369 3645899553880563026896027)
                      ·
                        rfl

theorem cell23_7100364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7100364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100364 prefixEnd_7100364 := by exact prefixLift 7100364
  have htrace : WordTrace (prefixWord ++ tailWord_7100364) baseStart_7100364 baseEnd_7100364 := by
    simpa [prefixWord, tailWord_7100364, baseEnd_7100364] using wordTrace_append hprefix tailTrace_7100364
  have hstable : (prefixWord ++ tailWord_7100364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100364).length < 2 ^ (prefixWord ++ tailWord_7100364).sum := by decide
  have hdescent : baseEnd_7100364 < baseStart_7100364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100374 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7100374 : Nat := 118140960795 + 7100374 * 2 ^ 59
def prefixEnd_7100374 : Nat := 4983230072969 + 3 ^ 40 * 7100374 * 2
def baseEnd_7100374 : Nat := 1215301562895702662590327

theorem tailTrace_7100374 : CollatzResearch.WordTrace tailWord_7100374 prefixEnd_7100374 1215301562895702662590327 := by
  unfold tailWord_7100374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16185744698660320011282761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172647943452376746787016117 16185744698660320011282761)
  ·
    refine ⟨12139308523995240008462071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16185744698660320011282761 12139308523995240008462071)
    ·
      refine ⟨18208962785992860012693107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12139308523995240008462071 18208962785992860012693107)
      ·
        refine ⟨27313444178989290019039661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18208962785992860012693107 27313444178989290019039661)
        ·
          refine ⟨10242541567120983757139873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27313444178989290019039661 10242541567120983757139873)
          ·
            refine ⟨7681906175340737817854905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242541567120983757139873 7681906175340737817854905)
            ·
              refine ⟨5761429631505553363391179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7681906175340737817854905 5761429631505553363391179)
              ·
                refine ⟨8642144447258330045086769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761429631505553363391179 8642144447258330045086769)
                ·
                  refine ⟨6481608335443747533815077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642144447258330045086769 6481608335443747533815077)
                  ·
                    refine ⟨1215301562895702662590327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481608335443747533815077 1215301562895702662590327)
                    ·
                      rfl

theorem cell23_7100374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7100374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100374 prefixEnd_7100374 := by exact prefixLift 7100374
  have htrace : WordTrace (prefixWord ++ tailWord_7100374) baseStart_7100374 baseEnd_7100374 := by
    simpa [prefixWord, tailWord_7100374, baseEnd_7100374] using wordTrace_append hprefix tailTrace_7100374
  have hstable : (prefixWord ++ tailWord_7100374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100374).length < 2 ^ (prefixWord ++ tailWord_7100374).sum := by decide
  have hdescent : baseEnd_7100374 < baseStart_7100374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100403 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 6, 2, 2]
def baseStart_7100403 : Nat := 118140960795 + 7100403 * 2 ^ 59
def prefixEnd_7100403 : Nat := 4983230072969 + 3 ^ 40 * 7100403 * 2
def baseEnd_7100403 : Nat := 3645919579626088374308347

theorem tailTrace_7100403 : CollatzResearch.WordTrace tailWord_7100403 prefixEnd_7100403 3645919579626088374308347 := by
  unfold tailWord_7100403
  simp only [CollatzResearch.WordTrace]
  refine ⟨258972972895460058133329863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172648648596973372088886575 258972972895460058133329863)
  ·
    refine ⟨388459459343190087199994795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258972972895460058133329863 388459459343190087199994795)
    ·
      refine ⟨582689189014785130799992193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388459459343190087199994795 582689189014785130799992193)
      ·
        refine ⟨437016891761088848099994145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582689189014785130799992193 437016891761088848099994145)
        ·
          refine ⟨327762668820816636074995609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437016891761088848099994145 327762668820816636074995609)
          ·
            refine ⟨245822001615612477056246707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327762668820816636074995609 245822001615612477056246707)
            ·
              refine ⟨368733002423418715584370061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245822001615612477056246707 368733002423418715584370061)
              ·
                refine ⟨138274875908782018344138773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368733002423418715584370061 138274875908782018344138773)
                ·
                  refine ⟨6481634808224157109881505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138274875908782018344138773 6481634808224157109881505)
                  ·
                    refine ⟨4861226106168117832411129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481634808224157109881505 4861226106168117832411129)
                    ·
                      refine ⟨3645919579626088374308347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861226106168117832411129 3645919579626088374308347)
                      ·
                        rfl

theorem cell23_7100403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 2, 2].length) (baseStart_7100403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100403 prefixEnd_7100403 := by exact prefixLift 7100403
  have htrace : WordTrace (prefixWord ++ tailWord_7100403) baseStart_7100403 baseEnd_7100403 := by
    simpa [prefixWord, tailWord_7100403, baseEnd_7100403] using wordTrace_append hprefix tailTrace_7100403
  have hstable : (prefixWord ++ tailWord_7100403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100403).length < 2 ^ (prefixWord ++ tailWord_7100403).sum := by decide
  have hdescent : baseEnd_7100403 < baseStart_7100403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100419 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_7100419 : Nat := 118140960795 + 7100419 * 2 ^ 59
def prefixEnd_7100419 : Nat := 4983230072969 + 3 ^ 40 * 7100419 * 2
def baseEnd_7100419 : Nat := 3645927795316560311708273

theorem tailTrace_7100419 : CollatzResearch.WordTrace tailWord_7100419 prefixEnd_7100419 3645927795316560311708273 := by
  unfold tailWord_7100419
  simp only [CollatzResearch.WordTrace]
  refine ⟨258973556463402092865912311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172649037642268061910608207 258973556463402092865912311)
  ·
    refine ⟨388460334695103139298868467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258973556463402092865912311 388460334695103139298868467)
    ·
      refine ⟨582690502042654708948302701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388460334695103139298868467 582690502042654708948302701)
      ·
        refine ⟨218508938265995515855613513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582690502042654708948302701 218508938265995515855613513)
        ·
          refine ⟨163881703699496636891710135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218508938265995515855613513 163881703699496636891710135)
          ·
            refine ⟨245822555549244955337565203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163881703699496636891710135 245822555549244955337565203)
            ·
              refine ⟨368733833323867433006347805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245822555549244955337565203 368733833323867433006347805)
              ·
                refine ⟨138275187496450287377380427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368733833323867433006347805 138275187496450287377380427)
                ·
                  refine ⟨207412781244675431066070641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138275187496450287377380427 207412781244675431066070641)
                  ·
                    refine ⟨155559585933506573299552981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207412781244675431066070641 155559585933506573299552981)
                    ·
                      refine ⟨3645927795316560311708273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155559585933506573299552981 3645927795316560311708273)
                      ·
                        rfl

theorem cell23_7100419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_7100419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100419 prefixEnd_7100419 := by exact prefixLift 7100419
  have htrace : WordTrace (prefixWord ++ tailWord_7100419) baseStart_7100419 baseEnd_7100419 := by
    simpa [prefixWord, tailWord_7100419, baseEnd_7100419] using wordTrace_append hprefix tailTrace_7100419
  have hstable : (prefixWord ++ tailWord_7100419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100419).length < 2 ^ (prefixWord ++ tailWord_7100419).sum := by decide
  have hdescent : baseEnd_7100419 < baseStart_7100419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100493 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7100493 : Nat := 118140960795 + 7100493 * 2 ^ 59
def prefixEnd_7100493 : Nat := 4983230072969 + 3 ^ 40 * 7100493 * 2
def baseEnd_7100493 : Nat := 3645965792884993022182933

theorem tailTrace_7100493 : CollatzResearch.WordTrace tailWord_7100493 prefixEnd_7100493 3645965792884993022182933 := by
  unfold tailWord_7100493
  simp only [CollatzResearch.WordTrace]
  refine ⟨258976255465134003504106133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172650836976756002336070755 258976255465134003504106133)
  ·
    refine ⟨12139511974928156414254975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258976255465134003504106133 12139511974928156414254975)
    ·
      refine ⟨18209267962392234621382463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12139511974928156414254975 18209267962392234621382463)
      ·
        refine ⟨27313901943588351932073695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18209267962392234621382463 27313901943588351932073695)
        ·
          refine ⟨40970852915382527898110543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27313901943588351932073695 40970852915382527898110543)
          ·
            refine ⟨61456279373073791847165815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40970852915382527898110543 61456279373073791847165815)
            ·
              refine ⟨92184419059610687770748723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61456279373073791847165815 92184419059610687770748723)
              ·
                refine ⟨138276628589416031656123085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92184419059610687770748723 138276628589416031656123085)
                ·
                  refine ⟨51853735721031011871046157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138276628589416031656123085 51853735721031011871046157)
                  ·
                    refine ⟨19445150895386629451642309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51853735721031011871046157 19445150895386629451642309)
                    ·
                      refine ⟨3645965792884993022182933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19445150895386629451642309 3645965792884993022182933)
                      ·
                        rfl

theorem cell23_7100493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7100493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100493 prefixEnd_7100493 := by exact prefixLift 7100493
  have htrace : WordTrace (prefixWord ++ tailWord_7100493) baseStart_7100493 baseEnd_7100493 := by
    simpa [prefixWord, tailWord_7100493, baseEnd_7100493] using wordTrace_append hprefix tailTrace_7100493
  have hstable : (prefixWord ++ tailWord_7100493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100493).length < 2 ^ (prefixWord ++ tailWord_7100493).sum := by decide
  have hdescent : baseEnd_7100493 < baseStart_7100493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100503 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 3, 4]
def baseStart_7100503 : Nat := 118140960795 + 7100503 * 2 ^ 59
def prefixEnd_7100503 : Nat := 4983230072969 + 3 ^ 40 * 7100503 * 2
def baseEnd_7100503 : Nat := 1215323642563845994352629

theorem tailTrace_7100503 : CollatzResearch.WordTrace tailWord_7100503 prefixEnd_7100503 1215323642563845994352629 := by
  unfold tailWord_7100503
  simp only [CollatzResearch.WordTrace]
  refine ⟨258976620195097775211970163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172651080130065183474646775 258976620195097775211970163)
  ·
    refine ⟨388464930292646662817955245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258976620195097775211970163 388464930292646662817955245)
    ·
      refine ⟨145674348859742498556733217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388464930292646662817955245 145674348859742498556733217)
      ·
        refine ⟨109255761644806873917549913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145674348859742498556733217 109255761644806873917549913)
        ·
          refine ⟨81941821233605155438162435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109255761644806873917549913 81941821233605155438162435)
          ·
            refine ⟨122912731850407733157243653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81941821233605155438162435 122912731850407733157243653)
            ·
              refine ⟨23046137221951449966983185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122912731850407733157243653 23046137221951449966983185)
              ·
                refine ⟨17284602916463587475237389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23046137221951449966983185 17284602916463587475237389)
                ·
                  refine ⟨6481726093673845303214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17284602916463587475237389 6481726093673845303214021)
                  ·
                    refine ⟨1215323642563845994352629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481726093673845303214021 1215323642563845994352629)
                    ·
                      rfl

theorem cell23_7100503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_7100503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100503 prefixEnd_7100503 := by exact prefixLift 7100503
  have htrace : WordTrace (prefixWord ++ tailWord_7100503) baseStart_7100503 baseEnd_7100503 := by
    simpa [prefixWord, tailWord_7100503, baseEnd_7100503] using wordTrace_append hprefix tailTrace_7100503
  have hstable : (prefixWord ++ tailWord_7100503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100503).length < 2 ^ (prefixWord ++ tailWord_7100503).sum := by decide
  have hdescent : baseEnd_7100503 < baseStart_7100503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100506 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_7100506 : Nat := 118140960795 + 7100506 * 2 ^ 59
def prefixEnd_7100506 : Nat := 4983230072969 + 3 ^ 40 * 7100506 * 2
def baseEnd_7100506 : Nat := 3645972468133501471320373

theorem tailTrace_7100506 : CollatzResearch.WordTrace tailWord_7100506 prefixEnd_7100506 3645972468133501471320373 := by
  unfold tailWord_7100506
  simp only [CollatzResearch.WordTrace]
  refine ⟨64744182403521726681082343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172651153076057937816219581 64744182403521726681082343)
  ·
    refine ⟨97116273605282590021623515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64744182403521726681082343 97116273605282590021623515)
    ·
      refine ⟨145674410407923885032435273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97116273605282590021623515 145674410407923885032435273)
      ·
        refine ⟨109255807805942913774326455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145674410407923885032435273 109255807805942913774326455)
        ·
          refine ⟨163883711708914370661489683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109255807805942913774326455 163883711708914370661489683)
          ·
            refine ⟨245825567563371555992234525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163883711708914370661489683 245825567563371555992234525)
            ·
              refine ⟨92184587836264333497087947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245825567563371555992234525 92184587836264333497087947)
              ·
                refine ⟨138276881754396500245631921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92184587836264333497087947 138276881754396500245631921)
                ·
                  refine ⟨103707661315797375184223941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138276881754396500245631921 103707661315797375184223941)
                  ·
                    refine ⟨19445186496712007847041989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103707661315797375184223941 19445186496712007847041989)
                    ·
                      refine ⟨3645972468133501471320373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19445186496712007847041989 3645972468133501471320373)
                      ·
                        rfl

theorem cell23_7100506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_7100506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100506 prefixEnd_7100506 := by exact prefixLift 7100506
  have htrace : WordTrace (prefixWord ++ tailWord_7100506) baseStart_7100506 baseEnd_7100506 := by
    simpa [prefixWord, tailWord_7100506, baseEnd_7100506] using wordTrace_append hprefix tailTrace_7100506
  have hstable : (prefixWord ++ tailWord_7100506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100506).length < 2 ^ (prefixWord ++ tailWord_7100506).sum := by decide
  have hdescent : baseEnd_7100506 < baseStart_7100506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100513 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_7100513 : Nat := 118140960795 + 7100513 * 2 ^ 59
def prefixEnd_7100513 : Nat := 4983230072969 + 3 ^ 40 * 7100513 * 2
def baseEnd_7100513 : Nat := 3645976062498082943932841

theorem tailTrace_7100513 : CollatzResearch.WordTrace tailWord_7100513 prefixEnd_7100513 3645976062498082943932841 := by
  unfold tailWord_7100513
  simp only [CollatzResearch.WordTrace]
  refine ⟨258976984925061546919834193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172651323283374364613222795 258976984925061546919834193)
  ·
    refine ⟨194232738693796160189875645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258976984925061546919834193 194232738693796160189875645)
    ·
      refine ⟨72837277010173560071203367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194232738693796160189875645 72837277010173560071203367)
      ·
        refine ⟨109255915515260340106805051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72837277010173560071203367 109255915515260340106805051)
        ·
          refine ⟨163883873272890510160207577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109255915515260340106805051 163883873272890510160207577)
          ·
            refine ⟨122912904954667882620155683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163883873272890510160207577 122912904954667882620155683)
            ·
              refine ⟨184369357432001823930233525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122912904954667882620155683 184369357432001823930233525)
              ·
                refine ⟨17284627259250170993459393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184369357432001823930233525 17284627259250170993459393)
                ·
                  refine ⟨12963470444437628245094545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17284627259250170993459393 12963470444437628245094545)
                  ·
                    refine ⟨9722602833328221183820909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12963470444437628245094545 9722602833328221183820909)
                    ·
                      refine ⟨3645976062498082943932841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9722602833328221183820909 3645976062498082943932841)
                      ·
                        rfl

theorem cell23_7100513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_7100513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100513 prefixEnd_7100513 := by exact prefixLift 7100513
  have htrace : WordTrace (prefixWord ++ tailWord_7100513) baseStart_7100513 baseEnd_7100513 := by
    simpa [prefixWord, tailWord_7100513, baseEnd_7100513] using wordTrace_append hprefix tailTrace_7100513
  have hstable : (prefixWord ++ tailWord_7100513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100513).length < 2 ^ (prefixWord ++ tailWord_7100513).sum := by decide
  have hdescent : baseEnd_7100513 < baseStart_7100513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100516 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 8]
def baseStart_7100516 : Nat := 118140960795 + 7100516 * 2 ^ 59
def prefixEnd_7100516 : Nat := 4983230072969 + 3 ^ 40 * 7100516 * 2
def baseEnd_7100516 : Nat := 405108622548894048021703

theorem tailTrace_7100516 : CollatzResearch.WordTrace tailWord_7100516 prefixEnd_7100516 405108622548894048021703 := by
  unfold tailWord_7100516
  simp only [CollatzResearch.WordTrace]
  refine ⟨129488547172025339216096701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172651396229367118954795601 129488547172025339216096701)
  ·
    refine ⟨48558205189509502206036263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129488547172025339216096701 48558205189509502206036263)
    ·
      refine ⟨72837307784264253309054395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48558205189509502206036263 72837307784264253309054395)
      ·
        refine ⟨109255961676396379963581593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72837307784264253309054395 109255961676396379963581593)
        ·
          refine ⟨81941971257297284972686195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109255961676396379963581593 81941971257297284972686195)
          ·
            refine ⟨122912956885945927459029293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81941971257297284972686195 122912956885945927459029293)
            ·
              refine ⟨46092358832229722797135985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122912956885945927459029293 46092358832229722797135985)
              ·
                refine ⟨34569269124172292097851989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46092358832229722797135985 34569269124172292097851989)
                ·
                  refine ⟨405108622548894048021703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34569269124172292097851989 405108622548894048021703)
                  ·
                    rfl

theorem cell23_7100516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_7100516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100516 prefixEnd_7100516 := by exact prefixLift 7100516
  have htrace : WordTrace (prefixWord ++ tailWord_7100516) baseStart_7100516 baseEnd_7100516 := by
    simpa [prefixWord, tailWord_7100516, baseEnd_7100516] using wordTrace_append hprefix tailTrace_7100516
  have hstable : (prefixWord ++ tailWord_7100516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100516).length < 2 ^ (prefixWord ++ tailWord_7100516).sum := by decide
  have hdescent : baseEnd_7100516 < baseStart_7100516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100530 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7100530 : Nat := 118140960795 + 7100530 * 2 ^ 59
def prefixEnd_7100530 : Nat := 4983230072969 + 3 ^ 40 * 7100530 * 2
def baseEnd_7100530 : Nat := 3645984791669209377420263

theorem tailTrace_7100530 : CollatzResearch.WordTrace tailWord_7100530 prefixEnd_7100530 3645984791669209377420263 := by
  unfold tailWord_7100530
  simp only [CollatzResearch.WordTrace]
  refine ⟨64744401241499989705800761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172651736643999972548802029 64744401241499989705800761)
  ·
    refine ⟨48558300931124992279350571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64744401241499989705800761 48558300931124992279350571)
    ·
      refine ⟨72837451396687488419025857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48558300931124992279350571 72837451396687488419025857)
      ·
        refine ⟨54628088547515616314269393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72837451396687488419025857 54628088547515616314269393)
        ·
          refine ⟨40971066410636712235702045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54628088547515616314269393 40971066410636712235702045)
          ·
            refine ⟨15364149903988767088388267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40971066410636712235702045 15364149903988767088388267)
            ·
              refine ⟨23046224855983150632582401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364149903988767088388267 23046224855983150632582401)
              ·
                refine ⟨17284668641987362974436801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23046224855983150632582401 17284668641987362974436801)
                ·
                  refine ⟨12963501481490522230827601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17284668641987362974436801 12963501481490522230827601)
                  ·
                    refine ⟨9722626111117891673120701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12963501481490522230827601 9722626111117891673120701)
                    ·
                      refine ⟨3645984791669209377420263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9722626111117891673120701 3645984791669209377420263)
                      ·
                        rfl

theorem cell23_7100530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7100530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100530 prefixEnd_7100530 := by exact prefixLift 7100530
  have htrace : WordTrace (prefixWord ++ tailWord_7100530) baseStart_7100530 baseEnd_7100530 := by
    simpa [prefixWord, tailWord_7100530, baseEnd_7100530] using wordTrace_append hprefix tailTrace_7100530
  have hstable : (prefixWord ++ tailWord_7100530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100530).length < 2 ^ (prefixWord ++ tailWord_7100530).sum := by decide
  have hdescent : baseEnd_7100530 < baseStart_7100530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100564 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7100564 : Nat := 118140960795 + 7100564 * 2 ^ 59
def prefixEnd_7100564 : Nat := 4983230072969 + 3 ^ 40 * 7100564 * 2
def baseEnd_7100564 : Nat := 3646002250011462244395107

theorem tailTrace_7100564 : CollatzResearch.WordTrace tailWord_7100564 prefixEnd_7100564 3646002250011462244395107 := by
  unfold tailWord_7100564
  simp only [CollatzResearch.WordTrace]
  refine ⟨129489422523938391314970373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172652563365251188419960497 129489422523938391314970373)
  ·
    refine ⟨24279266723238448371556945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129489422523938391314970373 24279266723238448371556945)
    ·
      refine ⟨18209450042428836278667709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24279266723238448371556945 18209450042428836278667709)
      ·
        refine ⟨6828543765910813604500391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18209450042428836278667709 6828543765910813604500391)
        ·
          refine ⟨10242815648866220406750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828543765910813604500391 10242815648866220406750587)
          ·
            refine ⟨15364223473299330610125881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242815648866220406750587 15364223473299330610125881)
            ·
              refine ⟨11523167604974497957594411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15364223473299330610125881 11523167604974497957594411)
              ·
                refine ⟨17284751407461746936391617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11523167604974497957594411 17284751407461746936391617)
                ·
                  refine ⟨12963563555596310202293713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17284751407461746936391617 12963563555596310202293713)
                  ·
                    refine ⟨9722672666697232651720285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12963563555596310202293713 9722672666697232651720285)
                    ·
                      refine ⟨3646002250011462244395107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9722672666697232651720285 3646002250011462244395107)
                      ·
                        rfl

theorem cell23_7100564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7100564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100564 prefixEnd_7100564 := by exact prefixLift 7100564
  have htrace : WordTrace (prefixWord ++ tailWord_7100564) baseStart_7100564 baseEnd_7100564 := by
    simpa [prefixWord, tailWord_7100564, baseEnd_7100564] using wordTrace_append hprefix tailTrace_7100564
  have hstable : (prefixWord ++ tailWord_7100564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100564).length < 2 ^ (prefixWord ++ tailWord_7100564).sum := by decide
  have hdescent : baseEnd_7100564 < baseStart_7100564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100603 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3]
def baseStart_7100603 : Nat := 118140960795 + 7100603 * 2 ^ 59
def prefixEnd_7100603 : Nat := 4983230072969 + 3 ^ 40 * 7100603 * 2
def baseEnd_7100603 : Nat := 3646022275756987591807427

theorem tailTrace_7100603 : CollatzResearch.WordTrace tailWord_7100603 prefixEnd_7100603 3646022275756987591807427 := by
  unfold tailWord_7100603
  simp only [CollatzResearch.WordTrace]
  refine ⟨258980267494735492290610463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172653511663156994860406975 258980267494735492290610463)
  ·
    refine ⟨388470401242103238435915695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258980267494735492290610463 388470401242103238435915695)
    ·
      refine ⟨582705601863154857653873543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388470401242103238435915695 582705601863154857653873543)
      ·
        refine ⟨874058402794732286480810315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582705601863154857653873543 874058402794732286480810315)
        ·
          refine ⟨1311087604192098429721215473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874058402794732286480810315 1311087604192098429721215473)
          ·
            refine ⟨983315703144073822290911605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1311087604192098429721215473 983315703144073822290911605)
            ·
              refine ⟨92185847169756920839772963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 983315703144073822290911605 92185847169756920839772963)
              ·
                refine ⟨138278770754635381259659445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92185847169756920839772963 138278770754635381259659445)
                ·
                  refine ⟨12963634758247066993093073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138278770754635381259659445 12963634758247066993093073)
                  ·
                    refine ⟨9722726068685300244819805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12963634758247066993093073 9722726068685300244819805)
                    ·
                      refine ⟨3646022275756987591807427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9722726068685300244819805 3646022275756987591807427)
                      ·
                        rfl

theorem cell23_7100603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].length) (baseStart_7100603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100603 prefixEnd_7100603 := by exact prefixLift 7100603
  have htrace : WordTrace (prefixWord ++ tailWord_7100603) baseStart_7100603 baseEnd_7100603 := by
    simpa [prefixWord, tailWord_7100603, baseEnd_7100603] using wordTrace_append hprefix tailTrace_7100603
  have hstable : (prefixWord ++ tailWord_7100603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100603).length < 2 ^ (prefixWord ++ tailWord_7100603).sum := by decide
  have hdescent : baseEnd_7100603 < baseStart_7100603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100613 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_7100613 : Nat := 118140960795 + 7100613 * 2 ^ 59
def prefixEnd_7100613 : Nat := 4983230072969 + 3 ^ 40 * 7100613 * 2
def baseEnd_7100613 : Nat := 3646027410563532552682381

theorem tailTrace_7100613 : CollatzResearch.WordTrace tailWord_7100613 prefixEnd_7100613 3646027410563532552682381 := by
  unfold tailWord_7100613
  simp only [CollatzResearch.WordTrace]
  refine ⟨258980632224699263998474493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172653754816466175998982995 258980632224699263998474493)
  ·
    refine ⟨97117737084262223999427935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258980632224699263998474493 97117737084262223999427935)
    ·
      refine ⟨145676605626393335999141903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97117737084262223999427935 145676605626393335999141903)
      ·
        refine ⟨218514908439590003998712855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145676605626393335999141903 218514908439590003998712855)
        ·
          refine ⟨327772362659385005998069283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218514908439590003998712855 327772362659385005998069283)
          ·
            refine ⟨491658543989077508997103925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327772362659385005998069283 491658543989077508997103925)
            ·
              refine ⟨46092988498976016468478493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491658543989077508997103925 46092988498976016468478493)
              ·
                refine ⟨17284870687116006175679435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46092988498976016468478493 17284870687116006175679435)
                ·
                  refine ⟨25927306030674009263519153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17284870687116006175679435 25927306030674009263519153)
                  ·
                    refine ⟨19445479523005506947639365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25927306030674009263519153 19445479523005506947639365)
                    ·
                      refine ⟨3646027410563532552682381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19445479523005506947639365 3646027410563532552682381)
                      ·
                        rfl

theorem cell23_7100613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_7100613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100613 prefixEnd_7100613 := by exact prefixLift 7100613
  have htrace : WordTrace (prefixWord ++ tailWord_7100613) baseStart_7100613 baseEnd_7100613 := by
    simpa [prefixWord, tailWord_7100613, baseEnd_7100613] using wordTrace_append hprefix tailTrace_7100613
  have hstable : (prefixWord ++ tailWord_7100613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100613).length < 2 ^ (prefixWord ++ tailWord_7100613).sum := by decide
  have hdescent : baseEnd_7100613 < baseStart_7100613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100623 : List Nat := [1, 1, 2, 1, 1, 3, 7, 7]
def baseStart_7100623 : Nat := 118140960795 + 7100623 * 2 ^ 59
def prefixEnd_7100623 : Nat := 4983230072969 + 3 ^ 40 * 7100623 * 2
def baseEnd_7100623 : Nat := 135038242421113981983605

theorem tailTrace_7100623 : CollatzResearch.WordTrace tailWord_7100623 prefixEnd_7100623 135038242421113981983605 := by
  unfold tailWord_7100623
  simp only [CollatzResearch.WordTrace]
  refine ⟨258980996954663035706338523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172653997969775357137559015 258980996954663035706338523)
  ·
    refine ⟨388471495431994553559507785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258980996954663035706338523 388471495431994553559507785)
    ·
      refine ⟨291353621573995915169630839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388471495431994553559507785 291353621573995915169630839)
      ·
        refine ⟨437030432360993872754446259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291353621573995915169630839 437030432360993872754446259)
        ·
          refine ⟨655545648541490809131669389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437030432360993872754446259 655545648541490809131669389)
          ·
            refine ⟨245829618203059053424376021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655545648541490809131669389 245829618203059053424376021)
            ·
              refine ⟨5761631676634196564633813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245829618203059053424376021 5761631676634196564633813)
              ·
                refine ⟨135038242421113981983605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5761631676634196564633813 135038242421113981983605)
                ·
                  rfl

theorem cell23_7100623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 7].length) (baseStart_7100623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100623 prefixEnd_7100623 := by exact prefixLift 7100623
  have htrace : WordTrace (prefixWord ++ tailWord_7100623) baseStart_7100623 baseEnd_7100623 := by
    simpa [prefixWord, tailWord_7100623, baseEnd_7100623] using wordTrace_append hprefix tailTrace_7100623
  have hstable : (prefixWord ++ tailWord_7100623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100623).length < 2 ^ (prefixWord ++ tailWord_7100623).sum := by decide
  have hdescent : baseEnd_7100623 < baseStart_7100623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100634 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_7100634 : Nat := 118140960795 + 7100634 * 2 ^ 59
def prefixEnd_7100634 : Nat := 4983230072969 + 3 ^ 40 * 7100634 * 2
def baseEnd_7100634 : Nat := 3646038193657276970519785

theorem tailTrace_7100634 : CollatzResearch.WordTrace tailWord_7100634 prefixEnd_7100634 3646038193657276970519785 := by
  unfold tailWord_7100634
  simp only [CollatzResearch.WordTrace]
  refine ⟨64745349539405796146247239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172654265438415456389992637 64745349539405796146247239)
  ·
    refine ⟨97118024309108694219370859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64745349539405796146247239 97118024309108694219370859)
    ·
      refine ⟨145677036463663041329056289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97118024309108694219370859 145677036463663041329056289)
      ·
        refine ⟨109257777347747280996792217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145677036463663041329056289 109257777347747280996792217)
        ·
          refine ⟨81943333010810460747594163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109257777347747280996792217 81943333010810460747594163)
          ·
            refine ⟨122914999516215691121391245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81943333010810460747594163 122914999516215691121391245)
            ·
              refine ⟨46093124818580884170521717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122914999516215691121391245 46093124818580884170521717)
              ·
                refine ⟨4321230451741957890986411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46093124818580884170521717 4321230451741957890986411)
                ·
                  refine ⟨6481845677612936836479617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321230451741957890986411 6481845677612936836479617)
                  ·
                    refine ⟨4861384258209702627359713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481845677612936836479617 4861384258209702627359713)
                    ·
                      refine ⟨3646038193657276970519785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861384258209702627359713 3646038193657276970519785)
                      ·
                        rfl

theorem cell23_7100634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_7100634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100634 prefixEnd_7100634 := by exact prefixLift 7100634
  have htrace : WordTrace (prefixWord ++ tailWord_7100634) baseStart_7100634 baseEnd_7100634 := by
    simpa [prefixWord, tailWord_7100634, baseEnd_7100634] using wordTrace_append hprefix tailTrace_7100634
  have hstable : (prefixWord ++ tailWord_7100634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100634).length < 2 ^ (prefixWord ++ tailWord_7100634).sum := by decide
  have hdescent : baseEnd_7100634 < baseStart_7100634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100693 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_7100693 : Nat := 118140960795 + 7100693 * 2 ^ 59
def prefixEnd_7100693 : Nat := 4983230072969 + 3 ^ 40 * 7100693 * 2
def baseEnd_7100693 : Nat := 3646068489015892239682013

theorem tailTrace_7100693 : CollatzResearch.WordTrace tailWord_7100693 prefixEnd_7100693 3646068489015892239682013 := by
  unfold tailWord_7100693
  simp only [CollatzResearch.WordTrace]
  refine ⟨258983550064409437661386733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172655700042939625107591155 258983550064409437661386733)
  ·
    refine ⟨97118831274153539123020025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258983550064409437661386733 97118831274153539123020025)
    ·
      refine ⟨72839123455615154342265019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97118831274153539123020025 72839123455615154342265019)
      ·
        refine ⟨109258685183422731513397529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72839123455615154342265019 109258685183422731513397529)
        ·
          refine ⟨81944013887567048635048147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109258685183422731513397529 81944013887567048635048147)
          ·
            refine ⟨122916020831350572952572221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81944013887567048635048147 122916020831350572952572221)
            ·
              refine ⟨46093507811756464857214583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122916020831350572952572221 46093507811756464857214583)
              ·
                refine ⟨69140261717634697285821875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46093507811756464857214583 69140261717634697285821875)
                ·
                  refine ⟨103710392576452045928732813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69140261717634697285821875 103710392576452045928732813)
                  ·
                    refine ⟨38891397216169517223274805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103710392576452045928732813 38891397216169517223274805)
                    ·
                      refine ⟨3646068489015892239682013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38891397216169517223274805 3646068489015892239682013)
                      ·
                        rfl

theorem cell23_7100693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_7100693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100693 prefixEnd_7100693 := by exact prefixLift 7100693
  have htrace : WordTrace (prefixWord ++ tailWord_7100693) baseStart_7100693 baseEnd_7100693 := by
    simpa [prefixWord, tailWord_7100693, baseEnd_7100693] using wordTrace_append hprefix tailTrace_7100693
  have hstable : (prefixWord ++ tailWord_7100693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100693).length < 2 ^ (prefixWord ++ tailWord_7100693).sum := by decide
  have hdescent : baseEnd_7100693 < baseStart_7100693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100707 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 4, 2, 2]
def baseStart_7100707 : Nat := 118140960795 + 7100707 * 2 ^ 59
def prefixEnd_7100707 : Nat := 4983230072969 + 3 ^ 40 * 7100707 * 2
def baseEnd_7100707 : Nat := 3646075677745055184906949

theorem tailTrace_7100707 : CollatzResearch.WordTrace tailWord_7100707 prefixEnd_7100707 3646075677745055184906949 := by
  unfold tailWord_7100707
  simp only [CollatzResearch.WordTrace]
  refine ⟨258984060686358718052396375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172656040457572478701597583 258984060686358718052396375)
  ·
    refine ⟨388476091029538077078594563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258984060686358718052396375 388476091029538077078594563)
    ·
      refine ⟨582714136544307115617891845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388476091029538077078594563 582714136544307115617891845)
      ·
        refine ⟨109258900602057584178354721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582714136544307115617891845 109258900602057584178354721)
        ·
          refine ⟨81944175451543188133766041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109258900602057584178354721 81944175451543188133766041)
          ·
            refine ⟨61458131588657391100324531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81944175451543188133766041 61458131588657391100324531)
            ·
              refine ⟨92187197382986086650486797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61458131588657391100324531 92187197382986086650486797)
              ·
                refine ⟨34570199018619782493932549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92187197382986086650486797 34570199018619782493932549)
                ·
                  refine ⟨6481912315991209217612353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34570199018619782493932549 6481912315991209217612353)
                  ·
                    refine ⟨4861434236993406913209265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481912315991209217612353 4861434236993406913209265)
                    ·
                      refine ⟨3646075677745055184906949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861434236993406913209265 3646075677745055184906949)
                      ·
                        rfl

theorem cell23_7100707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_7100707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100707 prefixEnd_7100707 := by exact prefixLift 7100707
  have htrace : WordTrace (prefixWord ++ tailWord_7100707) baseStart_7100707 baseEnd_7100707 := by
    simpa [prefixWord, tailWord_7100707, baseEnd_7100707] using wordTrace_append hprefix tailTrace_7100707
  have hstable : (prefixWord ++ tailWord_7100707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100707).length < 2 ^ (prefixWord ++ tailWord_7100707).sum := by decide
  have hdescent : baseEnd_7100707 < baseStart_7100707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100797 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_7100797 : Nat := 118140960795 + 7100797 * 2 ^ 59
def prefixEnd_7100797 : Nat := 4983230072969 + 3 ^ 40 * 7100797 * 2
def baseEnd_7100797 : Nat := 3646121891003959832781535

theorem tailTrace_7100797 : CollatzResearch.WordTrace tailWord_7100797 prefixEnd_7100797 3646121891003959832781535 := by
  unfold tailWord_7100797
  simp only [CollatzResearch.WordTrace]
  refine ⟨258987343256032663423172645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172658228837355108948781763 258987343256032663423172645)
  ·
    refine ⟨48560126860506124391844871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258987343256032663423172645 48560126860506124391844871)
    ·
      refine ⟨72840190290759186587767307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48560126860506124391844871 72840190290759186587767307)
      ·
        refine ⟨109260285436138779881650961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72840190290759186587767307 109260285436138779881650961)
        ·
          refine ⟨81945214077104084911238221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109260285436138779881650961 81945214077104084911238221)
          ·
            refine ⟨30729455278914031841714333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81945214077104084911238221 30729455278914031841714333)
            ·
              refine ⟨11523545729592761940642875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30729455278914031841714333 11523545729592761940642875)
              ·
                refine ⟨17285318594389142910964313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11523545729592761940642875 17285318594389142910964313)
                ·
                  refine ⟨12963988945791857183223235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17285318594389142910964313 12963988945791857183223235)
                  ·
                    refine ⟨19445983418687785774834853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12963988945791857183223235 19445983418687785774834853)
                    ·
                      refine ⟨3646121891003959832781535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19445983418687785774834853 3646121891003959832781535)
                      ·
                        rfl

theorem cell23_7100797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_7100797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100797 prefixEnd_7100797 := by exact prefixLift 7100797
  have htrace : WordTrace (prefixWord ++ tailWord_7100797) baseStart_7100797 baseEnd_7100797 := by
    simpa [prefixWord, tailWord_7100797, baseEnd_7100797] using wordTrace_append hprefix tailTrace_7100797
  have hstable : (prefixWord ++ tailWord_7100797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100797).length < 2 ^ (prefixWord ++ tailWord_7100797).sum := by decide
  have hdescent : baseEnd_7100797 < baseStart_7100797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100814 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7100814 : Nat := 118140960795 + 7100814 * 2 ^ 59
def prefixEnd_7100814 : Nat := 4983230072969 + 3 ^ 40 * 7100814 * 2
def baseEnd_7100814 : Nat := 3646130620175086266268957

theorem tailTrace_7100814 : CollatzResearch.WordTrace tailWord_7100814 prefixEnd_7100814 3646130620175086266268957 := by
  unfold tailWord_7100814
  simp only [CollatzResearch.WordTrace]
  refine ⟨32373495412121384415817687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172658642197980716884360997 32373495412121384415817687)
  ·
    refine ⟨48560243118182076623726531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32373495412121384415817687 48560243118182076623726531)
    ·
      refine ⟨72840364677273114935589797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48560243118182076623726531 72840364677273114935589797)
      ·
        refine ⟨13657568376988709050423087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72840364677273114935589797 13657568376988709050423087)
        ·
          refine ⟨20486352565483063575634631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657568376988709050423087 20486352565483063575634631)
          ·
            refine ⟨30729528848224595363451947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20486352565483063575634631 30729528848224595363451947)
            ·
              refine ⟨46094293272336893045177921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30729528848224595363451947 46094293272336893045177921)
              ·
                refine ⟨34570719954252669783883441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46094293272336893045177921 34570719954252669783883441)
                ·
                  refine ⟨25928039965689502337912581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34570719954252669783883441 25928039965689502337912581)
                  ·
                    refine ⟨4861507493566781688358609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25928039965689502337912581 4861507493566781688358609)
                    ·
                      refine ⟨3646130620175086266268957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861507493566781688358609 3646130620175086266268957)
                      ·
                        rfl

theorem cell23_7100814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7100814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100814 prefixEnd_7100814 := by exact prefixLift 7100814
  have htrace : WordTrace (prefixWord ++ tailWord_7100814) baseStart_7100814 baseEnd_7100814 := by
    simpa [prefixWord, tailWord_7100814, baseEnd_7100814] using wordTrace_append hprefix tailTrace_7100814
  have hstable : (prefixWord ++ tailWord_7100814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100814).length < 2 ^ (prefixWord ++ tailWord_7100814).sum := by decide
  have hdescent : baseEnd_7100814 < baseStart_7100814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100824 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_7100824 : Nat := 118140960795 + 7100824 * 2 ^ 59
def prefixEnd_7100824 : Nat := 4983230072969 + 3 ^ 40 * 7100824 * 2
def baseEnd_7100824 : Nat := 1215378584993877075714637

theorem tailTrace_7100824 : CollatzResearch.WordTrace tailWord_7100824 prefixEnd_7100824 1215378584993877075714637 := by
  unfold tailWord_7100824
  simp only [CollatzResearch.WordTrace]
  refine ⟨129494164013467423517202763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172658885351289898022937017 129494164013467423517202763)
  ·
    refine ⟨194241246020201135275804145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129494164013467423517202763 194241246020201135275804145)
    ·
      refine ⟨145680934515150851456853109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194241246020201135275804145 145680934515150851456853109)
      ·
        refine ⟨13657587610795392324079979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145680934515150851456853109 13657587610795392324079979)
        ·
          refine ⟨20486381416193088486119969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657587610795392324079979 20486381416193088486119969)
          ·
            refine ⟨15364786062144816364589977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20486381416193088486119969 15364786062144816364589977)
            ·
              refine ⟨11523589546608612273442483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15364786062144816364589977 11523589546608612273442483)
              ·
                refine ⟨17285384319912918410163725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11523589546608612273442483 17285384319912918410163725)
                ·
                  refine ⟨6482019119967344403811397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17285384319912918410163725 6482019119967344403811397)
                  ·
                    refine ⟨1215378584993877075714637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482019119967344403811397 1215378584993877075714637)
                    ·
                      rfl

theorem cell23_7100824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_7100824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100824 prefixEnd_7100824 := by exact prefixLift 7100824
  have htrace : WordTrace (prefixWord ++ tailWord_7100824) baseStart_7100824 baseEnd_7100824 := by
    simpa [prefixWord, tailWord_7100824, baseEnd_7100824] using wordTrace_append hprefix tailTrace_7100824
  have hstable : (prefixWord ++ tailWord_7100824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100824).length < 2 ^ (prefixWord ++ tailWord_7100824).sum := by decide
  have hdescent : baseEnd_7100824 < baseStart_7100824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100837 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 6]
def baseStart_7100837 : Nat := 118140960795 + 7100837 * 2 ^ 59
def prefixEnd_7100837 : Nat := 4983230072969 + 3 ^ 40 * 7100837 * 2
def baseEnd_7100837 : Nat := 405126936692237741809039

theorem tailTrace_7100837 : CollatzResearch.WordTrace tailWord_7100837 prefixEnd_7100837 405126936692237741809039 := by
  unfold tailWord_7100837
  simp only [CollatzResearch.WordTrace]
  refine ⟨258988802175887750254628765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172659201450591833503085843 258988802175887750254628765)
  ·
    refine ⟨97120800815957906345485787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258988802175887750254628765 97120800815957906345485787)
    ·
      refine ⟨145681201223936859518228681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97120800815957906345485787 145681201223936859518228681)
      ·
        refine ⟨109260900917952644638671511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145681201223936859518228681 109260900917952644638671511)
        ·
          refine ⟨163891351376928966958007267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109260900917952644638671511 163891351376928966958007267)
          ·
            refine ⟨245837027065393450437010901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163891351376928966958007267 245837027065393450437010901)
            ·
              refine ⟨5761805321845158994617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245837027065393450437010901 5761805321845158994617443)
              ·
                refine ⟨8642707982767738491926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761805321845158994617443 8642707982767738491926165)
                ·
                  refine ⟨405126936692237741809039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8642707982767738491926165 405126936692237741809039)
                  ·
                    rfl

theorem cell23_7100837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_7100837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100837 prefixEnd_7100837 := by exact prefixLift 7100837
  have htrace : WordTrace (prefixWord ++ tailWord_7100837) baseStart_7100837 baseEnd_7100837 := by
    simpa [prefixWord, tailWord_7100837, baseEnd_7100837] using wordTrace_append hprefix tailTrace_7100837
  have hstable : (prefixWord ++ tailWord_7100837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100837).length < 2 ^ (prefixWord ++ tailWord_7100837).sum := by decide
  have hdescent : baseEnd_7100837 < baseStart_7100837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100874 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_7100874 : Nat := 118140960795 + 7100874 * 2 ^ 59
def prefixEnd_7100874 : Nat := 4983230072969 + 3 ^ 40 * 7100874 * 2
def baseEnd_7100874 : Nat := 3646161429014356031518681

theorem tailTrace_7100874 : CollatzResearch.WordTrace tailWord_7100874 prefixEnd_7100874 3646161429014356031518681 := by
  unfold tailWord_7100874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64747537919188426393431419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172660101117835803715817117 64747537919188426393431419)
  ·
    refine ⟨97121306878782639590147129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64747537919188426393431419 97121306878782639590147129)
    ·
      refine ⟨72840980159086979692610347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97121306878782639590147129 72840980159086979692610347)
      ·
        refine ⟨109261470238630469538915521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72840980159086979692610347 109261470238630469538915521)
        ·
          refine ⟨81946102678972852154186641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109261470238630469538915521 81946102678972852154186641)
          ·
            refine ⟨61459577009229639115639981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81946102678972852154186641 61459577009229639115639981)
            ·
              refine ⟨23047341378461114668364993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61459577009229639115639981 23047341378461114668364993)
              ·
                refine ⟨17285506033845836001273745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23047341378461114668364993 17285506033845836001273745)
                ·
                  refine ⟨12964129525384377000955309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17285506033845836001273745 12964129525384377000955309)
                  ·
                    refine ⟨4861548572019141375358241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12964129525384377000955309 4861548572019141375358241)
                    ·
                      refine ⟨3646161429014356031518681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861548572019141375358241 3646161429014356031518681)
                      ·
                        rfl

theorem cell23_7100874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_7100874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100874 prefixEnd_7100874 := by exact prefixLift 7100874
  have htrace : WordTrace (prefixWord ++ tailWord_7100874) baseStart_7100874 baseEnd_7100874 := by
    simpa [prefixWord, tailWord_7100874, baseEnd_7100874] using wordTrace_append hprefix tailTrace_7100874
  have hstable : (prefixWord ++ tailWord_7100874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100874).length < 2 ^ (prefixWord ++ tailWord_7100874).sum := by decide
  have hdescent : baseEnd_7100874 < baseStart_7100874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100901 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_7100901 : Nat := 118140960795 + 7100901 * 2 ^ 59
def prefixEnd_7100901 : Nat := 4983230072969 + 3 ^ 40 * 7100901 * 2
def baseEnd_7100901 : Nat := 1215391764330675808627019

theorem tailTrace_7100901 : CollatzResearch.WordTrace tailWord_7100901 prefixEnd_7100901 1215391764330675808627019 := by
  unfold tailWord_7100901
  simp only [CollatzResearch.WordTrace]
  refine ⟨258991136447655889184958557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172660757631770592789972371 258991136447655889184958557)
  ·
    refine ⟨97121676167870958444359459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258991136447655889184958557 97121676167870958444359459)
    ·
      refine ⟨145682514251806437666539189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97121676167870958444359459 145682514251806437666539189)
      ·
        refine ⟨13657735711106853531238049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145682514251806437666539189 13657735711106853531238049)
        ·
          refine ⟨10243301783330140148428537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13657735711106853531238049 10243301783330140148428537)
          ·
            refine ⟨7682476337497605111321403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243301783330140148428537 7682476337497605111321403)
            ·
              refine ⟨11523714506246407666982105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682476337497605111321403 11523714506246407666982105)
              ·
                refine ⟨8642785879684805750236579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523714506246407666982105 8642785879684805750236579)
                ·
                  refine ⟨12964178819527208625354869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8642785879684805750236579 12964178819527208625354869)
                  ·
                    refine ⟨1215391764330675808627019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12964178819527208625354869 1215391764330675808627019)
                    ·
                      rfl

theorem cell23_7100901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_7100901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100901 prefixEnd_7100901 := by exact prefixLift 7100901
  have htrace : WordTrace (prefixWord ++ tailWord_7100901) baseStart_7100901 baseEnd_7100901 := by
    simpa [prefixWord, tailWord_7100901, baseEnd_7100901] using wordTrace_append hprefix tailTrace_7100901
  have hstable : (prefixWord ++ tailWord_7100901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100901).length < 2 ^ (prefixWord ++ tailWord_7100901).sum := by decide
  have hdescent : baseEnd_7100901 < baseStart_7100901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100904 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7100904 : Nat := 118140960795 + 7100904 * 2 ^ 59
def prefixEnd_7100904 : Nat := 4983230072969 + 3 ^ 40 * 7100904 * 2
def baseEnd_7100904 : Nat := 3646176833433990914143543

theorem tailTrace_7100904 : CollatzResearch.WordTrace tailWord_7100904 prefixEnd_7100904 3646176833433990914143543 := by
  unfold tailWord_7100904
  simp only [CollatzResearch.WordTrace]
  refine ⟨129495622933322510348658883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172660830577763347131545177 129495622933322510348658883)
  ·
    refine ⟨194243434399983765522988325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129495622933322510348658883 194243434399983765522988325)
    ·
      refine ⟨36420643949996956035560311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194243434399983765522988325 36420643949996956035560311)
      ·
        refine ⟨54630965924995434053340467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36420643949996956035560311 54630965924995434053340467)
        ·
          refine ⟨81946448887493151080010701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54630965924995434053340467 81946448887493151080010701)
          ·
            refine ⟨30729918332809931655004013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81946448887493151080010701 30729918332809931655004013)
            ·
              refine ⟨11523719374803724370626505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30729918332809931655004013 11523719374803724370626505)
              ·
                refine ⟨8642789531102793277969879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523719374803724370626505 8642789531102793277969879)
                ·
                  refine ⟨12964184296654189916954819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8642789531102793277969879 12964184296654189916954819)
                  ·
                    refine ⟨19446276444981284875432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12964184296654189916954819 19446276444981284875432229)
                    ·
                      refine ⟨3646176833433990914143543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19446276444981284875432229 3646176833433990914143543)
                      ·
                        rfl

theorem cell23_7100904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7100904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100904 prefixEnd_7100904 := by exact prefixLift 7100904
  have htrace : WordTrace (prefixWord ++ tailWord_7100904) baseStart_7100904 baseEnd_7100904 := by
    simpa [prefixWord, tailWord_7100904, baseEnd_7100904] using wordTrace_append hprefix tailTrace_7100904
  have hstable : (prefixWord ++ tailWord_7100904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100904).length < 2 ^ (prefixWord ++ tailWord_7100904).sum := by decide
  have hdescent : baseEnd_7100904 < baseStart_7100904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100907 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3]
def baseStart_7100907 : Nat := 118140960795 + 7100907 * 2 ^ 59
def prefixEnd_7100907 : Nat := 4983230072969 + 3 ^ 40 * 7100907 * 2
def baseEnd_7100907 : Nat := 3646178373875954402406029

theorem tailTrace_7100907 : CollatzResearch.WordTrace tailWord_7100907 prefixEnd_7100907 3646178373875954402406029 := by
  unfold tailWord_7100907
  simp only [CollatzResearch.WordTrace]
  refine ⟨258991355285634152209676975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172660903523756101473117983 258991355285634152209676975)
  ·
    refine ⟨388487032928451228314515463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258991355285634152209676975 388487032928451228314515463)
    ·
      refine ⟨582730549392676842471773195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388487032928451228314515463 582730549392676842471773195)
      ·
        refine ⟨874095824089015263707659793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582730549392676842471773195 874095824089015263707659793)
        ·
          refine ⟨655571868066761447780744845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874095824089015263707659793 655571868066761447780744845)
          ·
            refine ⟨245839450525035542917779317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655571868066761447780744845 245839450525035542917779317)
            ·
              refine ⟨23047448486722082148541811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245839450525035542917779317 23047448486722082148541811)
              ·
                refine ⟨34571172730083123222812717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23047448486722082148541811 34571172730083123222812717)
                ·
                  refine ⟨12964189773781171208554769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34571172730083123222812717 12964189773781171208554769)
                  ·
                    refine ⟨9723142330335878406416077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12964189773781171208554769 9723142330335878406416077)
                    ·
                      refine ⟨3646178373875954402406029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723142330335878406416077 3646178373875954402406029)
                      ·
                        rfl

theorem cell23_7100907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].length) (baseStart_7100907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100907 prefixEnd_7100907 := by exact prefixLift 7100907
  have htrace : WordTrace (prefixWord ++ tailWord_7100907) baseStart_7100907 baseEnd_7100907 := by
    simpa [prefixWord, tailWord_7100907, baseEnd_7100907] using wordTrace_append hprefix tailTrace_7100907
  have hstable : (prefixWord ++ tailWord_7100907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100907).length < 2 ^ (prefixWord ++ tailWord_7100907).sum := by decide
  have hdescent : baseEnd_7100907 < baseStart_7100907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100914 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_7100914 : Nat := 118140960795 + 7100914 * 2 ^ 59
def prefixEnd_7100914 : Nat := 4983230072969 + 3 ^ 40 * 7100914 * 2
def baseEnd_7100914 : Nat := 1215393989413511958339499

theorem tailTrace_7100914 : CollatzResearch.WordTrace tailWord_7100914 prefixEnd_7100914 1215393989413511958339499 := by
  unfold tailWord_7100914
  simp only [CollatzResearch.WordTrace]
  refine ⟨64747902649152198101295449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172661073731072528270121197 64747902649152198101295449)
  ·
    refine ⟨48560926986864148575971587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64747902649152198101295449 48560926986864148575971587)
    ·
      refine ⟨72841390480296222863957381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48560926986864148575971587 72841390480296222863957381)
      ·
        refine ⟨13657760715055541786992009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72841390480296222863957381 13657760715055541786992009)
        ·
          refine ⟨10243320536291656340244007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13657760715055541786992009 10243320536291656340244007)
          ·
            refine ⟨15364980804437484510366011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10243320536291656340244007 15364980804437484510366011)
            ·
              refine ⟨23047471206656226765549017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364980804437484510366011 23047471206656226765549017)
              ·
                refine ⟨17285603404992170074161763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23047471206656226765549017 17285603404992170074161763)
                ·
                  refine ⟨25928405107488255111242645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17285603404992170074161763 25928405107488255111242645)
                  ·
                    refine ⟨1215393989413511958339499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25928405107488255111242645 1215393989413511958339499)
                    ·
                      rfl

theorem cell23_7100914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_7100914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100914 prefixEnd_7100914 := by exact prefixLift 7100914
  have htrace : WordTrace (prefixWord ++ tailWord_7100914) baseStart_7100914 baseEnd_7100914 := by
    simpa [prefixWord, tailWord_7100914, baseEnd_7100914] using wordTrace_append hprefix tailTrace_7100914
  have hstable : (prefixWord ++ tailWord_7100914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100914).length < 2 ^ (prefixWord ++ tailWord_7100914).sum := by decide
  have hdescent : baseEnd_7100914 < baseStart_7100914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100938 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_7100938 : Nat := 118140960795 + 7100938 * 2 ^ 59
def prefixEnd_7100938 : Nat := 4983230072969 + 3 ^ 40 * 7100938 * 2
def baseEnd_7100938 : Nat := 3646194291776243781118387

theorem tailTrace_7100938 : CollatzResearch.WordTrace tailWord_7100938 prefixEnd_7100938 3646194291776243781118387 := by
  unfold tailWord_7100938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64748121487130461126013867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172661657299014563002703645 64748121487130461126013867)
  ·
    refine ⟨97122182230695691689020801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64748121487130461126013867 97122182230695691689020801)
    ·
      refine ⟨72841636673021768766765601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97122182230695691689020801 72841636673021768766765601)
      ·
        refine ⟨54631227504766326575074201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72841636673021768766765601 54631227504766326575074201)
        ·
          refine ⟨40973420628574744931305651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54631227504766326575074201 40973420628574744931305651)
          ·
            refine ⟨61460130942862117396958477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40973420628574744931305651 61460130942862117396958477)
            ·
              refine ⟨23047549103573294023859429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61460130942862117396958477 23047549103573294023859429)
              ·
                refine ⟨4321415456919992629473643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23047549103573294023859429 4321415456919992629473643)
                ·
                  refine ⟨6482123185379988944210465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321415456919992629473643 6482123185379988944210465)
                  ·
                    refine ⟨4861592389034991708157849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482123185379988944210465 4861592389034991708157849)
                    ·
                      refine ⟨3646194291776243781118387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861592389034991708157849 3646194291776243781118387)
                      ·
                        rfl

theorem cell23_7100938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_7100938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100938 prefixEnd_7100938 := by exact prefixLift 7100938
  have htrace : WordTrace (prefixWord ++ tailWord_7100938) baseStart_7100938 baseEnd_7100938 := by
    simpa [prefixWord, tailWord_7100938, baseEnd_7100938] using wordTrace_append hprefix tailTrace_7100938
  have hstable : (prefixWord ++ tailWord_7100938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100938).length < 2 ^ (prefixWord ++ tailWord_7100938).sum := by decide
  have hdescent : baseEnd_7100938 < baseStart_7100938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100951 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7100951 : Nat := 118140960795 + 7100951 * 2 ^ 59
def prefixEnd_7100951 : Nat := 4983230072969 + 3 ^ 40 * 7100951 * 2
def baseEnd_7100951 : Nat := 3646200967024752230255827

theorem tailTrace_7100951 : CollatzResearch.WordTrace tailWord_7100951 prefixEnd_7100951 3646200967024752230255827 := by
  unfold tailWord_7100951
  simp only [CollatzResearch.WordTrace]
  refine ⟨258992960097474747724278707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172661973398316498482852471 258992960097474747724278707)
  ·
    refine ⟨388489440146212121586418061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258992960097474747724278707 388489440146212121586418061)
    ·
      refine ⟨145683540054829545594906773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388489440146212121586418061 145683540054829545594906773)
      ·
        refine ⟨6828915940070134949761255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145683540054829545594906773 6828915940070134949761255)
        ·
          refine ⟨10243373910105202424641883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828915940070134949761255 10243373910105202424641883)
          ·
            refine ⟨15365060865157803636962825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10243373910105202424641883 15365060865157803636962825)
            ·
              refine ⟨11523795648868352727722119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15365060865157803636962825 11523795648868352727722119)
              ·
                refine ⟨17285693473302529091583179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11523795648868352727722119 17285693473302529091583179)
                ·
                  refine ⟨25928540209953793637374769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17285693473302529091583179 25928540209953793637374769)
                  ·
                    refine ⟨19446405157465345228031077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25928540209953793637374769 19446405157465345228031077)
                    ·
                      refine ⟨3646200967024752230255827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19446405157465345228031077 3646200967024752230255827)
                      ·
                        rfl

theorem cell23_7100951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7100951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100951 prefixEnd_7100951 := by exact prefixLift 7100951
  have htrace : WordTrace (prefixWord ++ tailWord_7100951) baseStart_7100951 baseEnd_7100951 := by
    simpa [prefixWord, tailWord_7100951, baseEnd_7100951] using wordTrace_append hprefix tailTrace_7100951
  have hstable : (prefixWord ++ tailWord_7100951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100951).length < 2 ^ (prefixWord ++ tailWord_7100951).sum := by decide
  have hdescent : baseEnd_7100951 < baseStart_7100951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100981 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_7100981 : Nat := 118140960795 + 7100981 * 2 ^ 59
def prefixEnd_7100981 : Nat := 4983230072969 + 3 ^ 40 * 7100981 * 2
def baseEnd_7100981 : Nat := 3646216371444387112880689

theorem tailTrace_7100981 : CollatzResearch.WordTrace tailWord_7100981 prefixEnd_7100981 3646216371444387112880689 := by
  unfold tailWord_7100981
  simp only [CollatzResearch.WordTrace]
  refine ⟨258994054287366062847870797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172662702858244041898580531 258994054287366062847870797)
  ·
    refine ⟨97122770357762273567951549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 258994054287366062847870797 97122770357762273567951549)
    ·
      refine ⟨36421038884160852587981831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97122770357762273567951549 36421038884160852587981831)
      ·
        refine ⟨54631558326241278881972747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36421038884160852587981831 54631558326241278881972747)
        ·
          refine ⟨81947337489361918322959121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54631558326241278881972747 81947337489361918322959121)
          ·
            refine ⟨61460503117021438742219341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81947337489361918322959121 61460503117021438742219341)
            ·
              refine ⟨23047688668883039528332253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61460503117021438742219341 23047688668883039528332253)
              ·
                refine ⟨8642883250831139823124595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23047688668883039528332253 8642883250831139823124595)
                ·
                  refine ⟨12964324876246709734686893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8642883250831139823124595 12964324876246709734686893)
                  ·
                    refine ⟨4861621828592516150507585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12964324876246709734686893 4861621828592516150507585)
                    ·
                      refine ⟨3646216371444387112880689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861621828592516150507585 3646216371444387112880689)
                      ·
                        rfl

theorem cell23_7100981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_7100981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100981 prefixEnd_7100981 := by exact prefixLift 7100981
  have htrace : WordTrace (prefixWord ++ tailWord_7100981) baseStart_7100981 baseEnd_7100981 := by
    simpa [prefixWord, tailWord_7100981, baseEnd_7100981] using wordTrace_append hprefix tailTrace_7100981
  have hstable : (prefixWord ++ tailWord_7100981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100981).length < 2 ^ (prefixWord ++ tailWord_7100981).sum := by decide
  have hdescent : baseEnd_7100981 < baseStart_7100981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7100988 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_7100988 : Nat := 118140960795 + 7100988 * 2 ^ 59
def prefixEnd_7100988 : Nat := 4983230072969 + 3 ^ 40 * 7100988 * 2
def baseEnd_7100988 : Nat := 3646219965808968585493157

theorem tailTrace_7100988 : CollatzResearch.WordTrace tailWord_7100988 prefixEnd_7100988 3646219965808968585493157 := by
  unfold tailWord_7100988
  simp only [CollatzResearch.WordTrace]
  refine ⟨129497154799170351521687809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172662873065560468695583745 129497154799170351521687809)
  ·
    refine ⟨97122866099377763641265857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129497154799170351521687809 97122866099377763641265857)
    ·
      refine ⟨72842149574533322730949393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97122866099377763641265857 72842149574533322730949393)
      ·
        refine ⟨54631612180899992048212045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72842149574533322730949393 54631612180899992048212045)
        ·
          refine ⟨20486854567837497018079517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54631612180899992048212045 20486854567837497018079517)
          ·
            refine ⟨7682570462939061381779819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20486854567837497018079517 7682570462939061381779819)
            ·
              refine ⟨11523855694408592072669729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682570462939061381779819 11523855694408592072669729)
              ·
                refine ⟨8642891770806444054502297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523855694408592072669729 8642891770806444054502297)
                ·
                  refine ⟨6482168828104833040876723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642891770806444054502297 6482168828104833040876723)
                  ·
                    refine ⟨9723253242157249561315085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482168828104833040876723 9723253242157249561315085)
                    ·
                      refine ⟨3646219965808968585493157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723253242157249561315085 3646219965808968585493157)
                      ·
                        rfl

theorem cell23_7100988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_7100988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7100988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7100988 prefixEnd_7100988 := by exact prefixLift 7100988
  have htrace : WordTrace (prefixWord ++ tailWord_7100988) baseStart_7100988 baseEnd_7100988 := by
    simpa [prefixWord, tailWord_7100988, baseEnd_7100988] using wordTrace_append hprefix tailTrace_7100988
  have hstable : (prefixWord ++ tailWord_7100988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7100988).length < 2 ^ (prefixWord ++ tailWord_7100988).sum := by decide
  have hdescent : baseEnd_7100988 < baseStart_7100988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7100988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101005 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7101005 : Nat := 118140960795 + 7101005 * 2 ^ 59
def prefixEnd_7101005 : Nat := 4983230072969 + 3 ^ 40 * 7101005 * 2
def baseEnd_7101005 : Nat := 3646228694980095018980579

theorem tailTrace_7101005 : CollatzResearch.WordTrace tailWord_7101005 prefixEnd_7101005 3646228694980095018980579 := by
  unfold tailWord_7101005
  simp only [CollatzResearch.WordTrace]
  refine ⟨258994929639279114946744469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172663286426186076631162979 258994929639279114946744469)
  ·
    refine ⟨12140387326841208513128647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 258994929639279114946744469 12140387326841208513128647)
    ·
      refine ⟨18210580990261812769692971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12140387326841208513128647 18210580990261812769692971)
      ·
        refine ⟨27315871485392719154539457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18210580990261812769692971 27315871485392719154539457)
        ·
          refine ⟨20486903614044539365904593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27315871485392719154539457 20486903614044539365904593)
          ·
            refine ⟨15365177710533404524428445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20486903614044539365904593 15365177710533404524428445)
            ·
              refine ⟨5761941641450026696660667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15365177710533404524428445 5761941641450026696660667)
              ·
                refine ⟨8642912462175040044991001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761941641450026696660667 8642912462175040044991001)
                ·
                  refine ⟨6482184346631280033743251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642912462175040044991001 6482184346631280033743251)
                  ·
                    refine ⟨9723276519946920050614877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482184346631280033743251 9723276519946920050614877)
                    ·
                      refine ⟨3646228694980095018980579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723276519946920050614877 3646228694980095018980579)
                      ·
                        rfl

theorem cell23_7101005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7101005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101005 prefixEnd_7101005 := by exact prefixLift 7101005
  have htrace : WordTrace (prefixWord ++ tailWord_7101005) baseStart_7101005 baseEnd_7101005 := by
    simpa [prefixWord, tailWord_7101005, baseEnd_7101005] using wordTrace_append hprefix tailTrace_7101005
  have hstable : (prefixWord ++ tailWord_7101005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101005).length < 2 ^ (prefixWord ++ tailWord_7101005).sum := by decide
  have hdescent : baseEnd_7101005 < baseStart_7101005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101007 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_7101007 : Nat := 118140960795 + 7101007 * 2 ^ 59
def prefixEnd_7101007 : Nat := 4983230072969 + 3 ^ 40 * 7101007 * 2
def baseEnd_7101007 : Nat := 3646229721941404011155569

theorem tailTrace_7101007 : CollatzResearch.WordTrace tailWord_7101007 prefixEnd_7101007 3646229721941404011155569 := by
  unfold tailWord_7101007
  simp only [CollatzResearch.WordTrace]
  refine ⟨258995002585271869288317275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172663335056847912858878183 258995002585271869288317275)
  ·
    refine ⟨388492503877907803932475913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258995002585271869288317275 388492503877907803932475913)
    ·
      refine ⟨291369377908430852949356935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388492503877907803932475913 291369377908430852949356935)
      ·
        refine ⟨437054066862646279424035403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291369377908430852949356935 437054066862646279424035403)
        ·
          refine ⟨655581100293969419136053105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437054066862646279424035403 655581100293969419136053105)
          ·
            refine ⟨491685825220477064352039829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655581100293969419136053105 491685825220477064352039829)
            ·
              refine ⟨23047773057209862391501867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 491685825220477064352039829 23047773057209862391501867)
              ·
                refine ⟨34571659585814793587252801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23047773057209862391501867 34571659585814793587252801)
                ·
                  refine ⟨25928744689361095190439601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34571659585814793587252801 25928744689361095190439601)
                  ·
                    refine ⟨19446558517020821392829701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25928744689361095190439601 19446558517020821392829701)
                    ·
                      refine ⟨3646229721941404011155569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19446558517020821392829701 3646229721941404011155569)
                      ·
                        rfl

theorem cell23_7101007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_7101007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101007 prefixEnd_7101007 := by exact prefixLift 7101007
  have htrace : WordTrace (prefixWord ++ tailWord_7101007) baseStart_7101007 baseEnd_7101007 := by
    simpa [prefixWord, tailWord_7101007, baseEnd_7101007] using wordTrace_append hprefix tailTrace_7101007
  have hstable : (prefixWord ++ tailWord_7101007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101007).length < 2 ^ (prefixWord ++ tailWord_7101007).sum := by decide
  have hdescent : baseEnd_7101007 < baseStart_7101007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101047 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 4, 5]
def baseStart_7101047 : Nat := 118140960795 + 7101047 * 2 ^ 59
def prefixEnd_7101047 : Nat := 4983230072969 + 3 ^ 40 * 7101047 * 2
def baseEnd_7101047 : Nat := 1215416753722527951551795

theorem tailTrace_7101047 : CollatzResearch.WordTrace tailWord_7101047 prefixEnd_7101047 1215416753722527951551795 := by
  unfold tailWord_7101047
  simp only [CollatzResearch.WordTrace]
  refine ⟨258996461505126956119773395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172664307670084637413182263 258996461505126956119773395)
  ·
    refine ⟨388494692257690434179660093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258996461505126956119773395 388494692257690434179660093)
    ·
      refine ⟨145685509596633912817372535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388494692257690434179660093 145685509596633912817372535)
      ·
        refine ⟨218528264394950869226058803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145685509596633912817372535 218528264394950869226058803)
        ·
          refine ⟨327792396592426303839088205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218528264394950869226058803 327792396592426303839088205)
          ·
            refine ⟨122922148722159863939658077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327792396592426303839088205 122922148722159863939658077)
            ·
              refine ⟨46095805770809948977371779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122922148722159863939658077 46095805770809948977371779)
              ·
                refine ⟨69143708656214923466057669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46095805770809948977371779 69143708656214923466057669)
                ·
                  refine ⟨12964445373040298149885813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69143708656214923466057669 12964445373040298149885813)
                  ·
                    refine ⟨1215416753722527951551795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12964445373040298149885813 1215416753722527951551795)
                    ·
                      rfl

theorem cell23_7101047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_7101047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101047 prefixEnd_7101047 := by exact prefixLift 7101047
  have htrace : WordTrace (prefixWord ++ tailWord_7101047) baseStart_7101047 baseEnd_7101047 := by
    simpa [prefixWord, tailWord_7101047, baseEnd_7101047] using wordTrace_append hprefix tailTrace_7101047
  have hstable : (prefixWord ++ tailWord_7101047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101047).length < 2 ^ (prefixWord ++ tailWord_7101047).sum := by decide
  have hdescent : baseEnd_7101047 < baseStart_7101047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101067 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_7101067 : Nat := 118140960795 + 7101067 * 2 ^ 59
def prefixEnd_7101067 : Nat := 4983230072969 + 3 ^ 40 * 7101067 * 2
def baseEnd_7101067 : Nat := 3646260530780673776405293

theorem tailTrace_7101067 : CollatzResearch.WordTrace tailWord_7101067 prefixEnd_7101067 3646260530780673776405293 := by
  unfold tailWord_7101067
  simp only [CollatzResearch.WordTrace]
  refine ⟨258997190965054499535501455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172664793976702999690334303 258997190965054499535501455)
  ·
    refine ⟨388495786447581749303252183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258997190965054499535501455 388495786447581749303252183)
    ·
      refine ⟨582743679671372623954878275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388495786447581749303252183 582743679671372623954878275)
      ·
        refine ⟨874115519507058935932317413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582743679671372623954878275 874115519507058935932317413)
        ·
          refine ⟨163896659907573550487309515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 874115519507058935932317413 163896659907573550487309515)
          ·
            refine ⟨245844989861360325730964273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163896659907573550487309515 245844989861360325730964273)
            ·
              refine ⟨184383742396020244298223205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245844989861360325730964273 184383742396020244298223205)
              ·
                refine ⟨34571951699253795805916851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184383742396020244298223205 34571951699253795805916851)
                ·
                  refine ⟨51857927548880693708875277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34571951699253795805916851 51857927548880693708875277)
                  ·
                    refine ⟨19446722830830260140828229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51857927548880693708875277 19446722830830260140828229)
                    ·
                      refine ⟨3646260530780673776405293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19446722830830260140828229 3646260530780673776405293)
                      ·
                        rfl

theorem cell23_7101067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_7101067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101067 prefixEnd_7101067 := by exact prefixLift 7101067
  have htrace : WordTrace (prefixWord ++ tailWord_7101067) baseStart_7101067 baseEnd_7101067 := by
    simpa [prefixWord, tailWord_7101067, baseEnd_7101067] using wordTrace_append hprefix tailTrace_7101067
  have hstable : (prefixWord ++ tailWord_7101067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101067).length < 2 ^ (prefixWord ++ tailWord_7101067).sum := by decide
  have hdescent : baseEnd_7101067 < baseStart_7101067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101101 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7101101 : Nat := 118140960795 + 7101101 * 2 ^ 59
def prefixEnd_7101101 : Nat := 4983230072969 + 3 ^ 40 * 7101101 * 2
def baseEnd_7101101 : Nat := 3646277989122926643380137

theorem tailTrace_7101101 : CollatzResearch.WordTrace tailWord_7101101 prefixEnd_7101101 3646277989122926643380137 := by
  unfold tailWord_7101101
  simp only [CollatzResearch.WordTrace]
  refine ⟨258998431046931323342239157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172665620697954215561492771 258998431046931323342239157)
  ·
    refine ⟨24281102910649811563334921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 258998431046931323342239157 24281102910649811563334921)
    ·
      refine ⟨18210827182987358672501191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24281102910649811563334921 18210827182987358672501191)
      ·
        refine ⟨27316240774481038008751787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18210827182987358672501191 27316240774481038008751787)
        ·
          refine ⟨40974361161721557013127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27316240774481038008751787 40974361161721557013127681)
          ·
            refine ⟨30730770871291167759845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40974361161721557013127681 30730770871291167759845761)
            ·
              refine ⟨23048078153468375819884321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30730770871291167759845761 23048078153468375819884321)
              ·
                refine ⟨17286058615101281864913241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23048078153468375819884321 17286058615101281864913241)
                ·
                  refine ⟨12964543961325961398684931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17286058615101281864913241 12964543961325961398684931)
                  ·
                    refine ⟨19446815941988942098027397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12964543961325961398684931 19446815941988942098027397)
                    ·
                      refine ⟨3646277989122926643380137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19446815941988942098027397 3646277989122926643380137)
                      ·
                        rfl

theorem cell23_7101101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7101101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101101 prefixEnd_7101101 := by exact prefixLift 7101101
  have htrace : WordTrace (prefixWord ++ tailWord_7101101) baseStart_7101101 baseEnd_7101101 := by
    simpa [prefixWord, tailWord_7101101, baseEnd_7101101] using wordTrace_append hprefix tailTrace_7101101
  have hstable : (prefixWord ++ tailWord_7101101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101101).length < 2 ^ (prefixWord ++ tailWord_7101101).sum := by decide
  have hdescent : baseEnd_7101101 < baseStart_7101101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101127 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_7101127 : Nat := 118140960795 + 7101127 * 2 ^ 59
def prefixEnd_7101127 : Nat := 4983230072969 + 3 ^ 40 * 7101127 * 2
def baseEnd_7101127 : Nat := 3646291339619943541655017

theorem tailTrace_7101127 : CollatzResearch.WordTrace tailWord_7101127 prefixEnd_7101127 3646291339619943541655017 := by
  unfold tailWord_7101127
  simp only [CollatzResearch.WordTrace]
  refine ⟨258999379344837129782685635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172666252896558086521790423 258999379344837129782685635)
  ·
    refine ⟨388499069017255694674028453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258999379344837129782685635 388499069017255694674028453)
    ·
      refine ⟨72843575440735442751380335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388499069017255694674028453 72843575440735442751380335)
      ·
        refine ⟨109265363161103164127070503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72843575440735442751380335 109265363161103164127070503)
        ·
          refine ⟨163898044741654746190605755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109265363161103164127070503 163898044741654746190605755)
          ·
            refine ⟨245847067112482119285908633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163898044741654746190605755 245847067112482119285908633)
            ·
              refine ⟨184385300334361589464431475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245847067112482119285908633 184385300334361589464431475)
              ·
                refine ⟨276577950501542384196647213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184385300334361589464431475 276577950501542384196647213)
                ·
                  refine ⟨103716731438078394073742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276577950501542384196647213 103716731438078394073742705)
                  ·
                    refine ⟨77787548578558795555307029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103716731438078394073742705 77787548578558795555307029)
                    ·
                      refine ⟨3646291339619943541655017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77787548578558795555307029 3646291339619943541655017)
                      ·
                        rfl

theorem cell23_7101127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_7101127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101127 prefixEnd_7101127 := by exact prefixLift 7101127
  have htrace : WordTrace (prefixWord ++ tailWord_7101127) baseStart_7101127 baseEnd_7101127 := by
    simpa [prefixWord, tailWord_7101127, baseEnd_7101127] using wordTrace_append hprefix tailTrace_7101127
  have hstable : (prefixWord ++ tailWord_7101127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101127).length < 2 ^ (prefixWord ++ tailWord_7101127).sum := by decide
  have hdescent : baseEnd_7101127 < baseStart_7101127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101161 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 2, 3, 2]
def baseStart_7101161 : Nat := 118140960795 + 7101161 * 2 ^ 59
def prefixEnd_7101161 : Nat := 4983230072969 + 3 ^ 40 * 7101161 * 2
def baseEnd_7101161 : Nat := 3646308797962196408629861

theorem tailTrace_7101161 : CollatzResearch.WordTrace tailWord_7101161 prefixEnd_7101161 3646308797962196408629861 := by
  unfold tailWord_7101161
  simp only [CollatzResearch.WordTrace]
  refine ⟨259000619426713953589423337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172667079617809302392948891 259000619426713953589423337)
  ·
    refine ⟨194250464570035465192067503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259000619426713953589423337 194250464570035465192067503)
    ·
      refine ⟨291375696855053197788101255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194250464570035465192067503 291375696855053197788101255)
      ·
        refine ⟨437063545282579796682151883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291375696855053197788101255 437063545282579796682151883)
        ·
          refine ⟨655595317923869695023227825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437063545282579796682151883 655595317923869695023227825)
          ·
            refine ⟨491696488442902271267420869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655595317923869695023227825 491696488442902271267420869)
            ·
              refine ⟨92193091583044175862641413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 491696488442902271267420869 92193091583044175862641413)
              ·
                refine ⟨17286204671820782974245265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92193091583044175862641413 17286204671820782974245265)
                ·
                  refine ⟨12964653503865587230683949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17286204671820782974245265 12964653503865587230683949)
                  ·
                    refine ⟨4861745063949595211506481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12964653503865587230683949 4861745063949595211506481)
                    ·
                      refine ⟨3646308797962196408629861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861745063949595211506481 3646308797962196408629861)
                      ·
                        rfl

theorem cell23_7101161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3, 2].length) (baseStart_7101161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101161 prefixEnd_7101161 := by exact prefixLift 7101161
  have htrace : WordTrace (prefixWord ++ tailWord_7101161) baseStart_7101161 baseEnd_7101161 := by
    simpa [prefixWord, tailWord_7101161, baseEnd_7101161] using wordTrace_append hprefix tailTrace_7101161
  have hstable : (prefixWord ++ tailWord_7101161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101161).length < 2 ^ (prefixWord ++ tailWord_7101161).sum := by decide
  have hdescent : baseEnd_7101161 < baseStart_7101161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101168 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3]
def baseStart_7101168 : Nat := 118140960795 + 7101168 * 2 ^ 59
def prefixEnd_7101168 : Nat := 4983230072969 + 3 ^ 40 * 7101168 * 2
def baseEnd_7101168 : Nat := 3646312392326777881242329

theorem tailTrace_7101168 : CollatzResearch.WordTrace tailWord_7101168 prefixEnd_7101168 3646312392326777881242329 := by
  unfold tailWord_7101168
  simp only [CollatzResearch.WordTrace]
  refine ⟨129500437368844296892464079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172667249825125729189952105 129500437368844296892464079)
  ·
    refine ⟨194250656053266445338696119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129500437368844296892464079 194250656053266445338696119)
    ·
      refine ⟨291375984079899668008044179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194250656053266445338696119 291375984079899668008044179)
      ·
        refine ⟨437063976119849502012066269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291375984079899668008044179 437063976119849502012066269)
        ·
          refine ⟨163898991044943563254524851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437063976119849502012066269 163898991044943563254524851)
          ·
            refine ⟨245848486567415344881787277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163898991044943563254524851 245848486567415344881787277)
            ·
              refine ⟨92193182462780754330670229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245848486567415344881787277 92193182462780754330670229)
              ·
                refine ⟨4321555427942847859250167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92193182462780754330670229 4321555427942847859250167)
                ·
                  refine ⟨6482333141914271788875251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321555427942847859250167 6482333141914271788875251)
                  ·
                    refine ⟨9723499712871407683312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482333141914271788875251 9723499712871407683312877)
                    ·
                      refine ⟨3646312392326777881242329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723499712871407683312877 3646312392326777881242329)
                      ·
                        rfl

theorem cell23_7101168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3].length) (baseStart_7101168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101168 prefixEnd_7101168 := by exact prefixLift 7101168
  have htrace : WordTrace (prefixWord ++ tailWord_7101168) baseStart_7101168 baseEnd_7101168 := by
    simpa [prefixWord, tailWord_7101168, baseEnd_7101168] using wordTrace_append hprefix tailTrace_7101168
  have hstable : (prefixWord ++ tailWord_7101168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101168).length < 2 ^ (prefixWord ++ tailWord_7101168).sum := by decide
  have hdescent : baseEnd_7101168 < baseStart_7101168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101184 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_7101184 : Nat := 118140960795 + 7101184 * 2 ^ 59
def prefixEnd_7101184 : Nat := 4983230072969 + 3 ^ 40 * 7101184 * 2
def baseEnd_7101184 : Nat := 1215440202672416606214085

theorem tailTrace_7101184 : CollatzResearch.WordTrace tailWord_7101184 prefixEnd_7101184 1215440202672416606214085 := by
  unfold tailWord_7101184
  simp only [CollatzResearch.WordTrace]
  refine ⟨129500729152815314258755303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172667638870420419011673737 129500729152815314258755303)
  ·
    refine ⟨194251093729222971388132955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129500729152815314258755303 194251093729222971388132955)
    ·
      refine ⟨291376640593834457082199433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194251093729222971388132955 291376640593834457082199433)
      ·
        refine ⟨218532480445375842811649575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291376640593834457082199433 218532480445375842811649575)
        ·
          refine ⟨327798720668063764217474363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218532480445375842811649575 327798720668063764217474363)
          ·
            refine ⟨491698081002095646326211545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327798720668063764217474363 491698081002095646326211545)
            ·
              refine ⟨368773560751571734744658659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491698081002095646326211545 368773560751571734744658659)
              ·
                refine ⟨553160341127357602116987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368773560751571734744658659 553160341127357602116987989)
                ·
                  refine ⟨6482347747586221899808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 553160341127357602116987989 6482347747586221899808453)
                  ·
                    refine ⟨1215440202672416606214085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482347747586221899808453 1215440202672416606214085)
                    ·
                      rfl

theorem cell23_7101184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_7101184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101184 prefixEnd_7101184 := by exact prefixLift 7101184
  have htrace : WordTrace (prefixWord ++ tailWord_7101184) baseStart_7101184 baseEnd_7101184 := by
    simpa [prefixWord, tailWord_7101184, baseEnd_7101184] using wordTrace_append hprefix tailTrace_7101184
  have hstable : (prefixWord ++ tailWord_7101184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101184).length < 2 ^ (prefixWord ++ tailWord_7101184).sum := by decide
  have hdescent : baseEnd_7101184 < baseStart_7101184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101194 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7101194 : Nat := 118140960795 + 7101194 * 2 ^ 59
def prefixEnd_7101194 : Nat := 4983230072969 + 3 ^ 40 * 7101194 * 2
def baseEnd_7101194 : Nat := 3646325742823794779517209

theorem tailTrace_7101194 : CollatzResearch.WordTrace tailWord_7101194 prefixEnd_7101194 3646325742823794779517209 := by
  unfold tailWord_7101194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64750455758898600056343659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172667882023729600150249757 64750455758898600056343659)
  ·
    refine ⟨97125683638347900084515489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64750455758898600056343659 97125683638347900084515489)
    ·
      refine ⟨72844262728760925063386617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97125683638347900084515489 72844262728760925063386617)
      ·
        refine ⟨54633197046570693797539963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72844262728760925063386617 54633197046570693797539963)
        ·
          refine ⟨81949795569856040696309945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54633197046570693797539963 81949795569856040696309945)
          ·
            refine ⟨61462346677392030522232459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81949795569856040696309945 61462346677392030522232459)
            ·
              refine ⟨92193520016088045783348689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61462346677392030522232459 92193520016088045783348689)
              ·
                refine ⟨69145140012066034337511517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92193520016088045783348689 69145140012066034337511517)
                ·
                  refine ⟨25929427504524762876566819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69145140012066034337511517 25929427504524762876566819)
                  ·
                    refine ⟨38894141256787144314850229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25929427504524762876566819 38894141256787144314850229)
                    ·
                      refine ⟨3646325742823794779517209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38894141256787144314850229 3646325742823794779517209)
                      ·
                        rfl

theorem cell23_7101194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7101194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101194 prefixEnd_7101194 := by exact prefixLift 7101194
  have htrace : WordTrace (prefixWord ++ tailWord_7101194) baseStart_7101194 baseEnd_7101194 := by
    simpa [prefixWord, tailWord_7101194, baseEnd_7101194] using wordTrace_append hprefix tailTrace_7101194
  have hstable : (prefixWord ++ tailWord_7101194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101194).length < 2 ^ (prefixWord ++ tailWord_7101194).sum := by decide
  have hdescent : baseEnd_7101194 < baseStart_7101194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101234 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7101234 : Nat := 118140960795 + 7101234 * 2 ^ 59
def prefixEnd_7101234 : Nat := 4983230072969 + 3 ^ 40 * 7101234 * 2
def baseEnd_7101234 : Nat := 3646346282049974623017025

theorem tailTrace_7101234 : CollatzResearch.WordTrace tailWord_7101234 prefixEnd_7101234 3646346282049974623017025 := by
  unfold tailWord_7101234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64750820488862371764207689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172668854636966324704553837 64750820488862371764207689)
  ·
    refine ⟨48563115366646778823155767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64750820488862371764207689 48563115366646778823155767)
    ·
      refine ⟨72844673049970168234733651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48563115366646778823155767 72844673049970168234733651)
      ·
        refine ⟨109267009574955252352100477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72844673049970168234733651 109267009574955252352100477)
        ·
          refine ⟨40975128590608219632037679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109267009574955252352100477 40975128590608219632037679)
          ·
            refine ⟨61462692885912329448056519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40975128590608219632037679 61462692885912329448056519)
            ·
              refine ⟨92194039328868494172084779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61462692885912329448056519 92194039328868494172084779)
              ·
                refine ⟨138291058993302741258127169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92194039328868494172084779 138291058993302741258127169)
                ·
                  refine ⟨103718294244977055943595377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138291058993302741258127169 103718294244977055943595377)
                  ·
                    refine ⟨77788720683732791957696533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103718294244977055943595377 77788720683732791957696533)
                    ·
                      refine ⟨3646346282049974623017025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77788720683732791957696533 3646346282049974623017025)
                      ·
                        rfl

theorem cell23_7101234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7101234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101234 prefixEnd_7101234 := by exact prefixLift 7101234
  have htrace : WordTrace (prefixWord ++ tailWord_7101234) baseStart_7101234 baseEnd_7101234 := by
    simpa [prefixWord, tailWord_7101234, baseEnd_7101234] using wordTrace_append hprefix tailTrace_7101234
  have hstable : (prefixWord ++ tailWord_7101234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101234).length < 2 ^ (prefixWord ++ tailWord_7101234).sum := by decide
  have hdescent : baseEnd_7101234 < baseStart_7101234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101235 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 2, 4]
def baseStart_7101235 : Nat := 118140960795 + 7101235 * 2 ^ 59
def prefixEnd_7101235 : Nat := 4983230072969 + 3 ^ 40 * 7101235 * 2
def baseEnd_7101235 : Nat := 1215448931843543039701507

theorem tailTrace_7101235 : CollatzResearch.WordTrace tailWord_7101235 prefixEnd_7101235 1215448931843543039701507 := by
  unfold tailWord_7101235
  simp only [CollatzResearch.WordTrace]
  refine ⟨259003318428445864227617159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172668878952297242818411439 259003318428445864227617159)
  ·
    refine ⟨388504977642668796341425739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259003318428445864227617159 388504977642668796341425739)
    ·
      refine ⟨582757466464003194512138609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388504977642668796341425739 582757466464003194512138609)
      ·
        refine ⟨437068099848002395884103957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582757466464003194512138609 437068099848002395884103957)
        ·
          refine ⟨20487567180375112307067373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 437068099848002395884103957 20487567180375112307067373)
          ·
            refine ⟨7682837692640667115150265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20487567180375112307067373 7682837692640667115150265)
            ·
              refine ⟨5762128269480500336362699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682837692640667115150265 5762128269480500336362699)
              ·
                refine ⟨8643192404220750504544049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762128269480500336362699 8643192404220750504544049)
                ·
                  refine ⟨6482394303165562878408037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8643192404220750504544049 6482394303165562878408037)
                  ·
                    refine ⟨1215448931843543039701507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482394303165562878408037 1215448931843543039701507)
                    ·
                      rfl

theorem cell23_7101235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 2, 4].length) (baseStart_7101235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101235 prefixEnd_7101235 := by exact prefixLift 7101235
  have htrace : WordTrace (prefixWord ++ tailWord_7101235) baseStart_7101235 baseEnd_7101235 := by
    simpa [prefixWord, tailWord_7101235, baseEnd_7101235] using wordTrace_append hprefix tailTrace_7101235
  have hstable : (prefixWord ++ tailWord_7101235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101235).length < 2 ^ (prefixWord ++ tailWord_7101235).sum := by decide
  have hdescent : baseEnd_7101235 < baseStart_7101235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101276 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7101276 : Nat := 118140960795 + 7101276 * 2 ^ 59
def prefixEnd_7101276 : Nat := 4983230072969 + 3 ^ 40 * 7101276 * 2
def baseEnd_7101276 : Nat := 3646367848237463458691833

theorem tailTrace_7101276 : CollatzResearch.WordTrace tailWord_7101276 prefixEnd_7101276 3646367848237463458691833 := by
  unfold tailWord_7101276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129502406910648664114929841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172669875880864885486573121 129502406910648664114929841)
  ·
    refine ⟨97126805182986498086197381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129502406910648664114929841 97126805182986498086197381)
    ·
      refine ⟨18211275971809968391162009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97126805182986498086197381 18211275971809968391162009)
      ·
        refine ⟨13658456978857476293371507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18211275971809968391162009 13658456978857476293371507)
        ·
          refine ⟨20487685468286214440057261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658456978857476293371507 20487685468286214440057261)
          ·
            refine ⟨7682882050607330415021473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20487685468286214440057261 7682882050607330415021473)
            ·
              refine ⟨5762161537955497811266105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682882050607330415021473 5762161537955497811266105)
              ·
                refine ⟨4321621153466623358449579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762161537955497811266105 4321621153466623358449579)
                ·
                  refine ⟨6482431730199935037674369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321621153466623358449579 6482431730199935037674369)
                  ·
                    refine ⟨4861823797649951278255777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482431730199935037674369 4861823797649951278255777)
                    ·
                      refine ⟨3646367848237463458691833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861823797649951278255777 3646367848237463458691833)
                      ·
                        rfl

theorem cell23_7101276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7101276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101276 prefixEnd_7101276 := by exact prefixLift 7101276
  have htrace : WordTrace (prefixWord ++ tailWord_7101276) baseStart_7101276 baseEnd_7101276 := by
    simpa [prefixWord, tailWord_7101276, baseEnd_7101276] using wordTrace_append hprefix tailTrace_7101276
  have hstable : (prefixWord ++ tailWord_7101276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101276).length < 2 ^ (prefixWord ++ tailWord_7101276).sum := by decide
  have hdescent : baseEnd_7101276 < baseStart_7101276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101298 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7101298 : Nat := 118140960795 + 7101298 * 2 ^ 59
def prefixEnd_7101298 : Nat := 4983230072969 + 3 ^ 40 * 7101298 * 2
def baseEnd_7101298 : Nat := 3646379144811862372616731

theorem tailTrace_7101298 : CollatzResearch.WordTrace tailWord_7101298 prefixEnd_7101298 3646379144811862372616731 := by
  unfold tailWord_7101298
  simp only [CollatzResearch.WordTrace]
  refine ⟨64751404056804406496790137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172670410818145083991440365 64751404056804406496790137)
  ·
    refine ⟨48563553042603304872592603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64751404056804406496790137 48563553042603304872592603)
    ·
      refine ⟨72845329563904957308888905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48563553042603304872592603 72845329563904957308888905)
      ·
        refine ⟨54633997172928717981666679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72845329563904957308888905 54633997172928717981666679)
        ·
          refine ⟨81950995759393076972500019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54633997172928717981666679 81950995759393076972500019)
          ·
            refine ⟨122926493639089615458750029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81950995759393076972500019 122926493639089615458750029)
            ·
              refine ⟨46097435114658605797031261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122926493639089615458750029 46097435114658605797031261)
              ·
                refine ⟨17286538167996977173886723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46097435114658605797031261 17286538167996977173886723)
                ·
                  refine ⟨25929807251995465760830085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17286538167996977173886723 25929807251995465760830085)
                  ·
                    refine ⟨4861838859749149830155641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25929807251995465760830085 4861838859749149830155641)
                    ·
                      refine ⟨3646379144811862372616731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861838859749149830155641 3646379144811862372616731)
                      ·
                        rfl

theorem cell23_7101298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7101298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101298 prefixEnd_7101298 := by exact prefixLift 7101298
  have htrace : WordTrace (prefixWord ++ tailWord_7101298) baseStart_7101298 baseEnd_7101298 := by
    simpa [prefixWord, tailWord_7101298, baseEnd_7101298] using wordTrace_append hprefix tailTrace_7101298
  have hstable : (prefixWord ++ tailWord_7101298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101298).length < 2 ^ (prefixWord ++ tailWord_7101298).sum := by decide
  have hdescent : baseEnd_7101298 < baseStart_7101298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101338 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_7101338 : Nat := 118140960795 + 7101338 * 2 ^ 59
def prefixEnd_7101338 : Nat := 4983230072969 + 3 ^ 40 * 7101338 * 2
def baseEnd_7101338 : Nat := 405155520448671357346283

theorem tailTrace_7101338 : CollatzResearch.WordTrace tailWord_7101338 prefixEnd_7101338 405155520448671357346283 := by
  unfold tailWord_7101338
  simp only [CollatzResearch.WordTrace]
  refine ⟨64751768786768178204654167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172671383431381808545744445 64751768786768178204654167)
  ·
    refine ⟨97127653180152267306981251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64751768786768178204654167 97127653180152267306981251)
    ·
      refine ⟨145691479770228400960471877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97127653180152267306981251 145691479770228400960471877)
      ·
        refine ⟨27317152456917825180088477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145691479770228400960471877 27317152456917825180088477)
        ·
          refine ⟨10243932171344184442533179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27317152456917825180088477 10243932171344184442533179)
          ·
            refine ⟨15365898257016276663799769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10243932171344184442533179 15365898257016276663799769)
            ·
              refine ⟨11524423692762207497849827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15365898257016276663799769 11524423692762207497849827)
              ·
                refine ⟨17286635539143311246774741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524423692762207497849827 17286635539143311246774741)
                ·
                  refine ⟨405155520448671357346283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17286635539143311246774741 405155520448671357346283)
                  ·
                    rfl

theorem cell23_7101338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_7101338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101338 prefixEnd_7101338 := by exact prefixLift 7101338
  have htrace : WordTrace (prefixWord ++ tailWord_7101338) baseStart_7101338 baseEnd_7101338 := by
    simpa [prefixWord, tailWord_7101338, baseEnd_7101338] using wordTrace_append hprefix tailTrace_7101338
  have hstable : (prefixWord ++ tailWord_7101338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101338).length < 2 ^ (prefixWord ++ tailWord_7101338).sum := by decide
  have hdescent : baseEnd_7101338 < baseStart_7101338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101388 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7101388 : Nat := 118140960795 + 7101388 * 2 ^ 59
def prefixEnd_7101388 : Nat := 4983230072969 + 3 ^ 40 * 7101388 * 2
def baseEnd_7101388 : Nat := 3646425358070767020491317

theorem tailTrace_7101388 : CollatzResearch.WordTrace tailWord_7101388 prefixEnd_7101388 3646425358070767020491317 := by
  unfold tailWord_7101388
  simp only [CollatzResearch.WordTrace]
  refine ⟨129504449398445785678968409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172672599197927714238624545 129504449398445785678968409)
  ·
    refine ⟨97128337048834339259226307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129504449398445785678968409 97128337048834339259226307)
    ·
      refine ⟨145692505573251508888839461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97128337048834339259226307 145692505573251508888839461)
      ·
        refine ⟨27317344794984657916657399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145692505573251508888839461 27317344794984657916657399)
        ·
          refine ⟨40976017192476986874986099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27317344794984657916657399 40976017192476986874986099)
          ·
            refine ⟨61464025788715480312479149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40976017192476986874986099 61464025788715480312479149)
            ·
              refine ⟨23049009670768305117179681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61464025788715480312479149 23049009670768305117179681)
              ·
                refine ⟨17286757253076228837884761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23049009670768305117179681 17286757253076228837884761)
                ·
                  refine ⟨12965067939807171628413571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17286757253076228837884761 12965067939807171628413571)
                  ·
                    refine ⟨19447601909710757442620357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12965067939807171628413571 19447601909710757442620357)
                    ·
                      refine ⟨3646425358070767020491317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19447601909710757442620357 3646425358070767020491317)
                      ·
                        rfl

theorem cell23_7101388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7101388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101388 prefixEnd_7101388 := by exact prefixLift 7101388
  have htrace : WordTrace (prefixWord ++ tailWord_7101388) baseStart_7101388 baseEnd_7101388 := by
    simpa [prefixWord, tailWord_7101388, baseEnd_7101388] using wordTrace_append hprefix tailTrace_7101388
  have hstable : (prefixWord ++ tailWord_7101388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101388).length < 2 ^ (prefixWord ++ tailWord_7101388).sum := by decide
  have hdescent : baseEnd_7101388 < baseStart_7101388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101389 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 7]
def baseStart_7101389 : Nat := 118140960795 + 7101389 * 2 ^ 59
def prefixEnd_7101389 : Nat := 4983230072969 + 3 ^ 40 * 7101389 * 2
def baseEnd_7101389 : Nat := 405158430172380168508757

theorem tailTrace_7101389 : CollatzResearch.WordTrace tailWord_7101389 prefixEnd_7101389 405158430172380168508757 := by
  unfold tailWord_7101389
  simp only [CollatzResearch.WordTrace]
  refine ⟨259008935269887948528723221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172672623513258632352482147 259008935269887948528723221)
  ·
    refine ⟨12141043840775997587283901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259008935269887948528723221 12141043840775997587283901)
    ·
      refine ⟨4552891440290999095231463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12141043840775997587283901 4552891440290999095231463)
      ·
        refine ⟨6829337160436498642847195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552891440290999095231463 6829337160436498642847195)
        ·
          refine ⟨10244005740654747964270793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829337160436498642847195 10244005740654747964270793)
          ·
            refine ⟨7683004305491060973203095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10244005740654747964270793 7683004305491060973203095)
            ·
              refine ⟨11524506458236591459804643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683004305491060973203095 11524506458236591459804643)
              ·
                refine ⟨17286759687354887189706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524506458236591459804643 17286759687354887189706965)
                ·
                  refine ⟨405158430172380168508757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17286759687354887189706965 405158430172380168508757)
                  ·
                    rfl

theorem cell23_7101389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_7101389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101389 prefixEnd_7101389 := by exact prefixLift 7101389
  have htrace : WordTrace (prefixWord ++ tailWord_7101389) baseStart_7101389 baseEnd_7101389 := by
    simpa [prefixWord, tailWord_7101389, baseEnd_7101389] using wordTrace_append hprefix tailTrace_7101389
  have hstable : (prefixWord ++ tailWord_7101389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101389).length < 2 ^ (prefixWord ++ tailWord_7101389).sum := by decide
  have hdescent : baseEnd_7101389 < baseStart_7101389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101425 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_7101425 : Nat := 118140960795 + 7101425 * 2 ^ 59
def prefixEnd_7101425 : Nat := 4983230072969 + 3 ^ 40 * 7101425 * 2
def baseEnd_7101425 : Nat := 3646444356854983375728647

theorem tailTrace_7101425 : CollatzResearch.WordTrace tailWord_7101425 prefixEnd_7101425 3646444356854983375728647 := by
  unfold tailWord_7101425
  simp only [CollatzResearch.WordTrace]
  refine ⟨259010248297757526677033729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172673498865171684451355819 259010248297757526677033729)
  ·
    refine ⟨194257686223318145007775297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259010248297757526677033729 194257686223318145007775297)
    ·
      refine ⟨145693264667488608755831473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194257686223318145007775297 145693264667488608755831473)
      ·
        refine ⟨109269948500616456566873605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145693264667488608755831473 109269948500616456566873605)
        ·
          refine ⟨20488115343865585606288801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109269948500616456566873605 20488115343865585606288801)
          ·
            refine ⟨15366086507899189204716601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20488115343865585606288801 15366086507899189204716601)
            ·
              refine ⟨11524564880924391903537451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15366086507899189204716601 11524564880924391903537451)
              ·
                refine ⟨17286847321386587855306177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524564880924391903537451 17286847321386587855306177)
                ·
                  refine ⟨12965135491039940891479633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17286847321386587855306177 12965135491039940891479633)
                  ·
                    refine ⟨9723851618279955668609725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12965135491039940891479633 9723851618279955668609725)
                    ·
                      refine ⟨3646444356854983375728647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723851618279955668609725 3646444356854983375728647)
                      ·
                        rfl

theorem cell23_7101425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_7101425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101425 prefixEnd_7101425 := by exact prefixLift 7101425
  have htrace : WordTrace (prefixWord ++ tailWord_7101425) baseStart_7101425 baseEnd_7101425 := by
    simpa [prefixWord, tailWord_7101425, baseEnd_7101425] using wordTrace_append hprefix tailTrace_7101425
  have hstable : (prefixWord ++ tailWord_7101425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101425).length < 2 ^ (prefixWord ++ tailWord_7101425).sum := by decide
  have hdescent : baseEnd_7101425 < baseStart_7101425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101482 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7101482 : Nat := 118140960795 + 7101482 * 2 ^ 59
def prefixEnd_7101482 : Nat := 4983230072969 + 3 ^ 40 * 7101482 * 2
def baseEnd_7101482 : Nat := 3646473625252289652715885

theorem tailTrace_7101482 : CollatzResearch.WordTrace tailWord_7101482 prefixEnd_7101482 3646473625252289652715885 := by
  unfold tailWord_7101482
  simp only [CollatzResearch.WordTrace]
  refine ⟨64753081814637756352964675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172674884839034016941239133 64753081814637756352964675)
  ·
    refine ⟨97129622721956634529447013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64753081814637756352964675 97129622721956634529447013)
    ·
      refine ⟨18211804260366868974271315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97129622721956634529447013 18211804260366868974271315)
      ·
        refine ⟨27317706390550303461406973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18211804260366868974271315 27317706390550303461406973)
        ·
          refine ⟨10244139896456363798027615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27317706390550303461406973 10244139896456363798027615)
          ·
            refine ⟨15366209844684545697041423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244139896456363798027615 15366209844684545697041423)
            ·
              refine ⟨23049314767026818545562135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366209844684545697041423 23049314767026818545562135)
              ·
                refine ⟨34573972150540227818343203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23049314767026818545562135 34573972150540227818343203)
                ·
                  refine ⟨51860958225810341727514805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34573972150540227818343203 51860958225810341727514805)
                  ·
                    refine ⟨4861964833669719536954513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51860958225810341727514805 4861964833669719536954513)
                    ·
                      refine ⟨3646473625252289652715885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861964833669719536954513 3646473625252289652715885)
                      ·
                        rfl

theorem cell23_7101482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7101482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101482 prefixEnd_7101482 := by exact prefixLift 7101482
  have htrace : WordTrace (prefixWord ++ tailWord_7101482) baseStart_7101482 baseEnd_7101482 := by
    simpa [prefixWord, tailWord_7101482, baseEnd_7101482] using wordTrace_append hprefix tailTrace_7101482
  have hstable : (prefixWord ++ tailWord_7101482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101482).length < 2 ^ (prefixWord ++ tailWord_7101482).sum := by decide
  have hdescent : baseEnd_7101482 < baseStart_7101482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101488 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_7101488 : Nat := 118140960795 + 7101488 * 2 ^ 59
def prefixEnd_7101488 : Nat := 4983230072969 + 3 ^ 40 * 7101488 * 2
def baseEnd_7101488 : Nat := 1215492235378738876413619

theorem tailTrace_7101488 : CollatzResearch.WordTrace tailWord_7101488 prefixEnd_7101488 1215492235378738876413619 := by
  unfold tailWord_7101488
  simp only [CollatzResearch.WordTrace]
  refine ⟨129506273048264644218288559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172675030731019525624384745 129506273048264644218288559)
  ·
    refine ⟨194259409572396966327432839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129506273048264644218288559 194259409572396966327432839)
    ·
      refine ⟨291389114358595449491149259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194259409572396966327432839 291389114358595449491149259)
      ·
        refine ⟨437083671537893174236723889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291389114358595449491149259 437083671537893174236723889)
        ·
          refine ⟨327812753653419880677542917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437083671537893174236723889 327812753653419880677542917)
          ·
            refine ⟨61464891310016227627039297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327812753653419880677542917 61464891310016227627039297)
            ·
              refine ⟨46098668482512170720279473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61464891310016227627039297 46098668482512170720279473)
              ·
                refine ⟨34574001361884128040209605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46098668482512170720279473 34574001361884128040209605)
                ·
                  refine ⟨6482625255353274007539301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34574001361884128040209605 6482625255353274007539301)
                  ·
                    refine ⟨1215492235378738876413619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482625255353274007539301 1215492235378738876413619)
                    ·
                      rfl

theorem cell23_7101488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_7101488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101488 prefixEnd_7101488 := by exact prefixLift 7101488
  have htrace : WordTrace (prefixWord ++ tailWord_7101488) baseStart_7101488 baseEnd_7101488 := by
    simpa [prefixWord, tailWord_7101488, baseEnd_7101488] using wordTrace_append hprefix tailTrace_7101488
  have hstable : (prefixWord ++ tailWord_7101488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101488).length < 2 ^ (prefixWord ++ tailWord_7101488).sum := by decide
  have hdescent : baseEnd_7101488 < baseStart_7101488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101491 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_7101491 : Nat := 118140960795 + 7101491 * 2 ^ 59
def prefixEnd_7101491 : Nat := 4983230072969 + 3 ^ 40 * 7101491 * 2
def baseEnd_7101491 : Nat := 3646478246578180117503343

theorem tailTrace_7101491 : CollatzResearch.WordTrace tailWord_7101491 prefixEnd_7101491 3646478246578180117503343 := by
  unfold tailWord_7101491
  simp only [CollatzResearch.WordTrace]
  refine ⟨259012655515518419948936327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172675103677012279965957551 259012655515518419948936327)
  ·
    refine ⟨388518983273277629923404491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259012655515518419948936327 388518983273277629923404491)
    ·
      refine ⟨582778474909916444885106737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388518983273277629923404491 582778474909916444885106737)
      ·
        refine ⟨437083856182437333663830053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582778474909916444885106737 437083856182437333663830053)
        ·
          refine ⟨81953223034207000061968135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437083856182437333663830053 81953223034207000061968135)
          ·
            refine ⟨122929834551310500092952203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81953223034207000061968135 122929834551310500092952203)
            ·
              refine ⟨184394751826965750139428305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122929834551310500092952203 184394751826965750139428305)
              ·
                refine ⟨138296063870224312604571229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184394751826965750139428305 138296063870224312604571229)
                ·
                  refine ⟨51861023951334117226714211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138296063870224312604571229 51861023951334117226714211)
                  ·
                    refine ⟨77791535927001175840071317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51861023951334117226714211 77791535927001175840071317)
                    ·
                      refine ⟨3646478246578180117503343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77791535927001175840071317 3646478246578180117503343)
                      ·
                        rfl

theorem cell23_7101491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_7101491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101491 prefixEnd_7101491 := by exact prefixLift 7101491
  have htrace : WordTrace (prefixWord ++ tailWord_7101491) baseStart_7101491 baseEnd_7101491 := by
    simpa [prefixWord, tailWord_7101491, baseEnd_7101491] using wordTrace_append hprefix tailTrace_7101491
  have hstable : (prefixWord ++ tailWord_7101491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101491).length < 2 ^ (prefixWord ++ tailWord_7101491).sum := by decide
  have hdescent : baseEnd_7101491 < baseStart_7101491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101492 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7101492 : Nat := 118140960795 + 7101492 * 2 ^ 59
def prefixEnd_7101492 : Nat := 4983230072969 + 3 ^ 40 * 7101492 * 2
def baseEnd_7101492 : Nat := 1215492920019611537863613

theorem tailTrace_7101492 : CollatzResearch.WordTrace tailWord_7101492 prefixEnd_7101492 1215492920019611537863613 := by
  unfold tailWord_7101492
  simp only [CollatzResearch.WordTrace]
  refine ⟨129506345994257398559861365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172675127992343198079815153 129506345994257398559861365)
  ·
    refine ⟨12141219936961631114987003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129506345994257398559861365 12141219936961631114987003)
    ·
      refine ⟨18211829905442446672480505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141219936961631114987003 18211829905442446672480505)
      ·
        refine ⟨13658872429081835004360379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18211829905442446672480505 13658872429081835004360379)
        ·
          refine ⟨20488308643622752506540569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658872429081835004360379 20488308643622752506540569)
          ·
            refine ⟨15366231482717064379905427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20488308643622752506540569 15366231482717064379905427)
            ·
              refine ⟨23049347224075596569858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366231482717064379905427 23049347224075596569858141)
              ·
                refine ⟨8643505209028348713696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23049347224075596569858141 8643505209028348713696803)
                ·
                  refine ⟨12965257813542523070545205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643505209028348713696803 12965257813542523070545205)
                  ·
                    refine ⟨1215492920019611537863613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12965257813542523070545205 1215492920019611537863613)
                    ·
                      rfl

theorem cell23_7101492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7101492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101492 prefixEnd_7101492 := by exact prefixLift 7101492
  have htrace : WordTrace (prefixWord ++ tailWord_7101492) baseStart_7101492 baseEnd_7101492 := by
    simpa [prefixWord, tailWord_7101492, baseEnd_7101492] using wordTrace_append hprefix tailTrace_7101492
  have hstable : (prefixWord ++ tailWord_7101492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101492).length < 2 ^ (prefixWord ++ tailWord_7101492).sum := by decide
  have hdescent : baseEnd_7101492 < baseStart_7101492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101495 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_7101495 : Nat := 118140960795 + 7101495 * 2 ^ 59
def prefixEnd_7101495 : Nat := 4983230072969 + 3 ^ 40 * 7101495 * 2
def baseEnd_7101495 : Nat := 3646480300500798101853325

theorem tailTrace_7101495 : CollatzResearch.WordTrace tailWord_7101495 prefixEnd_7101495 3646480300500798101853325 := by
  unfold tailWord_7101495
  simp only [CollatzResearch.WordTrace]
  refine ⟨259012801407503928632081939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172675200938335952421387959 259012801407503928632081939)
  ·
    refine ⟨388519202111255892948122909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259012801407503928632081939 388519202111255892948122909)
    ·
      refine ⟨145694700791720959855546091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388519202111255892948122909 145694700791720959855546091)
      ·
        refine ⟨218542051187581439783319137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145694700791720959855546091 218542051187581439783319137)
        ·
          refine ⟨163906538390686079837489353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218542051187581439783319137 163906538390686079837489353)
          ·
            refine ⟨122929903793014559878117015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163906538390686079837489353 122929903793014559878117015)
            ·
              refine ⟨184394855689521839817175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122929903793014559878117015 184394855689521839817175523)
              ·
                refine ⟨276592283534282759725763285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184394855689521839817175523 276592283534282759725763285)
                ·
                  refine ⟨6482631645334752181072577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276592283534282759725763285 6482631645334752181072577)
                  ·
                    refine ⟨4861973734001064135804433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482631645334752181072577 4861973734001064135804433)
                    ·
                      refine ⟨3646480300500798101853325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861973734001064135804433 3646480300500798101853325)
                      ·
                        rfl

theorem cell23_7101495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_7101495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101495 prefixEnd_7101495 := by exact prefixLift 7101495
  have htrace : WordTrace (prefixWord ++ tailWord_7101495) baseStart_7101495 baseEnd_7101495 := by
    simpa [prefixWord, tailWord_7101495, baseEnd_7101495] using wordTrace_append hprefix tailTrace_7101495
  have hstable : (prefixWord ++ tailWord_7101495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101495).length < 2 ^ (prefixWord ++ tailWord_7101495).sum := by decide
  have hdescent : baseEnd_7101495 < baseStart_7101495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101512 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_7101512 : Nat := 118140960795 + 7101512 * 2 ^ 59
def prefixEnd_7101512 : Nat := 4983230072969 + 3 ^ 40 * 7101512 * 2
def baseEnd_7101512 : Nat := 3646489029671924535340747

theorem tailTrace_7101512 : CollatzResearch.WordTrace tailWord_7101512 prefixEnd_7101512 3646489029671924535340747 := by
  unfold tailWord_7101512
  simp only [CollatzResearch.WordTrace]
  refine ⟨129506710724221170267725395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172675614298961560356967193 129506710724221170267725395)
  ·
    refine ⟨194260066086331755401588093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129506710724221170267725395 194260066086331755401588093)
    ·
      refine ⟨72847524782374408275595535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194260066086331755401588093 72847524782374408275595535)
      ·
        refine ⟨109271287173561612413393303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72847524782374408275595535 109271287173561612413393303)
        ·
          refine ⟨163906930760342418620089955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109271287173561612413393303 163906930760342418620089955)
          ·
            refine ⟨245860396140513627930134933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163906930760342418620089955 245860396140513627930134933)
            ·
              refine ⟨11524706069086576309225075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245860396140513627930134933 11524706069086576309225075)
              ·
                refine ⟨17287059103629864463837613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524706069086576309225075 17287059103629864463837613)
                ·
                  refine ⟨6482647163861199173939105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17287059103629864463837613 6482647163861199173939105)
                  ·
                    refine ⟨4861985372895899380454329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482647163861199173939105 4861985372895899380454329)
                    ·
                      refine ⟨3646489029671924535340747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4861985372895899380454329 3646489029671924535340747)
                      ·
                        rfl

theorem cell23_7101512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_7101512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101512 prefixEnd_7101512 := by exact prefixLift 7101512
  have htrace : WordTrace (prefixWord ++ tailWord_7101512) baseStart_7101512 baseEnd_7101512 := by
    simpa [prefixWord, tailWord_7101512, baseEnd_7101512] using wordTrace_append hprefix tailTrace_7101512
  have hstable : (prefixWord ++ tailWord_7101512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101512).length < 2 ^ (prefixWord ++ tailWord_7101512).sum := by decide
  have hdescent : baseEnd_7101512 < baseStart_7101512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101532 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_7101532 : Nat := 118140960795 + 7101532 * 2 ^ 59
def prefixEnd_7101532 : Nat := 4983230072969 + 3 ^ 40 * 7101532 * 2
def baseEnd_7101532 : Nat := 3646499299285014457090655

theorem tailTrace_7101532 : CollatzResearch.WordTrace tailWord_7101532 prefixEnd_7101532 3646499299285014457090655 := by
  unfold tailWord_7101532
  simp only [CollatzResearch.WordTrace]
  refine ⟨129507075454184941975589425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172676100605579922634119233 129507075454184941975589425)
  ·
    refine ⟨97130306590638706481692069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129507075454184941975589425 97130306590638706481692069)
    ·
      refine ⟨18211932485744757465317263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97130306590638706481692069 18211932485744757465317263)
      ·
        refine ⟨27317898728617136197975895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18211932485744757465317263 27317898728617136197975895)
        ·
          refine ⟨40976848092925704296963843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27317898728617136197975895 40976848092925704296963843)
          ·
            refine ⟨61465272139388556445445765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40976848092925704296963843 61465272139388556445445765)
            ·
              refine ⟨11524738526135354333521081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61465272139388556445445765 11524738526135354333521081)
              ·
                refine ⟨8643553894601515750140811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11524738526135354333521081 8643553894601515750140811)
                ·
                  refine ⟨12965330841902273625211217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643553894601515750140811 12965330841902273625211217)
                  ·
                    refine ⟨9723998131426705218908413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12965330841902273625211217 9723998131426705218908413)
                    ·
                      refine ⟨3646499299285014457090655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9723998131426705218908413 3646499299285014457090655)
                      ·
                        rfl

theorem cell23_7101532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_7101532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101532 prefixEnd_7101532 := by exact prefixLift 7101532
  have htrace : WordTrace (prefixWord ++ tailWord_7101532) baseStart_7101532 baseEnd_7101532 := by
    simpa [prefixWord, tailWord_7101532, baseEnd_7101532] using wordTrace_append hprefix tailTrace_7101532
  have hstable : (prefixWord ++ tailWord_7101532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101532).length < 2 ^ (prefixWord ++ tailWord_7101532).sum := by decide
  have hdescent : baseEnd_7101532 < baseStart_7101532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101545 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_7101545 : Nat := 118140960795 + 7101545 * 2 ^ 59
def prefixEnd_7101545 : Nat := 4983230072969 + 3 ^ 40 * 7101545 * 2
def baseEnd_7101545 : Nat := 3646505974533522906228095

theorem tailTrace_7101545 : CollatzResearch.WordTrace tailWord_7101545 prefixEnd_7101545 3646505974533522906228095 := by
  unfold tailWord_7101545
  simp only [CollatzResearch.WordTrace]
  refine ⟨259014625057322787171402089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172676416704881858114268059 259014625057322787171402089)
  ·
    refine ⟨194260968792992090378551567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259014625057322787171402089 194260968792992090378551567)
    ·
      refine ⟨291391453189488135567827351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194260968792992090378551567 291391453189488135567827351)
      ·
        refine ⟨437087179784232203351741027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291391453189488135567827351 437087179784232203351741027)
        ·
          refine ⟨655630769676348305027611541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437087179784232203351741027 655630769676348305027611541)
          ·
            refine ⟨30732692328578826798169291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 655630769676348305027611541 30732692328578826798169291)
            ·
              refine ⟨46099038492868240197253937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30732692328578826798169291 46099038492868240197253937)
              ·
                refine ⟨34574278869651180147940453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46099038492868240197253937 34574278869651180147940453)
                ·
                  refine ⟨6482677288059596277738835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34574278869651180147940453 6482677288059596277738835)
                  ·
                    refine ⟨9724015932089394416608253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482677288059596277738835 9724015932089394416608253)
                    ·
                      refine ⟨3646505974533522906228095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9724015932089394416608253 3646505974533522906228095)
                      ·
                        rfl

theorem cell23_7101545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_7101545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101545 prefixEnd_7101545 := by exact prefixLift 7101545
  have htrace : WordTrace (prefixWord ++ tailWord_7101545) baseStart_7101545 baseEnd_7101545 := by
    simpa [prefixWord, tailWord_7101545, baseEnd_7101545] using wordTrace_append hprefix tailTrace_7101545
  have hstable : (prefixWord ++ tailWord_7101545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101545).length < 2 ^ (prefixWord ++ tailWord_7101545).sum := by decide
  have hdescent : baseEnd_7101545 < baseStart_7101545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101546 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7101546 : Nat := 118140960795 + 7101546 * 2 ^ 59
def prefixEnd_7101546 : Nat := 4983230072969 + 3 ^ 40 * 7101546 * 2
def baseEnd_7101546 : Nat := 3646506488014177402315591

theorem tailTrace_7101546 : CollatzResearch.WordTrace tailWord_7101546 prefixEnd_7101546 3646506488014177402315591 := by
  unfold tailWord_7101546
  simp only [CollatzResearch.WordTrace]
  refine ⟨64753665382579791085547123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172676441020212776228125661 64753665382579791085547123)
  ·
    refine ⟨97130498073869686628320685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64753665382579791085547123 97130498073869686628320685)
    ·
      refine ⟨36423936777701132485620257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97130498073869686628320685 36423936777701132485620257)
      ·
        refine ⟨27317952583275849364215193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36423936777701132485620257 27317952583275849364215193)
        ·
          refine ⟨20488464437456887023161395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27317952583275849364215193 20488464437456887023161395)
          ·
            refine ⟨30732696656185330534742093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20488464437456887023161395 30732696656185330534742093)
            ·
              refine ⟨11524761246069498950528285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30732696656185330534742093 11524761246069498950528285)
              ·
                refine ⟨4321785467276062106448107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11524761246069498950528285 4321785467276062106448107)
                ·
                  refine ⟨6482678200914093159672161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321785467276062106448107 6482678200914093159672161)
                  ·
                    refine ⟨4862008650685569869754121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482678200914093159672161 4862008650685569869754121)
                    ·
                      refine ⟨3646506488014177402315591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862008650685569869754121 3646506488014177402315591)
                      ·
                        rfl

theorem cell23_7101546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7101546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101546 prefixEnd_7101546 := by exact prefixLift 7101546
  have htrace : WordTrace (prefixWord ++ tailWord_7101546) baseStart_7101546 baseEnd_7101546 := by
    simpa [prefixWord, tailWord_7101546, baseEnd_7101546] using wordTrace_append hprefix tailTrace_7101546
  have hstable : (prefixWord ++ tailWord_7101546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101546).length < 2 ^ (prefixWord ++ tailWord_7101546).sum := by decide
  have hdescent : baseEnd_7101546 < baseStart_7101546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101578 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_7101578 : Nat := 118140960795 + 7101578 * 2 ^ 59
def prefixEnd_7101578 : Nat := 4983230072969 + 3 ^ 40 * 7101578 * 2
def baseEnd_7101578 : Nat := 1215507639798373759038481

theorem tailTrace_7101578 : CollatzResearch.WordTrace tailWord_7101578 prefixEnd_7101578 1215507639798373759038481 := by
  unfold tailWord_7101578
  simp only [CollatzResearch.WordTrace]
  refine ⟨64753957166550808451838347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172677219110802155871568925 64753957166550808451838347)
  ·
    refine ⟨97130935749826212677757521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64753957166550808451838347 97130935749826212677757521)
    ·
      refine ⟨72848201812369659508318141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97130935749826212677757521 72848201812369659508318141)
      ·
        refine ⟨27318075679638622315619303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72848201812369659508318141 27318075679638622315619303)
        ·
          refine ⟨40977113519457933473428955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27318075679638622315619303 40977113519457933473428955)
          ·
            refine ⟨61465670279186900210143433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40977113519457933473428955 61465670279186900210143433)
            ·
              refine ⟨46099252709390175157607575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61465670279186900210143433 46099252709390175157607575)
              ·
                refine ⟨69148879064085262736411363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46099252709390175157607575 69148879064085262736411363)
                ·
                  refine ⟨103723318596127894104617045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69148879064085262736411363 103723318596127894104617045)
                  ·
                    refine ⟨1215507639798373759038481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103723318596127894104617045 1215507639798373759038481)
                    ·
                      rfl

theorem cell23_7101578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_7101578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101578 prefixEnd_7101578 := by exact prefixLift 7101578
  have htrace : WordTrace (prefixWord ++ tailWord_7101578) baseStart_7101578 baseEnd_7101578 := by
    simpa [prefixWord, tailWord_7101578, baseEnd_7101578] using wordTrace_append hprefix tailTrace_7101578
  have hstable : (prefixWord ++ tailWord_7101578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101578).length < 2 ^ (prefixWord ++ tailWord_7101578).sum := by decide
  have hdescent : baseEnd_7101578 < baseStart_7101578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101655 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 2, 5]
def baseStart_7101655 : Nat := 118140960795 + 7101655 * 2 ^ 59
def prefixEnd_7101655 : Nat := 4983230072969 + 3 ^ 40 * 7101655 * 2
def baseEnd_7101655 : Nat := 1215520819135172491950863

theorem tailTrace_7101655 : CollatzResearch.WordTrace tailWord_7101655 prefixEnd_7101655 1215520819135172491950863 := by
  unfold tailWord_7101655
  simp only [CollatzResearch.WordTrace]
  refine ⟨259018637086924275957906419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172679091391282850638604279 259018637086924275957906419)
  ·
    refine ⟨388527955630386413936859629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259018637086924275957906419 388527955630386413936859629)
    ·
      refine ⟨145697983361394905226322361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388527955630386413936859629 145697983361394905226322361)
      ·
        refine ⟨109273487521046178919741771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145697983361394905226322361 109273487521046178919741771)
        ·
          refine ⟨163910231281569268379612657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109273487521046178919741771 163910231281569268379612657)
          ·
            refine ⟨122932673461176951284709493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163910231281569268379612657 122932673461176951284709493)
            ·
              refine ⟨11524938136985339182941515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122932673461176951284709493 11524938136985339182941515)
              ·
                refine ⟨17287407205478008774412273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11524938136985339182941515 17287407205478008774412273)
                ·
                  refine ⟨12965555404108506580809205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17287407205478008774412273 12965555404108506580809205)
                  ·
                    refine ⟨1215520819135172491950863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12965555404108506580809205 1215520819135172491950863)
                    ·
                      rfl

theorem cell23_7101655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_7101655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101655 prefixEnd_7101655 := by exact prefixLift 7101655
  have htrace : WordTrace (prefixWord ++ tailWord_7101655) baseStart_7101655 baseEnd_7101655 := by
    simpa [prefixWord, tailWord_7101655, baseEnd_7101655] using wordTrace_append hprefix tailTrace_7101655
  have hstable : (prefixWord ++ tailWord_7101655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101655).length < 2 ^ (prefixWord ++ tailWord_7101655).sum := by decide
  have hdescent : baseEnd_7101655 < baseStart_7101655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101695 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_7101695 : Nat := 118140960795 + 7101695 * 2 ^ 59
def prefixEnd_7101695 : Nat := 4983230072969 + 3 ^ 40 * 7101695 * 2
def baseEnd_7101695 : Nat := 3646582996631697319352405

theorem tailTrace_7101695 : CollatzResearch.WordTrace tailWord_7101695 prefixEnd_7101695 3646582996631697319352405 := by
  unfold tailWord_7101695
  simp only [CollatzResearch.WordTrace]
  refine ⟨259020096006779362789362539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172680064004519575192908359 259020096006779362789362539)
  ·
    refine ⟨388530144010169044184043809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259020096006779362789362539 388530144010169044184043809)
    ·
      refine ⟨291397608007626783138032857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388530144010169044184043809 291397608007626783138032857)
      ·
        refine ⟨218548206005720087353524643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291397608007626783138032857 218548206005720087353524643)
        ·
          refine ⟨327822309008580131030286965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218548206005720087353524643 327822309008580131030286965)
          ·
            refine ⟨30733341469554387284089403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327822309008580131030286965 30733341469554387284089403)
            ·
              refine ⟨46100012204331580926134105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30733341469554387284089403 46100012204331580926134105)
              ·
                refine ⟨34575009153248685694600579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46100012204331580926134105 34575009153248685694600579)
                ·
                  refine ⟨51862513729873028541900869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34575009153248685694600579 51862513729873028541900869)
                  ·
                    refine ⟨9724221324351192851606413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51862513729873028541900869 9724221324351192851606413)
                    ·
                      refine ⟨3646582996631697319352405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9724221324351192851606413 3646582996631697319352405)
                      ·
                        rfl

theorem cell23_7101695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_7101695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101695 prefixEnd_7101695 := by exact prefixLift 7101695
  have htrace : WordTrace (prefixWord ++ tailWord_7101695) baseStart_7101695 baseEnd_7101695 := by
    simpa [prefixWord, tailWord_7101695, baseEnd_7101695] using wordTrace_append hprefix tailTrace_7101695
  have hstable : (prefixWord ++ tailWord_7101695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101695).length < 2 ^ (prefixWord ++ tailWord_7101695).sum := by decide
  have hdescent : baseEnd_7101695 < baseStart_7101695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101726 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7101726 : Nat := 118140960795 + 7101726 * 2 ^ 59
def prefixEnd_7101726 : Nat := 4983230072969 + 3 ^ 40 * 7101726 * 2
def baseEnd_7101726 : Nat := 3646598914531986698064763

theorem tailTrace_7101726 : CollatzResearch.WordTrace tailWord_7101726 prefixEnd_7101726 3646598914531986698064763 := by
  unfold tailWord_7101726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377653333708381885467629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172680817779778036722494021 32377653333708381885467629)
  ·
    refine ⟨12141620000140643207050361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32377653333708381885467629 12141620000140643207050361)
    ·
      refine ⟨9106215000105482405287771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12141620000140643207050361 9106215000105482405287771)
      ·
        refine ⟨13659322500158223607931657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106215000105482405287771 13659322500158223607931657)
        ·
          refine ⟨10244491875118667705948743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13659322500158223607931657 10244491875118667705948743)
          ·
            refine ⟨15366737812678001558923115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244491875118667705948743 15366737812678001558923115)
            ·
              refine ⟨23050106719017002338384673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366737812678001558923115 23050106719017002338384673)
              ·
                refine ⟨17287580039262751753788505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23050106719017002338384673 17287580039262751753788505)
                ·
                  refine ⟨12965685029447063815341379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17287580039262751753788505 12965685029447063815341379)
                  ·
                    refine ⟨19448527544170595723012069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12965685029447063815341379 19448527544170595723012069)
                    ·
                      refine ⟨3646598914531986698064763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19448527544170595723012069 3646598914531986698064763)
                      ·
                        rfl

theorem cell23_7101726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7101726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101726 prefixEnd_7101726 := by exact prefixLift 7101726
  have htrace : WordTrace (prefixWord ++ tailWord_7101726) baseStart_7101726 baseEnd_7101726 := by
    simpa [prefixWord, tailWord_7101726, baseEnd_7101726] using wordTrace_append hprefix tailTrace_7101726
  have hstable : (prefixWord ++ tailWord_7101726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101726).length < 2 ^ (prefixWord ++ tailWord_7101726).sum := by decide
  have hdescent : baseEnd_7101726 < baseStart_7101726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101749 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 6]
def baseStart_7101749 : Nat := 118140960795 + 7101749 * 2 ^ 59
def prefixEnd_7101749 : Nat := 4983230072969 + 3 ^ 40 * 7101749 * 2
def baseEnd_7101749 : Nat := 405178969398560012008573

theorem tailTrace_7101749 : CollatzResearch.WordTrace tailWord_7101749 prefixEnd_7101749 405178969398560012008573 := by
  unfold tailWord_7101749
  simp only [CollatzResearch.WordTrace]
  refine ⟨259022065548583730011828301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172681377032389153341218867 259022065548583730011828301)
  ·
    refine ⟨97133274580718898754435613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259022065548583730011828301 97133274580718898754435613)
    ·
      refine ⟨36424977967769587032913355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97133274580718898754435613 36424977967769587032913355)
      ·
        refine ⟨54637466951654380549370033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36424977967769587032913355 54637466951654380549370033)
        ·
          refine ⟨40978100213740785412027525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54637466951654380549370033 40978100213740785412027525)
          ·
            refine ⟨7683393790076397264755161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40978100213740785412027525 7683393790076397264755161)
            ·
              refine ⟨5762545342557297948566371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683393790076397264755161 5762545342557297948566371)
              ·
                refine ⟨8643818013835946922849557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762545342557297948566371 8643818013835946922849557)
                ·
                  refine ⟨405178969398560012008573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8643818013835946922849557 405178969398560012008573)
                  ·
                    rfl

theorem cell23_7101749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_7101749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101749 prefixEnd_7101749 := by exact prefixLift 7101749
  have htrace : WordTrace (prefixWord ++ tailWord_7101749) baseStart_7101749 baseEnd_7101749 := by
    simpa [prefixWord, tailWord_7101749, baseEnd_7101749] using wordTrace_append hprefix tailTrace_7101749
  have hstable : (prefixWord ++ tailWord_7101749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101749).length < 2 ^ (prefixWord ++ tailWord_7101749).sum := by decide
  have hdescent : baseEnd_7101749 < baseStart_7101749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101752 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_7101752 : Nat := 118140960795 + 7101752 * 2 ^ 59
def prefixEnd_7101752 : Nat := 4983230072969 + 3 ^ 40 * 7101752 * 2
def baseEnd_7101752 : Nat := 3646612265029003596339643

theorem tailTrace_7101752 : CollatzResearch.WordTrace tailWord_7101752 prefixEnd_7101752 3646612265029003596339643 := by
  unfold tailWord_7101752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129511087483786430762093755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172681449978381907682791673 129511087483786430762093755)
  ·
    refine ⟨194266631225679646143140633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129511087483786430762093755 194266631225679646143140633)
    ·
      refine ⟨145699973419259734607355475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194266631225679646143140633 145699973419259734607355475)
      ·
        refine ⟨218549960128889601911033213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145699973419259734607355475 218549960128889601911033213)
        ·
          refine ⟨81956235048333600716637455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218549960128889601911033213 81956235048333600716637455)
          ·
            refine ⟨122934352572500401074956183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81956235048333600716637455 122934352572500401074956183)
            ·
              refine ⟨184401528858750601612434275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122934352572500401074956183 184401528858750601612434275)
              ·
                refine ⟨276602293288125902418651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184401528858750601612434275 276602293288125902418651413)
                ·
                  refine ⟨12965732497880901675874285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 276602293288125902418651413 12965732497880901675874285)
                  ·
                    refine ⟨4862149686705338128452857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12965732497880901675874285 4862149686705338128452857)
                    ·
                      refine ⟨3646612265029003596339643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862149686705338128452857 3646612265029003596339643)
                      ·
                        rfl

theorem cell23_7101752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_7101752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101752 prefixEnd_7101752 := by exact prefixLift 7101752
  have htrace : WordTrace (prefixWord ++ tailWord_7101752) baseStart_7101752 baseEnd_7101752 := by
    simpa [prefixWord, tailWord_7101752, baseEnd_7101752] using wordTrace_append hprefix tailTrace_7101752
  have hstable : (prefixWord ++ tailWord_7101752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101752).length < 2 ^ (prefixWord ++ tailWord_7101752).sum := by decide
  have hdescent : baseEnd_7101752 < baseStart_7101752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101833 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 1, 1, 4]
def baseStart_7101833 : Nat := 118140960795 + 7101833 * 2 ^ 59
def prefixEnd_7101833 : Nat := 4983230072969 + 3 ^ 40 * 7101833 * 2
def baseEnd_7101833 : Nat := 3646653856962017779426771

theorem tailTrace_7101833 : CollatzResearch.WordTrace tailWord_7101833 prefixEnd_7101833 3646653856962017779426771 := by
  unfold tailWord_7101833
  simp only [CollatzResearch.WordTrace]
  refine ⟨259025129280279412357886153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172683419520186274905257435 259025129280279412357886153)
  ·
    refine ⟨194268846960209559268414615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259025129280279412357886153 194268846960209559268414615)
    ·
      refine ⟨291403270440314338902621923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194268846960209559268414615 291403270440314338902621923)
      ·
        refine ⟨437104905660471508353932885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291403270440314338902621923 437104905660471508353932885)
        ·
          refine ⟨5122323113208650488522651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 437104905660471508353932885 5122323113208650488522651)
          ·
            refine ⟨7683484669812975732783977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122323113208650488522651 7683484669812975732783977)
            ·
              refine ⟨5762613502359731799587983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683484669812975732783977 5762613502359731799587983)
              ·
                refine ⟨8643920253539597699381975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762613502359731799587983 8643920253539597699381975)
                ·
                  refine ⟨12965880380309396549072963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643920253539597699381975 12965880380309396549072963)
                  ·
                    refine ⟨19448820570464094823609445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12965880380309396549072963 19448820570464094823609445)
                    ·
                      refine ⟨3646653856962017779426771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19448820570464094823609445 3646653856962017779426771)
                      ·
                        rfl

theorem cell23_7101833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 1, 4].length) (baseStart_7101833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101833 prefixEnd_7101833 := by exact prefixLift 7101833
  have htrace : WordTrace (prefixWord ++ tailWord_7101833) baseStart_7101833 baseEnd_7101833 := by
    simpa [prefixWord, tailWord_7101833, baseEnd_7101833] using wordTrace_append hprefix tailTrace_7101833
  have hstable : (prefixWord ++ tailWord_7101833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101833).length < 2 ^ (prefixWord ++ tailWord_7101833).sum := by decide
  have hdescent : baseEnd_7101833 < baseStart_7101833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101849 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_7101849 : Nat := 118140960795 + 7101849 * 2 ^ 59
def prefixEnd_7101849 : Nat := 4983230072969 + 3 ^ 40 * 7101849 * 2
def baseEnd_7101849 : Nat := 3646662072652489716826697

theorem tailTrace_7101849 : CollatzResearch.WordTrace tailWord_7101849 prefixEnd_7101849 3646662072652489716826697 := by
  unfold tailWord_7101849
  simp only [CollatzResearch.WordTrace]
  refine ⟨259025712848221447090468601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172683808565480964726979067 259025712848221447090468601)
  ·
    refine ⟨194269284636166085317851451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259025712848221447090468601 194269284636166085317851451)
    ·
      refine ⟨291403926954249127976777177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194269284636166085317851451 291403926954249127976777177)
      ·
        refine ⟨218552945215686845982582883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291403926954249127976777177 218552945215686845982582883)
        ·
          refine ⟨327829417823530268973874325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218552945215686845982582883 327829417823530268973874325)
          ·
            refine ⟨15367003960477981358150359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327829417823530268973874325 15367003960477981358150359)
            ·
              refine ⟨23050505940716972037225539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15367003960477981358150359 23050505940716972037225539)
              ·
                refine ⟨34575758911075458055838309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23050505940716972037225539 34575758911075458055838309)
                ·
                  refine ⟨6482954795826648385469683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34575758911075458055838309 6482954795826648385469683)
                  ·
                    refine ⟨9724432193739972578204525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482954795826648385469683 9724432193739972578204525)
                    ·
                      refine ⟨3646662072652489716826697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9724432193739972578204525 3646662072652489716826697)
                      ·
                        rfl

theorem cell23_7101849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_7101849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101849 prefixEnd_7101849 := by exact prefixLift 7101849
  have htrace : WordTrace (prefixWord ++ tailWord_7101849) baseStart_7101849 baseEnd_7101849 := by
    simpa [prefixWord, tailWord_7101849, baseEnd_7101849] using wordTrace_append hprefix tailTrace_7101849
  have hstable : (prefixWord ++ tailWord_7101849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101849).length < 2 ^ (prefixWord ++ tailWord_7101849).sum := by decide
  have hdescent : baseEnd_7101849 < baseStart_7101849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101875 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_7101875 : Nat := 118140960795 + 7101875 * 2 ^ 59
def prefixEnd_7101875 : Nat := 4983230072969 + 3 ^ 40 * 7101875 * 2
def baseEnd_7101875 : Nat := 3646675423149506615101577

theorem tailTrace_7101875 : CollatzResearch.WordTrace tailWord_7101875 prefixEnd_7101875 3646675423149506615101577 := by
  unfold tailWord_7101875
  simp only [CollatzResearch.WordTrace]
  refine ⟨259026661146127253530915079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172684440764084835687276719 259026661146127253530915079)
  ·
    refine ⟨388539991719190880296372619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259026661146127253530915079 388539991719190880296372619)
    ·
      refine ⟨582809987578786320444558929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388539991719190880296372619 582809987578786320444558929)
      ·
        refine ⟨437107490684089740333419197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582809987578786320444558929 437107490684089740333419197)
        ·
          refine ⟨163915309006533652625032199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437107490684089740333419197 163915309006533652625032199)
          ·
            refine ⟨245872963509800478937548299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163915309006533652625032199 245872963509800478937548299)
            ·
              refine ⟨368809445264700718406322449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245872963509800478937548299 368809445264700718406322449)
              ·
                refine ⟨276607083948525538804741837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 368809445264700718406322449 276607083948525538804741837)
                ·
                  refine ⟨103727656480697077051778189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276607083948525538804741837 103727656480697077051778189)
                  ·
                    refine ⟨38897871180261403894416821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103727656480697077051778189 38897871180261403894416821)
                    ·
                      refine ⟨3646675423149506615101577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38897871180261403894416821 3646675423149506615101577)
                      ·
                        rfl

theorem cell23_7101875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_7101875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101875 prefixEnd_7101875 := by exact prefixLift 7101875
  have htrace : WordTrace (prefixWord ++ tailWord_7101875) baseStart_7101875 baseEnd_7101875 := by
    simpa [prefixWord, tailWord_7101875, baseEnd_7101875] using wordTrace_append hprefix tailTrace_7101875
  have hstable : (prefixWord ++ tailWord_7101875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101875).length < 2 ^ (prefixWord ++ tailWord_7101875).sum := by decide
  have hdescent : baseEnd_7101875 < baseStart_7101875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101890 : List Nat := [3, 5, 2, 1, 2, 1, 9]
def baseStart_7101890 : Nat := 118140960795 + 7101890 * 2 ^ 59
def prefixEnd_7101890 : Nat := 4983230072969 + 3 ^ 40 * 7101890 * 2
def baseEnd_7101890 : Nat := 45020779325423753782889

theorem tailTrace_7101890 : CollatzResearch.WordTrace tailWord_7101890 prefixEnd_7101890 45020779325423753782889 := by
  unfold tailWord_7101890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756802060268227773177781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172684805494048607395140749 64756802060268227773177781)
  ·
    refine ⟨6070950193150146353735417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64756802060268227773177781 6070950193150146353735417)
    ·
      refine ⟨4553212644862609765301563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6070950193150146353735417 4553212644862609765301563)
      ·
        refine ⟨6829818967293914647952345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553212644862609765301563 6829818967293914647952345)
        ·
          refine ⟨5122364225470435985964259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829818967293914647952345 5122364225470435985964259)
          ·
            refine ⟨7683546338205653978946389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122364225470435985964259 7683546338205653978946389)
            ·
              refine ⟨45020779325423753782889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7683546338205653978946389 45020779325423753782889)
              ·
                rfl

theorem cell23_7101890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 9].length) (baseStart_7101890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101890 prefixEnd_7101890 := by exact prefixLift 7101890
  have htrace : WordTrace (prefixWord ++ tailWord_7101890) baseStart_7101890 baseEnd_7101890 := by
    simpa [prefixWord, tailWord_7101890, baseEnd_7101890] using wordTrace_append hprefix tailTrace_7101890
  have hstable : (prefixWord ++ tailWord_7101890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101890).length < 2 ^ (prefixWord ++ tailWord_7101890).sum := by decide
  have hdescent : baseEnd_7101890 < baseStart_7101890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101902 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_7101902 : Nat := 118140960795 + 7101902 * 2 ^ 59
def prefixEnd_7101902 : Nat := 4983230072969 + 3 ^ 40 * 7101902 * 2
def baseEnd_7101902 : Nat := 3646689287127178009463953

theorem tailTrace_7101902 : CollatzResearch.WordTrace tailWord_7101902 prefixEnd_7101902 3646689287127178009463953 := by
  unfold tailWord_7101902
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378455739628679642768495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172685097278019624761431973 32378455739628679642768495)
  ·
    refine ⟨48567683609443019464152743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32378455739628679642768495 48567683609443019464152743)
    ·
      refine ⟨72851525414164529196229115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48567683609443019464152743 72851525414164529196229115)
      ·
        refine ⟨109277288121246793794343673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72851525414164529196229115 109277288121246793794343673)
        ·
          refine ⟨81957966090935095345757755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109277288121246793794343673 81957966090935095345757755)
          ·
            refine ⟨122936949136402643018636633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81957966090935095345757755 122936949136402643018636633)
            ·
              refine ⟨92202711852301982263977475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122936949136402643018636633 92202711852301982263977475)
              ·
                refine ⟨138304067778452973395966213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92202711852301982263977475 138304067778452973395966213)
                ·
                  refine ⟨25932012708459932511743665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138304067778452973395966213 25932012708459932511743665)
                  ·
                    refine ⟨19449009531344949383807749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25932012708459932511743665 19449009531344949383807749)
                    ·
                      refine ⟨3646689287127178009463953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19449009531344949383807749 3646689287127178009463953)
                      ·
                        rfl

theorem cell23_7101902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_7101902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101902 prefixEnd_7101902 := by exact prefixLift 7101902
  have htrace : WordTrace (prefixWord ++ tailWord_7101902) baseStart_7101902 baseEnd_7101902 := by
    simpa [prefixWord, tailWord_7101902, baseEnd_7101902] using wordTrace_append hprefix tailTrace_7101902
  have hstable : (prefixWord ++ tailWord_7101902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101902).length < 2 ^ (prefixWord ++ tailWord_7101902).sum := by decide
  have hdescent : baseEnd_7101902 < baseStart_7101902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101912 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 7]
def baseStart_7101912 : Nat := 118140960795 + 7101912 * 2 ^ 59
def prefixEnd_7101912 : Nat := 4983230072969 + 3 ^ 40 * 7101912 * 2
def baseEnd_7101912 : Nat := 405188269103746996704323

theorem tailTrace_7101912 : CollatzResearch.WordTrace tailWord_7101912 prefixEnd_7101912 405188269103746996704323 := by
  unfold tailWord_7101912
  simp only [CollatzResearch.WordTrace]
  refine ⟨129514005323496604425005995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172685340431328805900007993 129514005323496604425005995)
  ·
    refine ⟨194271007985244906637508993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129514005323496604425005995 194271007985244906637508993)
    ·
      refine ⟨145703255988933679978131745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194271007985244906637508993 145703255988933679978131745)
      ·
        refine ⟨109277441991700259983598809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145703255988933679978131745 109277441991700259983598809)
        ·
          refine ⟨81958081493775194987699107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109277441991700259983598809 81958081493775194987699107)
          ·
            refine ⟨122937122240662792481548661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81958081493775194987699107 122937122240662792481548661)
            ·
              refine ⟨11525355210062136795145187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122937122240662792481548661 11525355210062136795145187)
              ·
                refine ⟨17288032815093205192717781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11525355210062136795145187 17288032815093205192717781)
                ·
                  refine ⟨405188269103746996704323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17288032815093205192717781 405188269103746996704323)
                  ·
                    rfl

theorem cell23_7101912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_7101912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101912 prefixEnd_7101912 := by exact prefixLift 7101912
  have htrace : WordTrace (prefixWord ++ tailWord_7101912) baseStart_7101912 baseEnd_7101912 := by
    simpa [prefixWord, tailWord_7101912, baseEnd_7101912] using wordTrace_append hprefix tailTrace_7101912
  have hstable : (prefixWord ++ tailWord_7101912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101912).length < 2 ^ (prefixWord ++ tailWord_7101912).sum := by decide
  have hdescent : baseEnd_7101912 < baseStart_7101912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101915 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_7101915 : Nat := 118140960795 + 7101915 * 2 ^ 59
def prefixEnd_7101915 : Nat := 4983230072969 + 3 ^ 40 * 7101915 * 2
def baseEnd_7101915 : Nat := 3646695962375686458601393

theorem tailTrace_7101915 : CollatzResearch.WordTrace tailWord_7101915 prefixEnd_7101915 3646695962375686458601393 := by
  unfold tailWord_7101915
  simp only [CollatzResearch.WordTrace]
  refine ⟨259028120065982340362371199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172685413377321560241580799 259028120065982340362371199)
  ·
    refine ⟨388542180098973510543556799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259028120065982340362371199 388542180098973510543556799)
    ·
      refine ⟨582813270148460265815335199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388542180098973510543556799 582813270148460265815335199)
      ·
        refine ⟨874219905222690398723002799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582813270148460265815335199 874219905222690398723002799)
        ·
          refine ⟨1311329857834035598084504199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874219905222690398723002799 1311329857834035598084504199)
          ·
            refine ⟨1966994786751053397126756299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311329857834035598084504199 1966994786751053397126756299)
            ·
              refine ⟨2950492180126580095690134449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966994786751053397126756299 2950492180126580095690134449)
              ·
                refine ⟨2212869135094935071767600837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950492180126580095690134449 2212869135094935071767600837)
                ·
                  refine ⟨414912962830300325956425157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212869135094935071767600837 414912962830300325956425157)
                  ·
                    refine ⟨77796180530681311116829717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 414912962830300325956425157 77796180530681311116829717)
                    ·
                      refine ⟨3646695962375686458601393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77796180530681311116829717 3646695962375686458601393)
                      ·
                        rfl

theorem cell23_7101915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_7101915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101915 prefixEnd_7101915 := by exact prefixLift 7101915
  have htrace : WordTrace (prefixWord ++ tailWord_7101915) baseStart_7101915 baseEnd_7101915 := by
    simpa [prefixWord, tailWord_7101915, baseEnd_7101915] using wordTrace_append hprefix tailTrace_7101915
  have hstable : (prefixWord ++ tailWord_7101915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101915).length < 2 ^ (prefixWord ++ tailWord_7101915).sum := by decide
  have hdescent : baseEnd_7101915 < baseStart_7101915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101923 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7101923 : Nat := 118140960795 + 7101923 * 2 ^ 59
def prefixEnd_7101923 : Nat := 4983230072969 + 3 ^ 40 * 7101923 * 2
def baseEnd_7101923 : Nat := 3646700070220922427301357

theorem tailTrace_7101923 : CollatzResearch.WordTrace tailWord_7101923 prefixEnd_7101923 3646700070220922427301357 := by
  unfold tailWord_7101923
  simp only [CollatzResearch.WordTrace]
  refine ⟨259028411849953357728662423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172685607899968905152441615 259028411849953357728662423)
  ·
    refine ⟨388542617774930036592993635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259028411849953357728662423 388542617774930036592993635)
    ·
      refine ⟨582813926662395054889490453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388542617774930036592993635 582813926662395054889490453)
      ·
        refine ⟨27319402812299768197944865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 582813926662395054889490453 27319402812299768197944865)
        ·
          refine ⟨20489552109224826148458649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27319402812299768197944865 20489552109224826148458649)
          ·
            refine ⟨15367164081918619611343987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20489552109224826148458649 15367164081918619611343987)
            ·
              refine ⟨23050746122877929417015981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15367164081918619611343987 23050746122877929417015981)
              ·
                refine ⟨8644029796079223531380993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23050746122877929417015981 8644029796079223531380993)
                ·
                  refine ⟨6483022347059417648535745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8644029796079223531380993 6483022347059417648535745)
                  ·
                    refine ⟨4862266760294563236401809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483022347059417648535745 4862266760294563236401809)
                    ·
                      refine ⟨3646700070220922427301357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862266760294563236401809 3646700070220922427301357)
                      ·
                        rfl

theorem cell23_7101923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7101923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101923 prefixEnd_7101923 := by exact prefixLift 7101923
  have htrace : WordTrace (prefixWord ++ tailWord_7101923) baseStart_7101923 baseEnd_7101923 := by
    simpa [prefixWord, tailWord_7101923, baseEnd_7101923] using wordTrace_append hprefix tailTrace_7101923
  have hstable : (prefixWord ++ tailWord_7101923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101923).length < 2 ^ (prefixWord ++ tailWord_7101923).sum := by decide
  have hdescent : baseEnd_7101923 < baseStart_7101923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101959 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 2, 5]
def baseStart_7101959 : Nat := 118140960795 + 7101959 * 2 ^ 59
def prefixEnd_7101959 : Nat := 4983230072969 + 3 ^ 40 * 7101959 * 2
def baseEnd_7101959 : Nat := 1215572851841494762150397

theorem tailTrace_7101959 : CollatzResearch.WordTrace tailWord_7101959 prefixEnd_7101959 1215572851841494762150397 := by
  unfold tailWord_7101959
  simp only [CollatzResearch.WordTrace]
  refine ⟨259029724877822935876972931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172686483251881957251315287 259029724877822935876972931)
  ·
    refine ⟨388544587316734403815459397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259029724877822935876972931 388544587316734403815459397)
    ·
      refine ⟨72852110121887700715398637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388544587316734403815459397 72852110121887700715398637)
      ·
        refine ⟨27319541295707887768274489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72852110121887700715398637 27319541295707887768274489)
        ·
          refine ⟨20489655971780915826205867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27319541295707887768274489 20489655971780915826205867)
          ·
            refine ⟨30734483957671373739308801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489655971780915826205867 30734483957671373739308801)
            ·
              refine ⟨23050862968253530304481601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30734483957671373739308801 23050862968253530304481601)
              ·
                refine ⟨17288147226190147728361201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23050862968253530304481601 17288147226190147728361201)
                ·
                  refine ⟨12966110419642610796270901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17288147226190147728361201 12966110419642610796270901)
                  ·
                    refine ⟨1215572851841494762150397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12966110419642610796270901 1215572851841494762150397)
                    ·
                      rfl

theorem cell23_7101959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_7101959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101959 prefixEnd_7101959 := by exact prefixLift 7101959
  have htrace : WordTrace (prefixWord ++ tailWord_7101959) baseStart_7101959 baseEnd_7101959 := by
    simpa [prefixWord, tailWord_7101959, baseEnd_7101959] using wordTrace_append hprefix tailTrace_7101959
  have hstable : (prefixWord ++ tailWord_7101959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101959).length < 2 ^ (prefixWord ++ tailWord_7101959).sum := by decide
  have hdescent : baseEnd_7101959 < baseStart_7101959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7101963 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 5]
def baseStart_7101963 : Nat := 118140960795 + 7101963 * 2 ^ 59
def prefixEnd_7101963 : Nat := 4983230072969 + 3 ^ 40 * 7101963 * 2
def baseEnd_7101963 : Nat := 405191178827455807866797

theorem tailTrace_7101963 : CollatzResearch.WordTrace tailWord_7101963 prefixEnd_7101963 405191178827455807866797 := by
  unfold tailWord_7101963
  simp only [CollatzResearch.WordTrace]
  refine ⟨259029870769808444560118543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172686580513205629706745695 259029870769808444560118543)
  ·
    refine ⟨388544806154712666840177815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259029870769808444560118543 388544806154712666840177815)
    ·
      refine ⟨582817209232069000260266723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388544806154712666840177815 582817209232069000260266723)
      ·
        refine ⟨874225813848103500390400085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582817209232069000260266723 874225813848103500390400085)
        ·
          refine ⟨10244833756032462895200001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 874225813848103500390400085 10244833756032462895200001)
          ·
            refine ⟨7683625317024347171400001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10244833756032462895200001 7683625317024347171400001)
            ·
              refine ⟨5762718987768260378550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683625317024347171400001 5762718987768260378550001)
              ·
                refine ⟨4322039240826195283912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762718987768260378550001 4322039240826195283912501)
                ·
                  refine ⟨405191178827455807866797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4322039240826195283912501 405191178827455807866797)
                  ·
                    rfl

theorem cell23_7101963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 5].length) (baseStart_7101963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7101963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7101963 prefixEnd_7101963 := by exact prefixLift 7101963
  have htrace : WordTrace (prefixWord ++ tailWord_7101963) baseStart_7101963 baseEnd_7101963 := by
    simpa [prefixWord, tailWord_7101963, baseEnd_7101963] using wordTrace_append hprefix tailTrace_7101963
  have hstable : (prefixWord ++ tailWord_7101963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7101963).length < 2 ^ (prefixWord ++ tailWord_7101963).sum := by decide
  have hdescent : baseEnd_7101963 < baseStart_7101963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7101963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102002 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_7102002 : Nat := 118140960795 + 7102002 * 2 ^ 59
def prefixEnd_7102002 : Nat := 4983230072969 + 3 ^ 40 * 7102002 * 2
def baseEnd_7102002 : Nat := 405193403910291957579277

theorem tailTrace_7102002 : CollatzResearch.WordTrace tailWord_7102002 prefixEnd_7102002 405193403910291957579277 := by
  unfold tailWord_7102002
  simp only [CollatzResearch.WordTrace]
  refine ⟨64757823304166788555197065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172687528811111436147192173 64757823304166788555197065)
  ·
    refine ⟨48568367478125091416397799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64757823304166788555197065 48568367478125091416397799)
    ·
      refine ⟨72852551217187637124596699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48568367478125091416397799 72852551217187637124596699)
      ·
        refine ⟨109278826825781455686895049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72852551217187637124596699 109278826825781455686895049)
        ·
          refine ⟨81959120119336091765171287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109278826825781455686895049 81959120119336091765171287)
          ·
            refine ⟨122938680179004137647756931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81959120119336091765171287 122938680179004137647756931)
            ·
              refine ⟨184408020268506206471635397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122938680179004137647756931 184408020268506206471635397)
              ·
                refine ⟨34576503800344913713431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184408020268506206471635397 34576503800344913713431637)
                ·
                  refine ⟨405193403910291957579277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34576503800344913713431637 405193403910291957579277)
                  ·
                    rfl

theorem cell23_7102002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_7102002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102002 prefixEnd_7102002 := by exact prefixLift 7102002
  have htrace : WordTrace (prefixWord ++ tailWord_7102002) baseStart_7102002 baseEnd_7102002 := by
    simpa [prefixWord, tailWord_7102002, baseEnd_7102002] using wordTrace_append hprefix tailTrace_7102002
  have hstable : (prefixWord ++ tailWord_7102002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102002).length < 2 ^ (prefixWord ++ tailWord_7102002).sum := by decide
  have hdescent : baseEnd_7102002 < baseStart_7102002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102036 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 6]
def baseStart_7102036 : Nat := 118140960795 + 7102036 * 2 ^ 59
def prefixEnd_7102036 : Nat := 4983230072969 + 3 ^ 40 * 7102036 * 2
def baseEnd_7102036 : Nat := 405195343726097831687593

theorem tailTrace_7102036 : CollatzResearch.WordTrace tailWord_7102036 prefixEnd_7102036 405195343726097831687593 := by
  unfold tailWord_7102036
  simp only [CollatzResearch.WordTrace]
  refine ⟨129516266649271989013762981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172688355532362652018350641 129516266649271989013762981)
  ·
    refine ⟨24284299996738497940080559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129516266649271989013762981 24284299996738497940080559)
    ·
      refine ⟨36426449995107746910120839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24284299996738497940080559 36426449995107746910120839)
      ·
        refine ⟨54639674992661620365181259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36426449995107746910120839 54639674992661620365181259)
        ·
          refine ⟨81959512488992430547771889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54639674992661620365181259 81959512488992430547771889)
          ·
            refine ⟨61469634366744322910828917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81959512488992430547771889 61469634366744322910828917)
            ·
              refine ⟨5762778221882280272890211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61469634366744322910828917 5762778221882280272890211)
              ·
                refine ⟨8644167332823420409335317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762778221882280272890211 8644167332823420409335317)
                ·
                  refine ⟨405195343726097831687593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8644167332823420409335317 405195343726097831687593)
                  ·
                    rfl

theorem cell23_7102036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_7102036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102036 prefixEnd_7102036 := by exact prefixLift 7102036
  have htrace : WordTrace (prefixWord ++ tailWord_7102036) baseStart_7102036 baseEnd_7102036 := by
    simpa [prefixWord, tailWord_7102036, baseEnd_7102036] using wordTrace_append hprefix tailTrace_7102036
  have hstable : (prefixWord ++ tailWord_7102036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102036).length < 2 ^ (prefixWord ++ tailWord_7102036).sum := by decide
  have hdescent : baseEnd_7102036 < baseStart_7102036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102042 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_7102042 : Nat := 118140960795 + 7102042 * 2 ^ 59
def prefixEnd_7102042 : Nat := 4983230072969 + 3 ^ 40 * 7102042 * 2
def baseEnd_7102042 : Nat := 3646761174418807461713309

theorem tailTrace_7102042 : CollatzResearch.WordTrace tailWord_7102042 prefixEnd_7102042 3646761174418807461713309 := by
  unfold tailWord_7102042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64758188034130560263061095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172688501424348160701496253 64758188034130560263061095)
  ·
    refine ⟨97137282051195840394591643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64758188034130560263061095 97137282051195840394591643)
    ·
      refine ⟨145705923076793760591887465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97137282051195840394591643 145705923076793760591887465)
      ·
        refine ⟨109279442307595320443915599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145705923076793760591887465 109279442307595320443915599)
        ·
          refine ⟨163919163461392980665873399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109279442307595320443915599 163919163461392980665873399)
          ·
            refine ⟨245878745192089470998810099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163919163461392980665873399 245878745192089470998810099)
            ·
              refine ⟨368818117788134206498215149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245878745192089470998810099 368818117788134206498215149)
              ·
                refine ⟨138306794170550327436830681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368818117788134206498215149 138306794170550327436830681)
                ·
                  refine ⟨103730095627912745577623011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138306794170550327436830681 103730095627912745577623011)
                  ·
                    refine ⟨155595143441869118366434517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103730095627912745577623011 155595143441869118366434517)
                    ·
                      refine ⟨3646761174418807461713309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155595143441869118366434517 3646761174418807461713309)
                      ·
                        rfl

theorem cell23_7102042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_7102042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102042 prefixEnd_7102042 := by exact prefixLift 7102042
  have htrace : WordTrace (prefixWord ++ tailWord_7102042) baseStart_7102042 baseEnd_7102042 := by
    simpa [prefixWord, tailWord_7102042, baseEnd_7102042] using wordTrace_append hprefix tailTrace_7102042
  have hstable : (prefixWord ++ tailWord_7102042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102042).length < 2 ^ (prefixWord ++ tailWord_7102042).sum := by decide
  have hdescent : baseEnd_7102042 < baseStart_7102042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102066 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_7102066 : Nat := 118140960795 + 7102066 * 2 ^ 59
def prefixEnd_7102066 : Nat := 4983230072969 + 3 ^ 40 * 7102066 * 2
def baseEnd_7102066 : Nat := 1215591165984838455937733

theorem tailTrace_7102066 : CollatzResearch.WordTrace tailWord_7102066 prefixEnd_7102066 1215591165984838455937733 := by
  unfold tailWord_7102066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64758406872108823287779513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172689084992290195434078701 64758406872108823287779513)
  ·
    refine ⟨48568805154081617465834635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64758406872108823287779513 48568805154081617465834635)
    ·
      refine ⟨72853207731122426198751953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48568805154081617465834635 72853207731122426198751953)
      ·
        refine ⟨54639905798341819649063965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72853207731122426198751953 54639905798341819649063965)
        ·
          refine ⟨20489964674378182368398987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54639905798341819649063965 20489964674378182368398987)
          ·
            refine ⟨30734947011567273552598481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489964674378182368398987 30734947011567273552598481)
            ·
              refine ⟨23051210258675455164448861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30734947011567273552598481 23051210258675455164448861)
              ·
                refine ⟨8644203847003295686668323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23051210258675455164448861 8644203847003295686668323)
                ·
                  refine ⟨12966305770504943530002485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644203847003295686668323 12966305770504943530002485)
                  ·
                    refine ⟨1215591165984838455937733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12966305770504943530002485 1215591165984838455937733)
                    ·
                      rfl

theorem cell23_7102066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_7102066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102066 prefixEnd_7102066 := by exact prefixLift 7102066
  have htrace : WordTrace (prefixWord ++ tailWord_7102066) baseStart_7102066 baseEnd_7102066 := by
    simpa [prefixWord, tailWord_7102066, baseEnd_7102066] using wordTrace_append hprefix tailTrace_7102066
  have hstable : (prefixWord ++ tailWord_7102066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102066).length < 2 ^ (prefixWord ++ tailWord_7102066).sum := by decide
  have hdescent : baseEnd_7102066 < baseStart_7102066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102080 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 1, 1, 3]
def baseStart_7102080 : Nat := 118140960795 + 7102080 * 2 ^ 59
def prefixEnd_7102080 : Nat := 4983230072969 + 3 ^ 40 * 7102080 * 2
def baseEnd_7102080 : Nat := 3646780686683678313038135

theorem tailTrace_7102080 : CollatzResearch.WordTrace tailWord_7102080 prefixEnd_7102080 3646780686683678313038135 := by
  unfold tailWord_7102080
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517069055192286771063847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172689425406923049028085129 129517069055192286771063847)
  ·
    refine ⟨194275603582788430156595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129517069055192286771063847 194275603582788430156595771)
    ·
      refine ⟨291413405374182645234893657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194275603582788430156595771 291413405374182645234893657)
      ·
        refine ⟨218560054030636983926170243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291413405374182645234893657 218560054030636983926170243)
        ·
          refine ⟨327840081045955475889255365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218560054030636983926170243 327840081045955475889255365)
          ·
            refine ⟨61470015196116651729235381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327840081045955475889255365 61470015196116651729235381)
            ·
              refine ⟨5762813924635936099615817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61470015196116651729235381 5762813924635936099615817)
              ·
                refine ⟨4322110443476952074711863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762813924635936099615817 4322110443476952074711863)
                ·
                  refine ⟨6483165665215428112067795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322110443476952074711863 6483165665215428112067795)
                  ·
                    refine ⟨9724748497823142168101693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483165665215428112067795 9724748497823142168101693)
                    ·
                      refine ⟨3646780686683678313038135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9724748497823142168101693 3646780686683678313038135)
                      ·
                        rfl

theorem cell23_7102080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_7102080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102080 prefixEnd_7102080 := by exact prefixLift 7102080
  have htrace : WordTrace (prefixWord ++ tailWord_7102080) baseStart_7102080 baseEnd_7102080 := by
    simpa [prefixWord, tailWord_7102080, baseEnd_7102080] using wordTrace_append hprefix tailTrace_7102080
  have hstable : (prefixWord ++ tailWord_7102080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102080).length < 2 ^ (prefixWord ++ tailWord_7102080).sum := by decide
  have hdescent : baseEnd_7102080 < baseStart_7102080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102089 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_7102089 : Nat := 118140960795 + 7102089 * 2 ^ 59
def prefixEnd_7102089 : Nat := 4983230072969 + 3 ^ 40 * 7102089 * 2
def baseEnd_7102089 : Nat := 3646785308009568777825593

theorem tailTrace_7102089 : CollatzResearch.WordTrace tailWord_7102089 prefixEnd_7102089 3646785308009568777825593 := by
  unfold tailWord_7102089
  simp only [CollatzResearch.WordTrace]
  refine ⟨259034466367351968079205321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172689644244901312052803547 259034466367351968079205321)
  ·
    refine ⟨194275849775513976059403991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259034466367351968079205321 194275849775513976059403991)
    ·
      refine ⟨291413774663270964089105987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194275849775513976059403991 291413774663270964089105987)
      ·
        refine ⟨437120661994906446133658981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291413774663270964089105987 437120661994906446133658981)
        ·
          refine ⟨81960124124044958650061059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437120661994906446133658981 81960124124044958650061059)
          ·
            refine ⟨122940186186067437975091589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81960124124044958650061059 122940186186067437975091589)
            ·
              refine ⟨23051284909887644620329673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122940186186067437975091589 23051284909887644620329673)
              ·
                refine ⟨17288463682415733465247255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23051284909887644620329673 17288463682415733465247255)
                ·
                  refine ⟨25932695523623600197870883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17288463682415733465247255 25932695523623600197870883)
                  ·
                    refine ⟨38899043285435400296806325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25932695523623600197870883 38899043285435400296806325)
                    ·
                      refine ⟨3646785308009568777825593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38899043285435400296806325 3646785308009568777825593)
                      ·
                        rfl

theorem cell23_7102089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_7102089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102089 prefixEnd_7102089 := by exact prefixLift 7102089
  have htrace : WordTrace (prefixWord ++ tailWord_7102089) baseStart_7102089 baseEnd_7102089 := by
    simpa [prefixWord, tailWord_7102089, baseEnd_7102089] using wordTrace_append hprefix tailTrace_7102089
  have hstable : (prefixWord ++ tailWord_7102089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102089).length < 2 ^ (prefixWord ++ tailWord_7102089).sum := by decide
  have hdescent : baseEnd_7102089 < baseStart_7102089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102100 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_7102100 : Nat := 118140960795 + 7102100 * 2 ^ 59
def prefixEnd_7102100 : Nat := 4983230072969 + 3 ^ 40 * 7102100 * 2
def baseEnd_7102100 : Nat := 1215596985432256078262681

theorem tailTrace_7102100 : CollatzResearch.WordTrace tailWord_7102100 prefixEnd_7102100 1215596985432256078262681 := by
  unfold tailWord_7102100
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517433785156058478927877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172689911713541411305237169 129517433785156058478927877)
  ·
    refine ⟨24284518834716760964798977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129517433785156058478927877 24284518834716760964798977)
    ·
      refine ⟨18213389126037570723599233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24284518834716760964798977 18213389126037570723599233)
      ·
        refine ⟨13660041844528178042699425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18213389126037570723599233 13660041844528178042699425)
        ·
          refine ⟨10245031383396133532024569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13660041844528178042699425 10245031383396133532024569)
          ·
            refine ⟨7683773537547100149018427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10245031383396133532024569 7683773537547100149018427)
            ·
              refine ⟨11525660306320650223527641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683773537547100149018427 11525660306320650223527641)
              ·
                refine ⟨8644245229740487667645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11525660306320650223527641 8644245229740487667645731)
                ·
                  refine ⟨12966367844610731501468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644245229740487667645731 12966367844610731501468597)
                  ·
                    refine ⟨1215596985432256078262681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12966367844610731501468597 1215596985432256078262681)
                    ·
                      rfl

theorem cell23_7102100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_7102100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102100 prefixEnd_7102100 := by exact prefixLift 7102100
  have htrace : WordTrace (prefixWord ++ tailWord_7102100) baseStart_7102100 baseEnd_7102100 := by
    simpa [prefixWord, tailWord_7102100, baseEnd_7102100] using wordTrace_append hprefix tailTrace_7102100
  have hstable : (prefixWord ++ tailWord_7102100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102100).length < 2 ^ (prefixWord ++ tailWord_7102100).sum := by decide
  have hdescent : baseEnd_7102100 < baseStart_7102100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102103 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_7102103 : Nat := 118140960795 + 7102103 * 2 ^ 59
def prefixEnd_7102103 : Nat := 4983230072969 + 3 ^ 40 * 7102103 * 2
def baseEnd_7102103 : Nat := 3646792496738731723050529

theorem tailTrace_7102103 : CollatzResearch.WordTrace tailWord_7102103 prefixEnd_7102103 3646792496738731723050529 := by
  unfold tailWord_7102103
  simp only [CollatzResearch.WordTrace]
  refine ⟨259034976989301248470214963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172689984659534165646809975 259034976989301248470214963)
  ·
    refine ⟨388552465483951872705322445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259034976989301248470214963 388552465483951872705322445)
    ·
      refine ⟨145707174556481952264495917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388552465483951872705322445 145707174556481952264495917)
      ·
        refine ⟨54640190458680732099185969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145707174556481952264495917 54640190458680732099185969)
        ·
          refine ⟨40980142844010549074389477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54640190458680732099185969 40980142844010549074389477)
          ·
            refine ⟨7683776783251977951448027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40980142844010549074389477 7683776783251977951448027)
            ·
              refine ⟨11525665174877966927172041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7683776783251977951448027 11525665174877966927172041)
              ·
                refine ⟨8644248881158475195379031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11525665174877966927172041 8644248881158475195379031)
                ·
                  refine ⟨12966373321737712793068547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644248881158475195379031 12966373321737712793068547)
                  ·
                    refine ⟨19449559982606569189602821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12966373321737712793068547 19449559982606569189602821)
                    ·
                      refine ⟨3646792496738731723050529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19449559982606569189602821 3646792496738731723050529)
                      ·
                        rfl

theorem cell23_7102103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_7102103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102103 prefixEnd_7102103 := by exact prefixLift 7102103
  have htrace : WordTrace (prefixWord ++ tailWord_7102103) baseStart_7102103 baseEnd_7102103 := by
    simpa [prefixWord, tailWord_7102103, baseEnd_7102103] using wordTrace_append hprefix tailTrace_7102103
  have hstable : (prefixWord ++ tailWord_7102103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102103).length < 2 ^ (prefixWord ++ tailWord_7102103).sum := by decide
  have hdescent : baseEnd_7102103 < baseStart_7102103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102116 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_7102116 : Nat := 118140960795 + 7102116 * 2 ^ 59
def prefixEnd_7102116 : Nat := 4983230072969 + 3 ^ 40 * 7102116 * 2
def baseEnd_7102116 : Nat := 3646799171987240172187969

theorem tailTrace_7102116 : CollatzResearch.WordTrace tailWord_7102116 prefixEnd_7102116 3646799171987240172187969 := by
  unfold tailWord_7102116
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517725569127075845219101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172690300758836101126958801 129517725569127075845219101)
  ·
    refine ⟨48569147088422653441957163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129517725569127075845219101 48569147088422653441957163)
    ·
      refine ⟨72853720632633980162935745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48569147088422653441957163 72853720632633980162935745)
      ·
        refine ⟨54640290474475485122201809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72853720632633980162935745 54640290474475485122201809)
        ·
          refine ⟨40980217855856613841651357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54640290474475485122201809 40980217855856613841651357)
          ·
            refine ⟨15367581695946230190619259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40980217855856613841651357 15367581695946230190619259)
            ·
              refine ⟨23051372543919345285928889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15367581695946230190619259 23051372543919345285928889)
              ·
                refine ⟨17288529407939508964446667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23051372543919345285928889 17288529407939508964446667)
                ·
                  refine ⟨25932794111909263446670001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17288529407939508964446667 25932794111909263446670001)
                  ·
                    refine ⟨19449595583931947585002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25932794111909263446670001 19449595583931947585002501)
                    ·
                      refine ⟨3646799171987240172187969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19449595583931947585002501 3646799171987240172187969)
                      ·
                        rfl

theorem cell23_7102116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_7102116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102116 prefixEnd_7102116 := by exact prefixLift 7102116
  have htrace : WordTrace (prefixWord ++ tailWord_7102116) baseStart_7102116 baseEnd_7102116 := by
    simpa [prefixWord, tailWord_7102116, baseEnd_7102116] using wordTrace_append hprefix tailTrace_7102116
  have hstable : (prefixWord ++ tailWord_7102116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102116).length < 2 ^ (prefixWord ++ tailWord_7102116).sum := by decide
  have hdescent : baseEnd_7102116 < baseStart_7102116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102126 : List Nat := [4, 1, 4, 1, 2, 11]
def baseStart_7102126 : Nat := 118140960795 + 7102126 * 2 ^ 59
def prefixEnd_7102126 : Nat := 4983230072969 + 3 ^ 40 * 7102126 * 2
def baseEnd_7102126 : Nat := 15007425130838621946761

theorem tailTrace_7102126 : CollatzResearch.WordTrace tailWord_7102126 prefixEnd_7102126 15007425130838621946761 := by
  unfold tailWord_7102126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379476983527240424787779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172690543912145282265534821 32379476983527240424787779)
  ·
    refine ⟨48569215475290860637181669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32379476983527240424787779 48569215475290860637181669)
    ·
      refine ⟨9106727901617036369471563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48569215475290860637181669 9106727901617036369471563)
      ·
        refine ⟨13660091852425554554207345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106727901617036369471563 13660091852425554554207345)
        ·
          refine ⟨10245068889319165915655509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13660091852425554554207345 10245068889319165915655509)
          ·
            refine ⟨15007425130838621946761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10245068889319165915655509 15007425130838621946761)
            ·
              rfl

theorem cell23_7102126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 11].length) (baseStart_7102126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102126 prefixEnd_7102126 := by exact prefixLift 7102126
  have htrace : WordTrace (prefixWord ++ tailWord_7102126) baseStart_7102126 baseEnd_7102126 := by
    simpa [prefixWord, tailWord_7102126, baseEnd_7102126] using wordTrace_append hprefix tailTrace_7102126
  have hstable : (prefixWord ++ tailWord_7102126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102126).length < 2 ^ (prefixWord ++ tailWord_7102126).sum := by decide
  have hdescent : baseEnd_7102126 < baseStart_7102126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102136 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_7102136 : Nat := 118140960795 + 7102136 * 2 ^ 59
def prefixEnd_7102136 : Nat := 4983230072969 + 3 ^ 40 * 7102136 * 2
def baseEnd_7102136 : Nat := 3646809441600330093937877

theorem tailTrace_7102136 : CollatzResearch.WordTrace tailWord_7102136 prefixEnd_7102136 3646809441600330093937877 := by
  unfold tailWord_7102136
  simp only [CollatzResearch.WordTrace]
  refine ⟨129518090299090847553083131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172690787065454463404110841 129518090299090847553083131)
  ·
    refine ⟨194277135448636271329624697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129518090299090847553083131 194277135448636271329624697)
    ·
      refine ⟨145707851586477203497218523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194277135448636271329624697 145707851586477203497218523)
      ·
        refine ⟨218561777379715805245827785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145707851586477203497218523 218561777379715805245827785)
        ·
          refine ⟨163921333034786853934370839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218561777379715805245827785 163921333034786853934370839)
          ·
            refine ⟨245881999552180280901556259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163921333034786853934370839 245881999552180280901556259)
            ·
              refine ⟨368822999328270421352334389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245881999552180280901556259 368822999328270421352334389)
              ·
                refine ⟨34577156187025352001781349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368822999328270421352334389 34577156187025352001781349)
                ·
                  refine ⟨6483216785067253500334003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34577156187025352001781349 6483216785067253500334003)
                  ·
                    refine ⟨9724825177600880250501005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483216785067253500334003 9724825177600880250501005)
                    ·
                      refine ⟨3646809441600330093937877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9724825177600880250501005 3646809441600330093937877)
                      ·
                        rfl

theorem cell23_7102136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_7102136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102136 prefixEnd_7102136 := by exact prefixLift 7102136
  have htrace : WordTrace (prefixWord ++ tailWord_7102136) baseStart_7102136 baseEnd_7102136 := by
    simpa [prefixWord, tailWord_7102136, baseEnd_7102136] using wordTrace_append hprefix tailTrace_7102136
  have hstable : (prefixWord ++ tailWord_7102136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102136).length < 2 ^ (prefixWord ++ tailWord_7102136).sum := by decide
  have hdescent : baseEnd_7102136 < baseStart_7102136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102137 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7102137 : Nat := 118140960795 + 7102137 * 2 ^ 59
def prefixEnd_7102137 : Nat := 4983230072969 + 3 ^ 40 * 7102137 * 2
def baseEnd_7102137 : Nat := 3646809955080984590025373

theorem tailTrace_7102137 : CollatzResearch.WordTrace tailWord_7102137 prefixEnd_7102137 3646809955080984590025373 := by
  unfold tailWord_7102137
  simp only [CollatzResearch.WordTrace]
  refine ⟨259036217071178072276952665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172690811380785381517968443 259036217071178072276952665)
  ·
    refine ⟨194277162803383554207714499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259036217071178072276952665 194277162803383554207714499)
    ·
      refine ⟨291415744205075331311571749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194277162803383554207714499 291415744205075331311571749)
      ·
        refine ⟨54640452038451624620919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291415744205075331311571749 54640452038451624620919703)
        ·
          refine ⟨81960678057677436931379555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54640452038451624620919703 81960678057677436931379555)
          ·
            refine ⟨122941017086516155397069333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81960678057677436931379555 122941017086516155397069333)
            ·
              refine ⟨5762860175930444784237625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122941017086516155397069333 5762860175930444784237625)
              ·
                refine ⟨4322145131947833588178219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762860175930444784237625 4322145131947833588178219)
                ·
                  refine ⟨6483217697921750382267329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322145131947833588178219 6483217697921750382267329)
                  ·
                    refine ⟨4862413273441312786700497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483217697921750382267329 4862413273441312786700497)
                    ·
                      refine ⟨3646809955080984590025373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862413273441312786700497 3646809955080984590025373)
                      ·
                        rfl

theorem cell23_7102137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7102137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102137 prefixEnd_7102137 := by exact prefixLift 7102137
  have htrace : WordTrace (prefixWord ++ tailWord_7102137) baseStart_7102137 baseEnd_7102137 := by
    simpa [prefixWord, tailWord_7102137, baseEnd_7102137] using wordTrace_append hprefix tailTrace_7102137
  have hstable : (prefixWord ++ tailWord_7102137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102137).length < 2 ^ (prefixWord ++ tailWord_7102137).sum := by decide
  have hdescent : baseEnd_7102137 < baseStart_7102137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102150 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7102150 : Nat := 118140960795 + 7102150 * 2 ^ 59
def prefixEnd_7102150 : Nat := 4983230072969 + 3 ^ 40 * 7102150 * 2
def baseEnd_7102150 : Nat := 3646816630329493039162813

theorem tailTrace_7102150 : CollatzResearch.WordTrace tailWord_7102150 prefixEnd_7102150 3646816630329493039162813 := by
  unfold tailWord_7102150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094896600629092984286747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172691127480087316998117269 8094896600629092984286747)
  ·
    refine ⟨12142344900943639476430121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8094896600629092984286747 12142344900943639476430121)
    ·
      refine ⟨9106758675707729607322591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12142344900943639476430121 9106758675707729607322591)
      ·
        refine ⟨13660138013561594410983887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106758675707729607322591 13660138013561594410983887)
        ·
          refine ⟨20490207020342391616475831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13660138013561594410983887 20490207020342391616475831)
          ·
            refine ⟨30735310530513587424713747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20490207020342391616475831 30735310530513587424713747)
            ·
              refine ⟨46102965795770381137070621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30735310530513587424713747 46102965795770381137070621)
              ·
                refine ⟨17288612173413892926401483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46102965795770381137070621 17288612173413892926401483)
                ·
                  refine ⟨25932918260120839389602225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17288612173413892926401483 25932918260120839389602225)
                  ·
                    refine ⟨19449688695090629542201669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25932918260120839389602225 19449688695090629542201669)
                    ·
                      refine ⟨3646816630329493039162813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19449688695090629542201669 3646816630329493039162813)
                      ·
                        rfl

theorem cell23_7102150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7102150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102150 prefixEnd_7102150 := by exact prefixLift 7102150
  have htrace : WordTrace (prefixWord ++ tailWord_7102150) baseStart_7102150 baseEnd_7102150 := by
    simpa [prefixWord, tailWord_7102150, baseEnd_7102150] using wordTrace_append hprefix tailTrace_7102150
  have hstable : (prefixWord ++ tailWord_7102150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102150).length < 2 ^ (prefixWord ++ tailWord_7102150).sum := by decide
  have hdescent : baseEnd_7102150 < baseStart_7102150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102199 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 7]
def baseStart_7102199 : Nat := 118140960795 + 7102199 * 2 ^ 59
def prefixEnd_7102199 : Nat := 4983230072969 + 3 ^ 40 * 7102199 * 2
def baseEnd_7102199 : Nat := 405204643431284816383343

theorem tailTrace_7102199 : CollatzResearch.WordTrace tailWord_7102199 prefixEnd_7102199 405204643431284816383343 := by
  unfold tailWord_7102199
  simp only [CollatzResearch.WordTrace]
  refine ⟨259038478396953456865709651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172692318931302304577139767 259038478396953456865709651)
  ·
    refine ⟨388557717595430185298564477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259038478396953456865709651 388557717595430185298564477)
    ·
      refine ⟨145709144098286319486961679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388557717595430185298564477 145709144098286319486961679)
      ·
        refine ⟨218563716147429479230442519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145709144098286319486961679 218563716147429479230442519)
        ·
          refine ⟨327845574221144218845663779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218563716147429479230442519 327845574221144218845663779)
          ·
            refine ⟨491768361331716328268495669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327845574221144218845663779 491768361331716328268495669)
            ·
              refine ⟨46103283874848405775171469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491768361331716328268495669 46103283874848405775171469)
              ·
                refine ⟨17288731453068152165689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46103283874848405775171469 17288731453068152165689301)
                ·
                  refine ⟨405204643431284816383343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17288731453068152165689301 405204643431284816383343)
                  ·
                    rfl

theorem cell23_7102199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 7].length) (baseStart_7102199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102199 prefixEnd_7102199 := by exact prefixLift 7102199
  have htrace : WordTrace (prefixWord ++ tailWord_7102199) baseStart_7102199 baseEnd_7102199 := by
    simpa [prefixWord, tailWord_7102199, baseEnd_7102199] using wordTrace_append hprefix tailTrace_7102199
  have hstable : (prefixWord ++ tailWord_7102199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102199).length < 2 ^ (prefixWord ++ tailWord_7102199).sum := by decide
  have hdescent : baseEnd_7102199 < baseStart_7102199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102261 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_7102261 : Nat := 118140960795 + 7102261 * 2 ^ 59
def prefixEnd_7102261 : Nat := 4983230072969 + 3 ^ 40 * 7102261 * 2
def baseEnd_7102261 : Nat := 3646873626682142104874803

theorem tailTrace_7102261 : CollatzResearch.WordTrace tailWord_7102261 prefixEnd_7102261 3646873626682142104874803 := by
  unfold tailWord_7102261
  simp only [CollatzResearch.WordTrace]
  refine ⟨259040739722728841454466637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172693826481819227636311091 259040739722728841454466637)
  ·
    refine ⟨97140277396023315545424989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259040739722728841454466637 97140277396023315545424989)
    ·
      refine ⟨36427604023508743329534371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97140277396023315545424989 36427604023508743329534371)
      ·
        refine ⟨54641406035263114994301557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36427604023508743329534371 54641406035263114994301557)
        ·
          refine ⟨5122631815805917030715771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54641406035263114994301557 5122631815805917030715771)
          ·
            refine ⟨7683947723708875546073657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122631815805917030715771 7683947723708875546073657)
            ·
              refine ⟨5762960792781656659555243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683947723708875546073657 5762960792781656659555243)
              ·
                refine ⟨8644441189172484989332865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762960792781656659555243 8644441189172484989332865)
                ·
                  refine ⟨6483330891879363741999649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8644441189172484989332865 6483330891879363741999649)
                  ·
                    refine ⟨4862498168909522806499737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483330891879363741999649 4862498168909522806499737)
                    ·
                      refine ⟨3646873626682142104874803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862498168909522806499737 3646873626682142104874803)
                      ·
                        rfl

theorem cell23_7102261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_7102261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102261 prefixEnd_7102261 := by exact prefixLift 7102261
  have htrace : WordTrace (prefixWord ++ tailWord_7102261) baseStart_7102261 baseEnd_7102261 := by
    simpa [prefixWord, tailWord_7102261, baseEnd_7102261] using wordTrace_append hprefix tailTrace_7102261
  have hstable : (prefixWord ++ tailWord_7102261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102261).length < 2 ^ (prefixWord ++ tailWord_7102261).sum := by decide
  have hdescent : baseEnd_7102261 < baseStart_7102261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102299 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_7102299 : Nat := 118140960795 + 7102299 * 2 ^ 59
def prefixEnd_7102299 : Nat := 4983230072969 + 3 ^ 40 * 7102299 * 2
def baseEnd_7102299 : Nat := 3646893138947012956199627

theorem tailTrace_7102299 : CollatzResearch.WordTrace tailWord_7102299 prefixEnd_7102299 3646893138947012956199627 := by
  unfold tailWord_7102299
  simp only [CollatzResearch.WordTrace]
  refine ⟨259042125696591173944349951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172694750464394115962899967 259042125696591173944349951)
  ·
    refine ⟨388563188544886760916524927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259042125696591173944349951 388563188544886760916524927)
    ·
      refine ⟨582844782817330141374787391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388563188544886760916524927 582844782817330141374787391)
      ·
        refine ⟨874267174225995212062181087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582844782817330141374787391 874267174225995212062181087)
        ·
          refine ⟨1311400761338992818093271631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874267174225995212062181087 1311400761338992818093271631)
          ·
            refine ⟨1967101142008489227139907447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311400761338992818093271631 1967101142008489227139907447)
            ·
              refine ⟨2950651713012733840709861171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967101142008489227139907447 2950651713012733840709861171)
              ·
                refine ⟨4425977569519100761064791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950651713012733840709861171 4425977569519100761064791757)
                ·
                  refine ⟨1659741588569662785399296909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4425977569519100761064791757 1659741588569662785399296909)
                  ·
                    refine ⟨622403095713623544524736341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1659741588569662785399296909 622403095713623544524736341)
                    ·
                      refine ⟨3646893138947012956199627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 622403095713623544524736341 3646893138947012956199627)
                      ·
                        rfl

theorem cell23_7102299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_7102299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102299 prefixEnd_7102299 := by exact prefixLift 7102299
  have htrace : WordTrace (prefixWord ++ tailWord_7102299) baseStart_7102299 baseEnd_7102299 := by
    simpa [prefixWord, tailWord_7102299, baseEnd_7102299] using wordTrace_append hprefix tailTrace_7102299
  have hstable : (prefixWord ++ tailWord_7102299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102299).length < 2 ^ (prefixWord ++ tailWord_7102299).sum := by decide
  have hdescent : baseEnd_7102299 < baseStart_7102299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102303 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_7102303 : Nat := 118140960795 + 7102303 * 2 ^ 59
def prefixEnd_7102303 : Nat := 4983230072969 + 3 ^ 40 * 7102303 * 2
def baseEnd_7102303 : Nat := 3646895192869630940549609

theorem tailTrace_7102303 : CollatzResearch.WordTrace tailWord_7102303 prefixEnd_7102303 3646895192869630940549609 := by
  unfold tailWord_7102303
  simp only [CollatzResearch.WordTrace]
  refine ⟨259042271588576682627495563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172694847725717788418330375 259042271588576682627495563)
  ·
    refine ⟨388563407382865023941243345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259042271588576682627495563 388563407382865023941243345)
    ·
      refine ⟨291422555537148767955932509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388563407382865023941243345 291422555537148767955932509)
      ·
        refine ⟨109283458326430787983474691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291422555537148767955932509 109283458326430787983474691)
        ·
          refine ⟨163925187489646181975212037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109283458326430787983474691 163925187489646181975212037)
          ·
            refine ⟨30735972654308659120352257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163925187489646181975212037 30735972654308659120352257)
            ·
              refine ⟨23051979490731494340264193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30735972654308659120352257 23051979490731494340264193)
              ·
                refine ⟨17288984618048620755198145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23051979490731494340264193 17288984618048620755198145)
                ·
                  refine ⟨12966738463536465566398609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17288984618048620755198145 12966738463536465566398609)
                  ·
                    refine ⟨9725053847652349174798957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12966738463536465566398609 9725053847652349174798957)
                    ·
                      refine ⟨3646895192869630940549609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725053847652349174798957 3646895192869630940549609)
                      ·
                        rfl

theorem cell23_7102303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_7102303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102303 prefixEnd_7102303 := by exact prefixLift 7102303
  have htrace : WordTrace (prefixWord ++ tailWord_7102303) baseStart_7102303 baseEnd_7102303 := by
    simpa [prefixWord, tailWord_7102303, baseEnd_7102303] using wordTrace_append hprefix tailTrace_7102303
  have hstable : (prefixWord ++ tailWord_7102303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102303).length < 2 ^ (prefixWord ++ tailWord_7102303).sum := by decide
  have hdescent : baseEnd_7102303 < baseStart_7102303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102336 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_7102336 : Nat := 118140960795 + 7102336 * 2 ^ 59
def prefixEnd_7102336 : Nat := 4983230072969 + 3 ^ 40 * 7102336 * 2
def baseEnd_7102336 : Nat := 1215637379243743103812319

theorem tailTrace_7102336 : CollatzResearch.WordTrace tailWord_7102336 prefixEnd_7102336 1215637379243743103812319 := by
  unfold tailWord_7102336
  simp only [CollatzResearch.WordTrace]
  refine ⟨129521737598728564631723431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172695650131638086175631241 129521737598728564631723431)
  ·
    refine ⟨194282606398092846947585147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129521737598728564631723431 194282606398092846947585147)
    ·
      refine ⟨291423909597139270421377721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194282606398092846947585147 291423909597139270421377721)
      ·
        refine ⟨218567932197854452816033291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291423909597139270421377721 218567932197854452816033291)
        ·
          refine ⟨327851898296781679224049937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218567932197854452816033291 327851898296781679224049937)
          ·
            refine ⟨245888923722586259418037453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327851898296781679224049937 245888923722586259418037453)
            ·
              refine ⟨92208346395969847281764045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245888923722586259418037453 92208346395969847281764045)
              ·
                refine ⟨34578129898488692730661517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92208346395969847281764045 34578129898488692730661517)
                ·
                  refine ⟨12966798711933259773998069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34578129898488692730661517 12966798711933259773998069)
                  ·
                    refine ⟨1215637379243743103812319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12966798711933259773998069 1215637379243743103812319)
                    ·
                      rfl

theorem cell23_7102336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_7102336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102336 prefixEnd_7102336 := by exact prefixLift 7102336
  have htrace : WordTrace (prefixWord ++ tailWord_7102336) baseStart_7102336 baseEnd_7102336 := by
    simpa [prefixWord, tailWord_7102336, baseEnd_7102336] using wordTrace_append hprefix tailTrace_7102336
  have hstable : (prefixWord ++ tailWord_7102336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102336).length < 2 ^ (prefixWord ++ tailWord_7102336).sum := by decide
  have hdescent : baseEnd_7102336 < baseStart_7102336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102367 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7102367 : Nat := 118140960795 + 7102367 * 2 ^ 59
def prefixEnd_7102367 : Nat := 4983230072969 + 3 ^ 40 * 7102367 * 2
def baseEnd_7102367 : Nat := 3646928055631518690149315

theorem tailTrace_7102367 : CollatzResearch.WordTrace tailWord_7102367 prefixEnd_7102367 3646928055631518690149315 := by
  unfold tailWord_7102367
  simp only [CollatzResearch.WordTrace]
  refine ⟨259044605860344821557825355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172696403906896547705216903 259044605860344821557825355)
  ·
    refine ⟨388566908790517232336738033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259044605860344821557825355 388566908790517232336738033)
    ·
      refine ⟨291425181592887924252553525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388566908790517232336738033 291425181592887924252553525)
      ·
        refine ⟨27321110774333242898676893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291425181592887924252553525 27321110774333242898676893)
        ·
          refine ⟨10245416540374966087003835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27321110774333242898676893 10245416540374966087003835)
          ·
            refine ⟨15368124810562449130505753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245416540374966087003835 15368124810562449130505753)
            ·
              refine ⟨11526093607921836847879315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15368124810562449130505753 11526093607921836847879315)
              ·
                refine ⟨17289140411882755271818973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11526093607921836847879315 17289140411882755271818973)
                ·
                  refine ⟨6483427654456033226932115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17289140411882755271818973 6483427654456033226932115)
                  ·
                    refine ⟨9725141481684049840398173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483427654456033226932115 9725141481684049840398173)
                    ·
                      refine ⟨3646928055631518690149315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725141481684049840398173 3646928055631518690149315)
                      ·
                        rfl

theorem cell23_7102367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7102367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102367 prefixEnd_7102367 := by exact prefixLift 7102367
  have htrace : WordTrace (prefixWord ++ tailWord_7102367) baseStart_7102367 baseEnd_7102367 := by
    simpa [prefixWord, tailWord_7102367, baseEnd_7102367] using wordTrace_append hprefix tailTrace_7102367
  have hstable : (prefixWord ++ tailWord_7102367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102367).length < 2 ^ (prefixWord ++ tailWord_7102367).sum := by decide
  have hdescent : baseEnd_7102367 < baseStart_7102367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102410 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_7102410 : Nat := 118140960795 + 7102410 * 2 ^ 59
def prefixEnd_7102410 : Nat := 4983230072969 + 3 ^ 40 * 7102410 * 2
def baseEnd_7102410 : Nat := 3646950135299662021911617

theorem tailTrace_7102410 : CollatzResearch.WordTrace tailWord_7102410 prefixEnd_7102410 3646950135299662021911617 := by
  unfold tailWord_7102410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64761543549797259975410171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172697449466126026601093789 64761543549797259975410171)
  ·
    refine ⟨97142315324695889963115257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64761543549797259975410171 97142315324695889963115257)
    ·
      refine ⟨72856736493521917472336443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97142315324695889963115257 72856736493521917472336443)
      ·
        refine ⟨109285104740282876208504665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72856736493521917472336443 109285104740282876208504665)
        ·
          refine ⟨81963828555212157156378499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109285104740282876208504665 81963828555212157156378499)
          ·
            refine ⟨122945742832818235734567749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81963828555212157156378499 122945742832818235734567749)
            ·
              refine ⟨23052326781153419200231453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122945742832818235734567749 23052326781153419200231453)
              ·
                refine ⟨8644622542932532200086795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23052326781153419200231453 8644622542932532200086795)
                ·
                  refine ⟨12966933814398798300130193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644622542932532200086795 12966933814398798300130193)
                  ·
                    refine ⟨9725200360799098725097645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12966933814398798300130193 9725200360799098725097645)
                    ·
                      refine ⟨3646950135299662021911617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725200360799098725097645 3646950135299662021911617)
                      ·
                        rfl

theorem cell23_7102410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_7102410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102410 prefixEnd_7102410 := by exact prefixLift 7102410
  have htrace : WordTrace (prefixWord ++ tailWord_7102410) baseStart_7102410 baseEnd_7102410 := by
    simpa [prefixWord, tailWord_7102410, baseEnd_7102410] using wordTrace_append hprefix tailTrace_7102410
  have hstable : (prefixWord ++ tailWord_7102410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102410).length < 2 ^ (prefixWord ++ tailWord_7102410).sum := by decide
  have hdescent : baseEnd_7102410 < baseStart_7102410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102434 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7102434 : Nat := 118140960795 + 7102434 * 2 ^ 59
def prefixEnd_7102434 : Nat := 4983230072969 + 3 ^ 40 * 7102434 * 2
def baseEnd_7102434 : Nat := 1215654152945123309337169

theorem tailTrace_7102434 : CollatzResearch.WordTrace tailWord_7102434 prefixEnd_7102434 1215654152945123309337169 := by
  unfold tailWord_7102434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64761762387775523000128589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172698033034068061333676237 64761762387775523000128589)
  ·
    refine ⟨24285660895415821125048221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64761762387775523000128589 24285660895415821125048221)
    ·
      refine ⟨9107122835780932921893083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24285660895415821125048221 9107122835780932921893083)
      ·
        refine ⟨13660684253671399382839625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107122835780932921893083 13660684253671399382839625)
        ·
          refine ⟨10245513190253549537129719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13660684253671399382839625 10245513190253549537129719)
          ·
            refine ⟨15368269785380324305694579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245513190253549537129719 15368269785380324305694579)
            ·
              refine ⟨23052404678070486458541869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368269785380324305694579 23052404678070486458541869)
              ·
                refine ⟨8644651754276432421953201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23052404678070486458541869 8644651754276432421953201)
                ·
                  refine ⟨6483488815707324316464901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8644651754276432421953201 6483488815707324316464901)
                  ·
                    refine ⟨1215654152945123309337169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483488815707324316464901 1215654152945123309337169)
                    ·
                      rfl

theorem cell23_7102434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7102434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102434 prefixEnd_7102434 := by exact prefixLift 7102434
  have htrace : WordTrace (prefixWord ++ tailWord_7102434) baseStart_7102434 baseEnd_7102434 := by
    simpa [prefixWord, tailWord_7102434, baseEnd_7102434] using wordTrace_append hprefix tailTrace_7102434
  have hstable : (prefixWord ++ tailWord_7102434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102434).length < 2 ^ (prefixWord ++ tailWord_7102434).sum := by decide
  have hdescent : baseEnd_7102434 < baseStart_7102434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102474 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_7102474 : Nat := 118140960795 + 7102474 * 2 ^ 59
def prefixEnd_7102474 : Nat := 4983230072969 + 3 ^ 40 * 7102474 * 2
def baseEnd_7102474 : Nat := 3646982998061549771511323

theorem tailTrace_7102474 : CollatzResearch.WordTrace tailWord_7102474 prefixEnd_7102474 3646982998061549771511323 := by
  unfold tailWord_7102474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64762127117739294707992619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172699005647304785887980317 64762127117739294707992619)
  ·
    refine ⟨97143190676608942061988929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64762127117739294707992619 97143190676608942061988929)
    ·
      refine ⟨72857393007456706546491697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97143190676608942061988929 72857393007456706546491697)
      ·
        refine ⟨54643044755592529909868773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72857393007456706546491697 54643044755592529909868773)
        ·
          refine ⟨10245570891673599358100395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54643044755592529909868773 10245570891673599358100395)
          ·
            refine ⟨15368356337510399037150593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245570891673599358100395 15368356337510399037150593)
            ·
              refine ⟨11526267253132799277862945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15368356337510399037150593 11526267253132799277862945)
              ·
                refine ⟨8644700439849599458397209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11526267253132799277862945 8644700439849599458397209)
                ·
                  refine ⟨6483525329887199593797907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8644700439849599458397209 6483525329887199593797907)
                  ·
                    refine ⟨9725287994830799390696861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483525329887199593797907 9725287994830799390696861)
                    ·
                      refine ⟨3646982998061549771511323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725287994830799390696861 3646982998061549771511323)
                      ·
                        rfl

theorem cell23_7102474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_7102474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102474 prefixEnd_7102474 := by exact prefixLift 7102474
  have htrace : WordTrace (prefixWord ++ tailWord_7102474) baseStart_7102474 baseEnd_7102474 := by
    simpa [prefixWord, tailWord_7102474, baseEnd_7102474] using wordTrace_append hprefix tailTrace_7102474
  have hstable : (prefixWord ++ tailWord_7102474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102474).length < 2 ^ (prefixWord ++ tailWord_7102474).sum := by decide
  have hdescent : baseEnd_7102474 < baseStart_7102474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102483 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3]
def baseStart_7102483 : Nat := 118140960795 + 7102483 * 2 ^ 59
def prefixEnd_7102483 : Nat := 4983230072969 + 3 ^ 40 * 7102483 * 2
def baseEnd_7102483 : Nat := 3646987619387440236298781

theorem tailTrace_7102483 : CollatzResearch.WordTrace tailWord_7102483 prefixEnd_7102483 3646987619387440236298781 := by
  unfold tailWord_7102483
  simp only [CollatzResearch.WordTrace]
  refine ⟨259048836727924573369048103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172699224485283048912698735 259048836727924573369048103)
  ·
    refine ⟨388573255091886860053572155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259048836727924573369048103 388573255091886860053572155)
    ·
      refine ⟨582859882637830290080358233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388573255091886860053572155 582859882637830290080358233)
      ·
        refine ⟨437144911978372717560268675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582859882637830290080358233 437144911978372717560268675)
        ·
          refine ⟨655717367967559076340403013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437144911978372717560268675 655717367967559076340403013)
          ·
            refine ⟨122947006493917326813825565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655717367967559076340403013 122947006493917326813825565)
            ·
              refine ⟨46105127435218997555184587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122947006493917326813825565 46105127435218997555184587)
              ·
                refine ⟨69157691152828496332776881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46105127435218997555184587 69157691152828496332776881)
                ·
                  refine ⟨51868268364621372249582661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69157691152828496332776881 51868268364621372249582661)
                  ·
                    refine ⟨9725300318366507296796749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51868268364621372249582661 9725300318366507296796749)
                    ·
                      refine ⟨3646987619387440236298781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725300318366507296796749 3646987619387440236298781)
                      ·
                        rfl

theorem cell23_7102483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_7102483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102483 prefixEnd_7102483 := by exact prefixLift 7102483
  have htrace : WordTrace (prefixWord ++ tailWord_7102483) baseStart_7102483 baseEnd_7102483 := by
    simpa [prefixWord, tailWord_7102483, baseEnd_7102483] using wordTrace_append hprefix tailTrace_7102483
  have hstable : (prefixWord ++ tailWord_7102483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102483).length < 2 ^ (prefixWord ++ tailWord_7102483).sum := by decide
  have hdescent : baseEnd_7102483 < baseStart_7102483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102533 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_7102533 : Nat := 118140960795 + 7102533 * 2 ^ 59
def prefixEnd_7102533 : Nat := 4983230072969 + 3 ^ 40 * 7102533 * 2
def baseEnd_7102533 : Nat := 1215671097806721680224517

theorem tailTrace_7102533 : CollatzResearch.WordTrace tailWord_7102533 prefixEnd_7102533 1215671097806721680224517 := by
  unfold tailWord_7102533
  simp only [CollatzResearch.WordTrace]
  refine ⟨259050660377743431908368253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172700440251828954605578835 259050660377743431908368253)
  ·
    refine ⟨97143997641653786965638095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259050660377743431908368253 97143997641653786965638095)
    ·
      refine ⟨145715996462480680448457143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97143997641653786965638095 145715996462480680448457143)
      ·
        refine ⟨218573994693721020672685715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145715996462480680448457143 218573994693721020672685715)
        ·
          refine ⟨327860992040581531009028573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218573994693721020672685715 327860992040581531009028573)
          ·
            refine ⟨122947872015218074128385715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327860992040581531009028573 122947872015218074128385715)
            ·
              refine ⟨184421808022827111192578573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122947872015218074128385715 184421808022827111192578573)
              ·
                refine ⟨69158178008560166697216965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184421808022827111192578573 69158178008560166697216965)
                ·
                  refine ⟨12967158376605031255728181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69158178008560166697216965 12967158376605031255728181)
                  ·
                    refine ⟨1215671097806721680224517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12967158376605031255728181 1215671097806721680224517)
                    ·
                      rfl

theorem cell23_7102533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_7102533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102533 prefixEnd_7102533 := by exact prefixLift 7102533
  have htrace : WordTrace (prefixWord ++ tailWord_7102533) baseStart_7102533 baseEnd_7102533 := by
    simpa [prefixWord, tailWord_7102533, baseEnd_7102533] using wordTrace_append hprefix tailTrace_7102533
  have hstable : (prefixWord ++ tailWord_7102533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102533).length < 2 ^ (prefixWord ++ tailWord_7102533).sum := by decide
  have hdescent : baseEnd_7102533 < baseStart_7102533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102540 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7102540 : Nat := 118140960795 + 7102540 * 2 ^ 59
def prefixEnd_7102540 : Nat := 4983230072969 + 3 ^ 40 * 7102540 * 2
def baseEnd_7102540 : Nat := 3647016887784746513286019

theorem tailTrace_7102540 : CollatzResearch.WordTrace tailWord_7102540 prefixEnd_7102540 3647016887784746513286019 := by
  unfold tailWord_7102540
  simp only [CollatzResearch.WordTrace]
  refine ⟨129525457844359036051936537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172700610459145381402582049 129525457844359036051936537)
  ·
    refine ⟨97144093383269277038952403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129525457844359036051936537 97144093383269277038952403)
    ·
      refine ⟨145716140074903915558428605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97144093383269277038952403 145716140074903915558428605)
      ·
        refine ⟨54643552528088968334410727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145716140074903915558428605 54643552528088968334410727)
        ·
          refine ⟨81965328792133452501616091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54643552528088968334410727 81965328792133452501616091)
          ·
            refine ⟨122947993188200178752424137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81965328792133452501616091 122947993188200178752424137)
            ·
              refine ⟨92210994891150134064318103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122947993188200178752424137 92210994891150134064318103)
              ·
                refine ⟨138316492336725201096477155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92210994891150134064318103 138316492336725201096477155)
                ·
                  refine ⟨207474738505087801644715733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138316492336725201096477155 207474738505087801644715733)
                  ·
                    refine ⟨4862689183712995351048025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207474738505087801644715733 4862689183712995351048025)
                    ·
                      refine ⟨3647016887784746513286019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862689183712995351048025 3647016887784746513286019)
                      ·
                        rfl

theorem cell23_7102540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7102540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102540 prefixEnd_7102540 := by exact prefixLift 7102540
  have htrace : WordTrace (prefixWord ++ tailWord_7102540) baseStart_7102540 baseEnd_7102540 := by
    simpa [prefixWord, tailWord_7102540, baseEnd_7102540] using wordTrace_append hprefix tailTrace_7102540
  have hstable : (prefixWord ++ tailWord_7102540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102540).length < 2 ^ (prefixWord ++ tailWord_7102540).sum := by decide
  have hdescent : baseEnd_7102540 < baseStart_7102540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102553 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_7102553 : Nat := 118140960795 + 7102553 * 2 ^ 59
def prefixEnd_7102553 : Nat := 4983230072969 + 3 ^ 40 * 7102553 * 2
def baseEnd_7102553 : Nat := 3647023563033254962423459

theorem tailTrace_7102553 : CollatzResearch.WordTrace tailWord_7102553 prefixEnd_7102553 3647023563033254962423459 := by
  unfold tailWord_7102553
  simp only [CollatzResearch.WordTrace]
  refine ⟨259051389837670975324096313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172700926558447316882730875 259051389837670975324096313)
  ·
    refine ⟨194288542378253231493072235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259051389837670975324096313 194288542378253231493072235)
    ·
      refine ⟨291432813567379847239608353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194288542378253231493072235 291432813567379847239608353)
      ·
        refine ⟨218574610175534885429706265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291432813567379847239608353 218574610175534885429706265)
        ·
          refine ⟨163930957631651164072279699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218574610175534885429706265 163930957631651164072279699)
          ·
            refine ⟨245896436447476746108419549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163930957631651164072279699 245896436447476746108419549)
            ·
              refine ⟨92211163667803779790657331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245896436447476746108419549 92211163667803779790657331)
              ·
                refine ⟨138316745501705669685985997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92211163667803779790657331 138316745501705669685985997)
                ·
                  refine ⟨51868779563139626132244749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138316745501705669685985997 51868779563139626132244749)
                  ·
                    refine ⟨19450792336177359799591781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51868779563139626132244749 19450792336177359799591781)
                    ·
                      refine ⟨3647023563033254962423459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19450792336177359799591781 3647023563033254962423459)
                      ·
                        rfl

theorem cell23_7102553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_7102553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102553 prefixEnd_7102553 := by exact prefixLift 7102553
  have htrace : WordTrace (prefixWord ++ tailWord_7102553) baseStart_7102553 baseEnd_7102553 := by
    simpa [prefixWord, tailWord_7102553, baseEnd_7102553] using wordTrace_append hprefix tailTrace_7102553
  have hstable : (prefixWord ++ tailWord_7102553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102553).length < 2 ^ (prefixWord ++ tailWord_7102553).sum := by decide
  have hdescent : baseEnd_7102553 < baseStart_7102553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102597 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_7102597 : Nat := 118140960795 + 7102597 * 2 ^ 59
def prefixEnd_7102597 : Nat := 4983230072969 + 3 ^ 40 * 7102597 * 2
def baseEnd_7102597 : Nat := 1215682052060684263424419

theorem tailTrace_7102597 : CollatzResearch.WordTrace tailWord_7102597 prefixEnd_7102597 1215682052060684263424419 := by
  unfold tailWord_7102597
  simp only [CollatzResearch.WordTrace]
  refine ⟨259052994649511570838698045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172701996433007713892465363 259052994649511570838698045)
  ·
    refine ⟨97144872993566839064511767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259052994649511570838698045 97144872993566839064511767)
    ·
      refine ⟨145717309490350258596767651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97144872993566839064511767 145717309490350258596767651)
      ·
        refine ⟨218575964235525387895151477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145717309490350258596767651 218575964235525387895151477)
        ·
          refine ⟨20491496647080505115170451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218575964235525387895151477 20491496647080505115170451)
          ·
            refine ⟨30737244970620757672755677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20491496647080505115170451 30737244970620757672755677)
            ·
              refine ⟨11526466863982784127283379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30737244970620757672755677 11526466863982784127283379)
              ·
                refine ⟨17289700295974176190925069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11526466863982784127283379 17289700295974176190925069)
                ·
                  refine ⟨6483637610990316071596901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17289700295974176190925069 6483637610990316071596901)
                  ·
                    refine ⟨1215682052060684263424419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483637610990316071596901 1215682052060684263424419)
                    ·
                      rfl

theorem cell23_7102597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_7102597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102597 prefixEnd_7102597 := by exact prefixLift 7102597
  have htrace : WordTrace (prefixWord ++ tailWord_7102597) baseStart_7102597 baseEnd_7102597 := by
    simpa [prefixWord, tailWord_7102597, baseEnd_7102597] using wordTrace_append hprefix tailTrace_7102597
  have hstable : (prefixWord ++ tailWord_7102597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102597).length < 2 ^ (prefixWord ++ tailWord_7102597).sum := by decide
  have hdescent : baseEnd_7102597 < baseStart_7102597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102697 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_7102697 : Nat := 118140960795 + 7102697 * 2 ^ 59
def prefixEnd_7102697 : Nat := 4983230072969 + 3 ^ 40 * 7102697 * 2
def baseEnd_7102697 : Nat := 3647097504247502399022797

theorem tailTrace_7102697 : CollatzResearch.WordTrace tailWord_7102697 prefixEnd_7102697 3647097504247502399022797 := by
  unfold tailWord_7102697
  simp only [CollatzResearch.WordTrace]
  refine ⟨259056641949149287917338345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172704427966099525278225563 259056641949149287917338345)
  ·
    refine ⟨194292481461861965938003759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259056641949149287917338345 194292481461861965938003759)
    ·
      refine ⟨291438722192792948907005639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194292481461861965938003759 291438722192792948907005639)
      ·
        refine ⟨437158083289189423360508459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291438722192792948907005639 437158083289189423360508459)
        ·
          refine ⟨655737124933784135040762689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437158083289189423360508459 655737124933784135040762689)
          ·
            refine ⟨491802843700338101280572017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655737124933784135040762689 491802843700338101280572017)
            ·
              refine ⟨368852132775253575960429013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491802843700338101280572017 368852132775253575960429013)
              ·
                refine ⟨8644971861920005686572555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 368852132775253575960429013 8644971861920005686572555)
                ·
                  refine ⟨12967457792880008529858833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644971861920005686572555 12967457792880008529858833)
                  ·
                    refine ⟨9725593344660006397394125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12967457792880008529858833 9725593344660006397394125)
                    ·
                      refine ⟨3647097504247502399022797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725593344660006397394125 3647097504247502399022797)
                      ·
                        rfl

theorem cell23_7102697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_7102697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102697 prefixEnd_7102697 := by exact prefixLift 7102697
  have htrace : WordTrace (prefixWord ++ tailWord_7102697) baseStart_7102697 baseEnd_7102697 := by
    simpa [prefixWord, tailWord_7102697, baseEnd_7102697] using wordTrace_append hprefix tailTrace_7102697
  have hstable : (prefixWord ++ tailWord_7102697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102697).length < 2 ^ (prefixWord ++ tailWord_7102697).sum := by decide
  have hdescent : baseEnd_7102697 < baseStart_7102697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102730 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_7102730 : Nat := 118140960795 + 7102730 * 2 ^ 59
def prefixEnd_7102730 : Nat := 4983230072969 + 3 ^ 40 * 7102730 * 2
def baseEnd_7102730 : Nat := 1215704816369700256636715

theorem tailTrace_7102730 : CollatzResearch.WordTrace tailWord_7102730 prefixEnd_7102730 1215704816369700256636715 := by
  unfold tailWord_7102730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64764461389507433638322411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172705230372019823035526429 64764461389507433638322411)
  ·
    refine ⟨97146692084261150457483617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64764461389507433638322411 97146692084261150457483617)
    ·
      refine ⟨72860019063195862843112713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97146692084261150457483617 72860019063195862843112713)
      ·
        refine ⟨54645014297396897132334535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72860019063195862843112713 54645014297396897132334535)
        ·
          refine ⟨81967521446095345698501803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54645014297396897132334535 81967521446095345698501803)
          ·
            refine ⟨122951282169143018547752705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81967521446095345698501803 122951282169143018547752705)
            ·
              refine ⟨92213461626857263910814529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122951282169143018547752705 92213461626857263910814529)
              ·
                refine ⟨69160096220142947933110897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92213461626857263910814529 69160096220142947933110897)
                ·
                  refine ⟨51870072165107210949833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69160096220142947933110897 51870072165107210949833173)
                  ·
                    refine ⟨1215704816369700256636715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51870072165107210949833173 1215704816369700256636715)
                    ·
                      rfl

theorem cell23_7102730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7102730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102730 prefixEnd_7102730 := by exact prefixLift 7102730
  have htrace : WordTrace (prefixWord ++ tailWord_7102730) baseStart_7102730 baseEnd_7102730 := by
    simpa [prefixWord, tailWord_7102730, baseEnd_7102730] using wordTrace_append hprefix tailTrace_7102730
  have hstable : (prefixWord ++ tailWord_7102730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102730).length < 2 ^ (prefixWord ++ tailWord_7102730).sum := by decide
  have hdescent : baseEnd_7102730 < baseStart_7102730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102762 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7102762 : Nat := 118140960795 + 7102762 * 2 ^ 59
def prefixEnd_7102762 : Nat := 4983230072969 + 3 ^ 40 * 7102762 * 2
def baseEnd_7102762 : Nat := 3647130880490044644709999

theorem tailTrace_7102762 : CollatzResearch.WordTrace tailWord_7102762 prefixEnd_7102762 3647130880490044644709999 := by
  unfold tailWord_7102762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64764753173478451004613635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172706008462609202678969693 64764753173478451004613635)
  ·
    refine ⟨97147129760217676506920453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64764753173478451004613635 97147129760217676506920453)
    ·
      refine ⟨18215086830040814345047585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97147129760217676506920453 18215086830040814345047585)
      ·
        refine ⟨13661315122530610758785689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18215086830040814345047585 13661315122530610758785689)
        ·
          refine ⟨10245986341897958069089267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13661315122530610758785689 10245986341897958069089267)
          ·
            refine ⟨15368979512846937103633901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245986341897958069089267 15368979512846937103633901)
            ·
              refine ⟨5763367317317601413862713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15368979512846937103633901 5763367317317601413862713)
              ·
                refine ⟨4322525487988201060397035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763367317317601413862713 4322525487988201060397035)
                ·
                  refine ⟨6483788231982301590595553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322525487988201060397035 6483788231982301590595553)
                  ·
                    refine ⟨4862841173986726192946665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483788231982301590595553 4862841173986726192946665)
                    ·
                      refine ⟨3647130880490044644709999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862841173986726192946665 3647130880490044644709999)
                      ·
                        rfl

theorem cell23_7102762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7102762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102762 prefixEnd_7102762 := by exact prefixLift 7102762
  have htrace : WordTrace (prefixWord ++ tailWord_7102762) baseStart_7102762 baseEnd_7102762 := by
    simpa [prefixWord, tailWord_7102762, baseEnd_7102762] using wordTrace_append hprefix tailTrace_7102762
  have hstable : (prefixWord ++ tailWord_7102762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102762).length < 2 ^ (prefixWord ++ tailWord_7102762).sum := by decide
  have hdescent : baseEnd_7102762 < baseStart_7102762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102778 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_7102778 : Nat := 118140960795 + 7102778 * 2 ^ 59
def prefixEnd_7102778 : Nat := 4983230072969 + 3 ^ 40 * 7102778 * 2
def baseEnd_7102778 : Nat := 3647139096180516582109925

theorem tailTrace_7102778 : CollatzResearch.WordTrace tailWord_7102778 prefixEnd_7102778 3647139096180516582109925 := by
  unfold tailWord_7102778
  simp only [CollatzResearch.WordTrace]
  refine ⟨64764899065463959687759247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172706397507903892500691325 64764899065463959687759247)
  ·
    refine ⟨97147348598195939531638871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64764899065463959687759247 97147348598195939531638871)
    ·
      refine ⟨145721022897293909297458307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97147348598195939531638871 145721022897293909297458307)
      ·
        refine ⟨218581534345940863946187461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145721022897293909297458307 218581534345940863946187461)
        ·
          refine ⟨40984037689863911989910149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218581534345940863946187461 40984037689863911989910149)
          ·
            refine ⟨7684507066849483498108153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40984037689863911989910149 7684507066849483498108153)
            ·
              refine ⟨5763380300137112623581115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7684507066849483498108153 5763380300137112623581115)
              ·
                refine ⟨8645070450205668935371673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763380300137112623581115 8645070450205668935371673)
                ·
                  refine ⟨6483802837654251701528755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645070450205668935371673 6483802837654251701528755)
                  ·
                    refine ⟨9725704256481377552293133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6483802837654251701528755 9725704256481377552293133)
                    ·
                      refine ⟨3647139096180516582109925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725704256481377552293133 3647139096180516582109925)
                      ·
                        rfl

theorem cell23_7102778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_7102778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102778 prefixEnd_7102778 := by exact prefixLift 7102778
  have htrace : WordTrace (prefixWord ++ tailWord_7102778) baseStart_7102778 baseEnd_7102778 := by
    simpa [prefixWord, tailWord_7102778, baseEnd_7102778] using wordTrace_append hprefix tailTrace_7102778
  have hstable : (prefixWord ++ tailWord_7102778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102778).length < 2 ^ (prefixWord ++ tailWord_7102778).sum := by decide
  have hdescent : baseEnd_7102778 < baseStart_7102778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102784 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2]
def baseStart_7102784 : Nat := 118140960795 + 7102784 * 2 ^ 59
def prefixEnd_7102784 : Nat := 4983230072969 + 3 ^ 40 * 7102784 * 2
def baseEnd_7102784 : Nat := 3647142177064443558634897

theorem tailTrace_7102784 : CollatzResearch.WordTrace tailWord_7102784 prefixEnd_7102784 3647142177064443558634897 := by
  unfold tailWord_7102784
  simp only [CollatzResearch.WordTrace]
  refine ⟨129529907549917050887877703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172706543399889401183836937 129529907549917050887877703)
  ·
    refine ⟨194294861324875576331816555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129529907549917050887877703 194294861324875576331816555)
    ·
      refine ⟨291442291987313364497724833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194294861324875576331816555 291442291987313364497724833)
      ·
        refine ⟨218581718990485023373293625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291442291987313364497724833 218581718990485023373293625)
        ·
          refine ⟨163936289242863767529970219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218581718990485023373293625 163936289242863767529970219)
          ·
            refine ⟨245904433864295651294955329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163936289242863767529970219 245904433864295651294955329)
            ·
              refine ⟨184428325398221738471216497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245904433864295651294955329 184428325398221738471216497)
              ·
                refine ⟨138321244048666303853412373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184428325398221738471216497 138321244048666303853412373)
                ·
                  refine ⟨6483808314781232993128705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138321244048666303853412373 6483808314781232993128705)
                  ·
                    refine ⟨4862856236085924744846529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483808314781232993128705 4862856236085924744846529)
                    ·
                      refine ⟨3647142177064443558634897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862856236085924744846529 3647142177064443558634897)
                      ·
                        rfl

theorem cell23_7102784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_7102784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102784 prefixEnd_7102784 := by exact prefixLift 7102784
  have htrace : WordTrace (prefixWord ++ tailWord_7102784) baseStart_7102784 baseEnd_7102784 := by
    simpa [prefixWord, tailWord_7102784, baseEnd_7102784] using wordTrace_append hprefix tailTrace_7102784
  have hstable : (prefixWord ++ tailWord_7102784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102784).length < 2 ^ (prefixWord ++ tailWord_7102784).sum := by decide
  have hdescent : baseEnd_7102784 < baseStart_7102784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102788 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7102788 : Nat := 118140960795 + 7102788 * 2 ^ 59
def prefixEnd_7102788 : Nat := 4983230072969 + 3 ^ 40 * 7102788 * 2
def baseEnd_7102788 : Nat := 3647144230987061542984879

theorem tailTrace_7102788 : CollatzResearch.WordTrace tailWord_7102788 prefixEnd_7102788 3647144230987061542984879 := by
  unfold tailWord_7102788
  simp only [CollatzResearch.WordTrace]
  refine ⟨129529980495909805229450509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172706640661213073639267345 129529980495909805229450509)
  ·
    refine ⟨48573742685966176961043941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129529980495909805229450509 48573742685966176961043941)
    ·
      refine ⟨9107576753618658180195739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48573742685966176961043941 9107576753618658180195739)
      ·
        refine ⟨13661365130427987270293609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107576753618658180195739 13661365130427987270293609)
        ·
          refine ⟨10246023847820990452720207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13661365130427987270293609 10246023847820990452720207)
          ·
            refine ⟨15369035771731485679080311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246023847820990452720207 15369035771731485679080311)
            ·
              refine ⟨23053553657597228518620467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15369035771731485679080311 23053553657597228518620467)
              ·
                refine ⟨34580330486395842777930701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23053553657597228518620467 34580330486395842777930701)
                ·
                  refine ⟨12967623932398441041724013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34580330486395842777930701 12967623932398441041724013)
                  ·
                    refine ⟨4862858974649415390646505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12967623932398441041724013 4862858974649415390646505)
                    ·
                      refine ⟨3647144230987061542984879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862858974649415390646505 3647144230987061542984879)
                      ·
                        rfl

theorem cell23_7102788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7102788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102788 prefixEnd_7102788 := by exact prefixLift 7102788
  have htrace : WordTrace (prefixWord ++ tailWord_7102788) baseStart_7102788 baseEnd_7102788 := by
    simpa [prefixWord, tailWord_7102788, baseEnd_7102788] using wordTrace_append hprefix tailTrace_7102788
  have hstable : (prefixWord ++ tailWord_7102788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102788).length < 2 ^ (prefixWord ++ tailWord_7102788).sum := by decide
  have hdescent : baseEnd_7102788 < baseStart_7102788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102818 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7102818 : Nat := 118140960795 + 7102818 * 2 ^ 59
def prefixEnd_7102818 : Nat := 4983230072969 + 3 ^ 40 * 7102818 * 2
def baseEnd_7102818 : Nat := 3647159635406696425609741

theorem tailTrace_7102818 : CollatzResearch.WordTrace tailWord_7102818 prefixEnd_7102818 3647159635406696425609741 := by
  unfold tailWord_7102818
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765263795427731395623277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172707370121140617054995405 64765263795427731395623277)
  ·
    refine ⟨24286973923285399273358729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64765263795427731395623277 24286973923285399273358729)
    ·
      refine ⟨18215230442464049455019047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24286973923285399273358729 18215230442464049455019047)
      ·
        refine ⟨27322845663696074182528571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18215230442464049455019047 27322845663696074182528571)
        ·
          refine ⟨40984268495544111273792857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27322845663696074182528571 40984268495544111273792857)
          ·
            refine ⟨30738201371658083455344643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40984268495544111273792857 30738201371658083455344643)
            ·
              refine ⟨46107302057487125183016965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30738201371658083455344643 46107302057487125183016965)
              ·
                refine ⟨8645119135778835971815681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46107302057487125183016965 8645119135778835971815681)
                ·
                  refine ⟨6483839351834126978861761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645119135778835971815681 6483839351834126978861761)
                  ·
                    refine ⟨4862879513875595234146321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6483839351834126978861761 4862879513875595234146321)
                    ·
                      refine ⟨3647159635406696425609741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862879513875595234146321 3647159635406696425609741)
                      ·
                        rfl

theorem cell23_7102818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7102818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102818 prefixEnd_7102818 := by exact prefixLift 7102818
  have htrace : WordTrace (prefixWord ++ tailWord_7102818) baseStart_7102818 baseEnd_7102818 := by
    simpa [prefixWord, tailWord_7102818, baseEnd_7102818] using wordTrace_append hprefix tailTrace_7102818
  have hstable : (prefixWord ++ tailWord_7102818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102818).length < 2 ^ (prefixWord ++ tailWord_7102818).sum := by decide
  have hdescent : baseEnd_7102818 < baseStart_7102818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102834 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7102834 : Nat := 118140960795 + 7102834 * 2 ^ 59
def prefixEnd_7102834 : Nat := 4983230072969 + 3 ^ 40 * 7102834 * 2
def baseEnd_7102834 : Nat := 3647167851097168363009667

theorem tailTrace_7102834 : CollatzResearch.WordTrace tailWord_7102834 prefixEnd_7102834 3647167851097168363009667 := by
  unfold tailWord_7102834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765409687413240078768889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172707759166435306876717037 64765409687413240078768889)
  ·
    refine ⟨48574057265559930059076667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64765409687413240078768889 48574057265559930059076667)
    ·
      refine ⟨72861085898339895088615001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48574057265559930059076667 72861085898339895088615001)
      ·
        refine ⟨54645814423754921316461251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72861085898339895088615001 54645814423754921316461251)
        ·
          refine ⟨81968721635632381974691877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54645814423754921316461251 81968721635632381974691877)
          ·
            refine ⟨15369135306681071620254727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81968721635632381974691877 15369135306681071620254727)
            ·
              refine ⟨23053702960021607430382091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15369135306681071620254727 23053702960021607430382091)
              ·
                refine ⟨34580554440032411145573137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23053702960021607430382091 34580554440032411145573137)
                ·
                  refine ⟨25935415830024308359179853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34580554440032411145573137 25935415830024308359179853)
                  ·
                    refine ⟨9725780936259115634692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25935415830024308359179853 9725780936259115634692445)
                    ·
                      refine ⟨3647167851097168363009667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9725780936259115634692445 3647167851097168363009667)
                      ·
                        rfl

theorem cell23_7102834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7102834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102834 prefixEnd_7102834 := by exact prefixLift 7102834
  have htrace : WordTrace (prefixWord ++ tailWord_7102834) baseStart_7102834 baseEnd_7102834 := by
    simpa [prefixWord, tailWord_7102834, baseEnd_7102834] using wordTrace_append hprefix tailTrace_7102834
  have hstable : (prefixWord ++ tailWord_7102834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102834).length < 2 ^ (prefixWord ++ tailWord_7102834).sum := by decide
  have hdescent : baseEnd_7102834 < baseStart_7102834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102858 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_7102858 : Nat := 118140960795 + 7102858 * 2 ^ 59
def prefixEnd_7102858 : Nat := 4983230072969 + 3 ^ 40 * 7102858 * 2
def baseEnd_7102858 : Nat := 405242241625875141012173

theorem tailTrace_7102858 : CollatzResearch.WordTrace tailWord_7102858 prefixEnd_7102858 405242241625875141012173 := by
  unfold tailWord_7102858
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765628525391503103487307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172708342734377341609299485 64765628525391503103487307)
  ·
    refine ⟨97148442788087254655230961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64765628525391503103487307 97148442788087254655230961)
    ·
      refine ⟨72861332091065440991423221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97148442788087254655230961 72861332091065440991423221)
      ·
        refine ⟨6830749883537385092945927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72861332091065440991423221 6830749883537385092945927)
        ·
          refine ⟨10246124825306077639418891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6830749883537385092945927 10246124825306077639418891)
          ·
            refine ⟨15369187237959116459128337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246124825306077639418891 15369187237959116459128337)
            ·
              refine ⟨11526890428469337344346253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15369187237959116459128337 11526890428469337344346253)
              ·
                refine ⟨4322583910676001504129845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11526890428469337344346253 4322583910676001504129845)
                ·
                  refine ⟨405242241625875141012173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4322583910676001504129845 405242241625875141012173)
                  ·
                    rfl

theorem cell23_7102858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_7102858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102858 prefixEnd_7102858 := by exact prefixLift 7102858
  have htrace : WordTrace (prefixWord ++ tailWord_7102858) baseStart_7102858 baseEnd_7102858 := by
    simpa [prefixWord, tailWord_7102858, baseEnd_7102858] using wordTrace_append hprefix tailTrace_7102858
  have hstable : (prefixWord ++ tailWord_7102858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102858).length < 2 ^ (prefixWord ++ tailWord_7102858).sum := by decide
  have hdescent : baseEnd_7102858 < baseStart_7102858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102884 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_7102884 : Nat := 118140960795 + 7102884 * 2 ^ 59
def prefixEnd_7102884 : Nat := 4983230072969 + 3 ^ 40 * 7102884 * 2
def baseEnd_7102884 : Nat := 1215731175043297722461479

theorem tailTrace_7102884 : CollatzResearch.WordTrace tailWord_7102884 prefixEnd_7102884 1215731175043297722461479 := by
  unfold tailWord_7102884
  simp only [CollatzResearch.WordTrace]
  refine ⟨129531731199735909427197853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172708974932981212569597137 129531731199735909427197853)
  ·
    refine ⟨48574399199900966035199195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129531731199735909427197853 48574399199900966035199195)
    ·
      refine ⟨72861598799851449052798793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48574399199900966035199195 72861598799851449052798793)
      ·
        refine ⟨54646199099888586789599095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72861598799851449052798793 54646199099888586789599095)
        ·
          refine ⟨81969298649832880184398643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54646199099888586789599095 81969298649832880184398643)
          ·
            refine ⟨122953947974749320276597965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81969298649832880184398643 122953947974749320276597965)
            ·
              refine ⟨46107730490530995103724237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122953947974749320276597965 46107730490530995103724237)
              ·
                refine ⟨17290398933949123163896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46107730490530995103724237 17290398933949123163896589)
                ·
                  refine ⟨6483899600230921186461221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17290398933949123163896589 6483899600230921186461221)
                  ·
                    refine ⟨1215731175043297722461479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483899600230921186461221 1215731175043297722461479)
                    ·
                      rfl

theorem cell23_7102884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_7102884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102884 prefixEnd_7102884 := by exact prefixLift 7102884
  have htrace : WordTrace (prefixWord ++ tailWord_7102884) baseStart_7102884 baseEnd_7102884 := by
    simpa [prefixWord, tailWord_7102884, baseEnd_7102884] using wordTrace_append hprefix tailTrace_7102884
  have hstable : (prefixWord ++ tailWord_7102884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102884).length < 2 ^ (prefixWord ++ tailWord_7102884).sum := by decide
  have hdescent : baseEnd_7102884 < baseStart_7102884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102927 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 5, 5]
def baseStart_7102927 : Nat := 118140960795 + 7102927 * 2 ^ 59
def prefixEnd_7102927 : Nat := 4983230072969 + 3 ^ 40 * 7102927 * 2
def baseEnd_7102927 : Nat := 1215738534932678833048913

theorem tailTrace_7102927 : CollatzResearch.WordTrace tailWord_7102927 prefixEnd_7102927 1215738534932678833048913 := by
  unfold tailWord_7102927
  simp only [CollatzResearch.WordTrace]
  refine ⟨259065030738316037198211035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172710020492210691465474023 259065030738316037198211035)
  ·
    refine ⟨388597546107474055797316553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259065030738316037198211035 388597546107474055797316553)
    ·
      refine ⟨291448159580605541847987415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388597546107474055797316553 291448159580605541847987415)
      ·
        refine ⟨437172239370908312771981123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291448159580605541847987415 437172239370908312771981123)
        ·
          refine ⟨655758359056362469157971685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437172239370908312771981123 655758359056362469157971685)
          ·
            refine ⟨122954692323067962967119691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655758359056362469157971685 122954692323067962967119691)
            ·
              refine ⟨184432038484601944450679537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122954692323067962967119691 184432038484601944450679537)
              ·
                refine ⟨138324028863451458338009653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184432038484601944450679537 138324028863451458338009653)
                ·
                  refine ⟨12967877705948574219188405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138324028863451458338009653 12967877705948574219188405)
                  ·
                    refine ⟨1215738534932678833048913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12967877705948574219188405 1215738534932678833048913)
                    ·
                      rfl

theorem cell23_7102927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_7102927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102927 prefixEnd_7102927 := by exact prefixLift 7102927
  have htrace : WordTrace (prefixWord ++ tailWord_7102927) baseStart_7102927 baseEnd_7102927 := by
    simpa [prefixWord, tailWord_7102927, baseEnd_7102927] using wordTrace_append hprefix tailTrace_7102927
  have hstable : (prefixWord ++ tailWord_7102927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102927).length < 2 ^ (prefixWord ++ tailWord_7102927).sum := by decide
  have hdescent : baseEnd_7102927 < baseStart_7102927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102951 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7102951 : Nat := 118140960795 + 7102951 * 2 ^ 59
def prefixEnd_7102951 : Nat := 4983230072969 + 3 ^ 40 * 7102951 * 2
def baseEnd_7102951 : Nat := 3647227928333744405246629

theorem tailTrace_7102951 : CollatzResearch.WordTrace tailWord_7102951 prefixEnd_7102951 3647227928333744405246629 := by
  unfold tailWord_7102951
  simp only [CollatzResearch.WordTrace]
  refine ⟨259065906090229089297084707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172710604060152726198056471 259065906090229089297084707)
  ·
    refine ⟨388598859135343633945627061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259065906090229089297084707 388598859135343633945627061)
    ·
      refine ⟨36431143043938465682402537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388598859135343633945627061 36431143043938465682402537)
      ·
        refine ⟨27323357282953849261801903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36431143043938465682402537 27323357282953849261801903)
        ·
          refine ⟨40985035924430773892702855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27323357282953849261801903 40985035924430773892702855)
          ·
            refine ⟨61477553886646160839054283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40985035924430773892702855 61477553886646160839054283)
            ·
              refine ⟨92216330829969241258581425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61477553886646160839054283 92216330829969241258581425)
              ·
                refine ⟨69162248122476930943936069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92216330829969241258581425 69162248122476930943936069)
                ·
                  refine ⟨12967921522964424551988013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69162248122476930943936069 12967921522964424551988013)
                  ·
                    refine ⟨4862970571111659206995505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12967921522964424551988013 4862970571111659206995505)
                    ·
                      refine ⟨3647227928333744405246629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4862970571111659206995505 3647227928333744405246629)
                      ·
                        rfl

theorem cell23_7102951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7102951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102951 prefixEnd_7102951 := by exact prefixLift 7102951
  have htrace : WordTrace (prefixWord ++ tailWord_7102951) baseStart_7102951 baseEnd_7102951 := by
    simpa [prefixWord, tailWord_7102951, baseEnd_7102951] using wordTrace_append hprefix tailTrace_7102951
  have hstable : (prefixWord ++ tailWord_7102951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102951).length < 2 ^ (prefixWord ++ tailWord_7102951).sum := by decide
  have hdescent : baseEnd_7102951 < baseStart_7102951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7102987 : List Nat := [1, 1, 1, 1, 7, 12]
def baseStart_7102987 : Nat := 118140960795 + 7102987 * 2 ^ 59
def prefixEnd_7102987 : Nat := 4983230072969 + 3 ^ 40 * 7102987 * 2
def baseEnd_7102987 : Nat := 15009244500565046355541

theorem tailTrace_7102987 : CollatzResearch.WordTrace tailWord_7102987 prefixEnd_7102987 15009244500565046355541 := by
  unfold tailWord_7102987
  simp only [CollatzResearch.WordTrace]
  refine ⟨259067219118098667445395215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172711479412065778296930143 259067219118098667445395215)
  ·
    refine ⟨388600828677148001168092823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259067219118098667445395215 388600828677148001168092823)
    ·
      refine ⟨582901243015722001752139235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388600828677148001168092823 582901243015722001752139235)
      ·
        refine ⟨874351864523583002628208853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582901243015722001752139235 874351864523583002628208853)
        ·
          refine ⟨20492621824771476624098645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 874351864523583002628208853 20492621824771476624098645)
          ·
            refine ⟨15009244500565046355541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20492621824771476624098645 15009244500565046355541)
            ·
              rfl

theorem cell23_7102987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 12].length) (baseStart_7102987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7102987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7102987 prefixEnd_7102987 := by exact prefixLift 7102987
  have htrace : WordTrace (prefixWord ++ tailWord_7102987) baseStart_7102987 baseEnd_7102987 := by
    simpa [prefixWord, tailWord_7102987, baseEnd_7102987] using wordTrace_append hprefix tailTrace_7102987
  have hstable : (prefixWord ++ tailWord_7102987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7102987).length < 2 ^ (prefixWord ++ tailWord_7102987).sum := by decide
  have hdescent : baseEnd_7102987 < baseStart_7102987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7102987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103004 : List Nat := [2, 2, 3, 1, 2, 2, 3, 8]
def baseStart_7103004 : Nat := 118140960795 + 7103004 * 2 ^ 59
def prefixEnd_7103004 : Nat := 4983230072969 + 3 ^ 40 * 7103004 * 2
def baseEnd_7103004 : Nat := 135083523807719729551255

theorem tailTrace_7103004 : CollatzResearch.WordTrace tailWord_7103004 prefixEnd_7103004 135083523807719729551255 := by
  unfold tailWord_7103004
  simp only [CollatzResearch.WordTrace]
  refine ⟨129533919579518539674382033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172711892772691386232509377 129533919579518539674382033)
  ·
    refine ⟨97150439684638904755786525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129533919579518539674382033 97150439684638904755786525)
    ·
      refine ⟨36431414881739589283419947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97150439684638904755786525 36431414881739589283419947)
      ·
        refine ⟨54647122322609383925129921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36431414881739589283419947 54647122322609383925129921)
        ·
          refine ⟨40985341741957037943847441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54647122322609383925129921 40985341741957037943847441)
          ·
            refine ⟨30739006306467778457885581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40985341741957037943847441 30739006306467778457885581)
            ·
              refine ⟨11527127364925416921707093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30739006306467778457885581 11527127364925416921707093)
              ·
                refine ⟨135083523807719729551255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11527127364925416921707093 135083523807719729551255)
                ·
                  rfl

theorem cell23_7103004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 8].length) (baseStart_7103004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103004 prefixEnd_7103004 := by exact prefixLift 7103004
  have htrace : WordTrace (prefixWord ++ tailWord_7103004) baseStart_7103004 baseEnd_7103004 := by
    simpa [prefixWord, tailWord_7103004, baseEnd_7103004] using wordTrace_append hprefix tailTrace_7103004
  have hstable : (prefixWord ++ tailWord_7103004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103004).length < 2 ^ (prefixWord ++ tailWord_7103004).sum := by decide
  have hdescent : baseEnd_7103004 < baseStart_7103004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103011 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4]
def baseStart_7103011 : Nat := 118140960795 + 7103011 * 2 ^ 59
def prefixEnd_7103011 : Nat := 4983230072969 + 3 ^ 40 * 7103011 * 2
def baseEnd_7103011 : Nat := 3647258737173014170496353

theorem tailTrace_7103011 : CollatzResearch.WordTrace tailWord_7103011 prefixEnd_7103011 3647258737173014170496353 := by
  unfold tailWord_7103011
  simp only [CollatzResearch.WordTrace]
  refine ⟨259068094470011719544268887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172712062980007813029512591 259068094470011719544268887)
  ·
    refine ⟨388602141705017579316403331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259068094470011719544268887 388602141705017579316403331)
    ·
      refine ⟨582903212557526368974604997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388602141705017579316403331 582903212557526368974604997)
      ·
        refine ⟨109294352354536194182738437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582903212557526368974604997 109294352354536194182738437)
        ·
          refine ⟨20492691066475536409263457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109294352354536194182738437 20492691066475536409263457)
          ·
            refine ⟨15369518299856652306947593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20492691066475536409263457 15369518299856652306947593)
            ·
              refine ⟨11527138724892489230210695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15369518299856652306947593 11527138724892489230210695)
              ·
                refine ⟨17290708087338733845316043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11527138724892489230210695 17290708087338733845316043)
                ·
                  refine ⟨25936062131008100767974065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17290708087338733845316043 25936062131008100767974065)
                  ·
                    refine ⟨19452046598256075575980549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25936062131008100767974065 19452046598256075575980549)
                    ·
                      refine ⟨3647258737173014170496353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19452046598256075575980549 3647258737173014170496353)
                      ·
                        rfl

theorem cell23_7103011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_7103011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103011 prefixEnd_7103011 := by exact prefixLift 7103011
  have htrace : WordTrace (prefixWord ++ tailWord_7103011) baseStart_7103011 baseEnd_7103011 := by
    simpa [prefixWord, tailWord_7103011, baseEnd_7103011] using wordTrace_append hprefix tailTrace_7103011
  have hstable : (prefixWord ++ tailWord_7103011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103011).length < 2 ^ (prefixWord ++ tailWord_7103011).sum := by decide
  have hdescent : baseEnd_7103011 < baseStart_7103011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103031 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_7103031 : Nat := 118140960795 + 7103031 * 2 ^ 59
def prefixEnd_7103031 : Nat := 4983230072969 + 3 ^ 40 * 7103031 * 2
def baseEnd_7103031 : Nat := 3647269006786104092246261

theorem tailTrace_7103031 : CollatzResearch.WordTrace tailWord_7103031 prefixEnd_7103031 3647269006786104092246261 := by
  unfold tailWord_7103031
  simp only [CollatzResearch.WordTrace]
  refine ⟨259068823929939262959996947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172712549286626175306664631 259068823929939262959996947)
  ·
    refine ⟨388603235894908894439995421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259068823929939262959996947 388603235894908894439995421)
    ·
      refine ⟨145726213460590835414998283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388603235894908894439995421 145726213460590835414998283)
      ·
        refine ⟨218589320190886253122497425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145726213460590835414998283 218589320190886253122497425)
        ·
          refine ⟨163941990143164689841873069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218589320190886253122497425 163941990143164689841873069)
          ·
            refine ⟨61478246303686758690702401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163941990143164689841873069 61478246303686758690702401)
            ·
              refine ⟨46108684727765069018026801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61478246303686758690702401 46108684727765069018026801)
              ·
                refine ⟨34581513545823801763520101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46108684727765069018026801 34581513545823801763520101)
                ·
                  refine ⟨6484033789841962830660019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34581513545823801763520101 6484033789841962830660019)
                  ·
                    refine ⟨9726050684762944245990029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484033789841962830660019 9726050684762944245990029)
                    ·
                      refine ⟨3647269006786104092246261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726050684762944245990029 3647269006786104092246261)
                      ·
                        rfl

theorem cell23_7103031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_7103031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103031 prefixEnd_7103031 := by exact prefixLift 7103031
  have htrace : WordTrace (prefixWord ++ tailWord_7103031) baseStart_7103031 baseEnd_7103031 := by
    simpa [prefixWord, tailWord_7103031, baseEnd_7103031] using wordTrace_append hprefix tailTrace_7103031
  have hstable : (prefixWord ++ tailWord_7103031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103031).length < 2 ^ (prefixWord ++ tailWord_7103031).sum := by decide
  have hdescent : baseEnd_7103031 < baseStart_7103031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103054 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_7103054 : Nat := 118140960795 + 7103054 * 2 ^ 59
def prefixEnd_7103054 : Nat := 4983230072969 + 3 ^ 40 * 7103054 * 2
def baseEnd_7103054 : Nat := 3647280816841157502258655

theorem tailTrace_7103054 : CollatzResearch.WordTrace tailWord_7103054 prefixEnd_7103054 3647280816841157502258655 := by
  unfold tailWord_7103054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32383707851106992236010527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172713108539237291925389477 32383707851106992236010527)
  ·
    refine ⟨48575561776660488354015791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32383707851106992236010527 48575561776660488354015791)
    ·
      refine ⟨72863342664990732531023687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48575561776660488354015791 72863342664990732531023687)
      ·
        refine ⟨109295013997486098796535531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72863342664990732531023687 109295013997486098796535531)
        ·
          refine ⟨163942520996229148194803297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109295013997486098796535531 163942520996229148194803297)
          ·
            refine ⟨122956890747171861146102473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163942520996229148194803297 122956890747171861146102473)
            ·
              refine ⟨92217668060378895859576855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122956890747171861146102473 92217668060378895859576855)
              ·
                refine ⟨138326502090568343789365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92217668060378895859576855 138326502090568343789365283)
                ·
                  refine ⟨207489753135852515684047925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138326502090568343789365283 207489753135852515684047925)
                  ·
                    refine ⟨19452164356486173345379493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207489753135852515684047925 19452164356486173345379493)
                    ·
                      refine ⟨3647280816841157502258655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19452164356486173345379493 3647280816841157502258655)
                      ·
                        rfl

theorem cell23_7103054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_7103054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103054 prefixEnd_7103054 := by exact prefixLift 7103054
  have htrace : WordTrace (prefixWord ++ tailWord_7103054) baseStart_7103054 baseEnd_7103054 := by
    simpa [prefixWord, tailWord_7103054, baseEnd_7103054] using wordTrace_append hprefix tailTrace_7103054
  have hstable : (prefixWord ++ tailWord_7103054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103054).length < 2 ^ (prefixWord ++ tailWord_7103054).sum := by decide
  have hdescent : baseEnd_7103054 < baseStart_7103054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103064 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_7103064 : Nat := 118140960795 + 7103064 * 2 ^ 59
def prefixEnd_7103064 : Nat := 4983230072969 + 3 ^ 40 * 7103064 * 2
def baseEnd_7103064 : Nat := 1215761983882567487711203

theorem tailTrace_7103064 : CollatzResearch.WordTrace tailWord_7103064 prefixEnd_7103064 1215761983882567487711203 := by
  unfold tailWord_7103064
  simp only [CollatzResearch.WordTrace]
  refine ⟨129535013769409854797974123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172713351692546473063965497 129535013769409854797974123)
  ·
    refine ⟨194302520654114782196961185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129535013769409854797974123 194302520654114782196961185)
    ·
      refine ⟨145726890490586086647720889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194302520654114782196961185 145726890490586086647720889)
      ·
        refine ⟨109295167867939564985790667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145726890490586086647720889 109295167867939564985790667)
        ·
          refine ⟨163942751801909347478686001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109295167867939564985790667 163942751801909347478686001)
          ·
            refine ⟨122957063851432010609014501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163942751801909347478686001 122957063851432010609014501)
            ·
              refine ⟨23054449472143501989190219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122957063851432010609014501 23054449472143501989190219)
              ·
                refine ⟨34581674208215252983785329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23054449472143501989190219 34581674208215252983785329)
                ·
                  refine ⟨25936255656161439737838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34581674208215252983785329 25936255656161439737838997)
                  ·
                    refine ⟨1215761983882567487711203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25936255656161439737838997 1215761983882567487711203)
                    ·
                      rfl

theorem cell23_7103064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_7103064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103064 prefixEnd_7103064 := by exact prefixLift 7103064
  have htrace : WordTrace (prefixWord ++ tailWord_7103064) baseStart_7103064 baseEnd_7103064 := by
    simpa [prefixWord, tailWord_7103064, baseEnd_7103064] using wordTrace_append hprefix tailTrace_7103064
  have hstable : (prefixWord ++ tailWord_7103064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103064).length < 2 ^ (prefixWord ++ tailWord_7103064).sum := by decide
  have hdescent : baseEnd_7103064 < baseStart_7103064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103084 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_7103084 : Nat := 118140960795 + 7103084 * 2 ^ 59
def prefixEnd_7103084 : Nat := 4983230072969 + 3 ^ 40 * 7103084 * 2
def baseEnd_7103084 : Nat := 3647296221260792384883517

theorem tailTrace_7103084 : CollatzResearch.WordTrace tailWord_7103084 prefixEnd_7103084 3647296221260792384883517 := by
  unfold tailWord_7103084
  simp only [CollatzResearch.WordTrace]
  refine ⟨129535378499373626505838153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172713837999164835341117537 129535378499373626505838153)
  ·
    refine ⟨97151533874530219879378615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129535378499373626505838153 97151533874530219879378615)
    ·
      refine ⟨145727300811795329819067923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97151533874530219879378615 145727300811795329819067923)
      ·
        refine ⟨218590951217692994728601885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145727300811795329819067923 218590951217692994728601885)
        ·
          refine ⟨81971606706634873023225707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218590951217692994728601885 81971606706634873023225707)
          ·
            refine ⟨122957410059952309534838561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81971606706634873023225707 122957410059952309534838561)
            ·
              refine ⟨92218057544964232151128921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122957410059952309534838561 92218057544964232151128921)
              ·
                refine ⟨69163543158723174113346691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92218057544964232151128921 69163543158723174113346691)
                ·
                  refine ⟨103745314738084761170020037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69163543158723174113346691 103745314738084761170020037)
                  ·
                    refine ⟨19452246513390892719378757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103745314738084761170020037 19452246513390892719378757)
                    ·
                      refine ⟨3647296221260792384883517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19452246513390892719378757 3647296221260792384883517)
                      ·
                        rfl

theorem cell23_7103084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_7103084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103084 prefixEnd_7103084 := by exact prefixLift 7103084
  have htrace : WordTrace (prefixWord ++ tailWord_7103084) baseStart_7103084 baseEnd_7103084 := by
    simpa [prefixWord, tailWord_7103084, baseEnd_7103084] using wordTrace_append hprefix tailTrace_7103084
  have hstable : (prefixWord ++ tailWord_7103084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103084).length < 2 ^ (prefixWord ++ tailWord_7103084).sum := by decide
  have hdescent : baseEnd_7103084 < baseStart_7103084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103105 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7103105 : Nat := 118140960795 + 7103105 * 2 ^ 59
def prefixEnd_7103105 : Nat := 4983230072969 + 3 ^ 40 * 7103105 * 2
def baseEnd_7103105 : Nat := 3647307004354536802720921

theorem tailTrace_7103105 : CollatzResearch.WordTrace tailWord_7103105 prefixEnd_7103105 3647307004354536802720921 := by
  unfold tailWord_7103105
  simp only [CollatzResearch.WordTrace]
  refine ⟨259071522931671173598190769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172714348621114115732127179 259071522931671173598190769)
  ·
    refine ⟨194303642198753380198643077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259071522931671173598190769 194303642198753380198643077)
    ·
      refine ⟨36431932912266258787245577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194303642198753380198643077 36431932912266258787245577)
      ·
        refine ⟨27323949684199694090434183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36431932912266258787245577 27323949684199694090434183)
        ·
          refine ⟨40985924526299541135651275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27323949684199694090434183 40985924526299541135651275)
          ·
            refine ⟨61478886789449311703476913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40985924526299541135651275 61478886789449311703476913)
            ·
              refine ⟨46109165092086983777607685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61478886789449311703476913 46109165092086983777607685)
              ·
                refine ⟨8645468454766309458301441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46109165092086983777607685 8645468454766309458301441)
                ·
                  refine ⟨6484101341074732093726081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645468454766309458301441 6484101341074732093726081)
                  ·
                    refine ⟨4863076005806049070294561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484101341074732093726081 4863076005806049070294561)
                    ·
                      refine ⟨3647307004354536802720921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863076005806049070294561 3647307004354536802720921)
                      ·
                        rfl

theorem cell23_7103105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7103105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103105 prefixEnd_7103105 := by exact prefixLift 7103105
  have htrace : WordTrace (prefixWord ++ tailWord_7103105) baseStart_7103105 baseEnd_7103105 := by
    simpa [prefixWord, tailWord_7103105, baseEnd_7103105] using wordTrace_append hprefix tailTrace_7103105
  have hstable : (prefixWord ++ tailWord_7103105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103105).length < 2 ^ (prefixWord ++ tailWord_7103105).sum := by decide
  have hdescent : baseEnd_7103105 < baseStart_7103105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103122 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7103122 : Nat := 118140960795 + 7103122 * 2 ^ 59
def prefixEnd_7103122 : Nat := 4983230072969 + 3 ^ 40 * 7103122 * 2
def baseEnd_7103122 : Nat := 3647315733525663236208343

theorem tailTrace_7103122 : CollatzResearch.WordTrace tailWord_7103122 prefixEnd_7103122 3647315733525663236208343 := by
  unfold tailWord_7103122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768035743152396375389905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172714761981739723667706413 64768035743152396375389905)
  ·
    refine ⟨48576026807364297281542429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64768035743152396375389905 48576026807364297281542429)
    ·
      refine ⟨18216010052761611480578411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48576026807364297281542429 18216010052761611480578411)
      ·
        refine ⟨27324015079142417220867617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18216010052761611480578411 27324015079142417220867617)
        ·
          refine ⟨20493011309356812915650713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27324015079142417220867617 20493011309356812915650713)
          ·
            refine ⟨15369758482017609686738035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20493011309356812915650713 15369758482017609686738035)
            ·
              refine ⟨23054637723026414530107053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15369758482017609686738035 23054637723026414530107053)
              ·
                refine ⟨8645489146134905448790145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23054637723026414530107053 8645489146134905448790145)
                ·
                  refine ⟨6484116859601179086592609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645489146134905448790145 6484116859601179086592609)
                  ·
                    refine ⟨4863087644700884314944457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484116859601179086592609 4863087644700884314944457)
                    ·
                      refine ⟨3647315733525663236208343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863087644700884314944457 3647315733525663236208343)
                      ·
                        rfl

theorem cell23_7103122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7103122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103122 prefixEnd_7103122 := by exact prefixLift 7103122
  have htrace : WordTrace (prefixWord ++ tailWord_7103122) baseStart_7103122 baseEnd_7103122 := by
    simpa [prefixWord, tailWord_7103122, baseEnd_7103122] using wordTrace_append hprefix tailTrace_7103122
  have hstable : (prefixWord ++ tailWord_7103122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103122).length < 2 ^ (prefixWord ++ tailWord_7103122).sum := by decide
  have hdescent : baseEnd_7103122 < baseStart_7103122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103178 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_7103178 : Nat := 118140960795 + 7103178 * 2 ^ 59
def prefixEnd_7103178 : Nat := 4983230072969 + 3 ^ 40 * 7103178 * 2
def baseEnd_7103178 : Nat := 3647344488442315017108085

theorem tailTrace_7103178 : CollatzResearch.WordTrace tailWord_7103178 prefixEnd_7103178 3647344488442315017108085 := by
  unfold tailWord_7103178
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768546365101676766399547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172716123640271138043732125 64768546365101676766399547)
  ·
    refine ⟨97152819547652515149599321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64768546365101676766399547 97152819547652515149599321)
    ·
      refine ⟨72864614660739386362199491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97152819547652515149599321 72864614660739386362199491)
      ·
        refine ⟨109296921991109079543299237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72864614660739386362199491 109296921991109079543299237)
        ·
          refine ⟨20493172873332952414368607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109296921991109079543299237 20493172873332952414368607)
          ·
            refine ⟨30739759309999428621552911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20493172873332952414368607 30739759309999428621552911)
            ·
              refine ⟨46109638964999142932329367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30739759309999428621552911 46109638964999142932329367)
              ·
                refine ⟨69164458447498714398494051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46109638964999142932329367 69164458447498714398494051)
                ·
                  refine ⟨103746687671248071597741077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69164458447498714398494051 103746687671248071597741077)
                  ·
                    refine ⟨4863125984589753356144113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103746687671248071597741077 4863125984589753356144113)
                    ·
                      refine ⟨3647344488442315017108085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863125984589753356144113 3647344488442315017108085)
                      ·
                        rfl

theorem cell23_7103178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_7103178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103178 prefixEnd_7103178 := by exact prefixLift 7103178
  have htrace : WordTrace (prefixWord ++ tailWord_7103178) baseStart_7103178 baseEnd_7103178 := by
    simpa [prefixWord, tailWord_7103178, baseEnd_7103178] using wordTrace_append hprefix tailTrace_7103178
  have hstable : (prefixWord ++ tailWord_7103178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103178).length < 2 ^ (prefixWord ++ tailWord_7103178).sum := by decide
  have hdescent : baseEnd_7103178 < baseStart_7103178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103205 : List Nat := [1, 3, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_7103205 : Nat := 118140960795 + 7103205 * 2 ^ 59
def prefixEnd_7103205 : Nat := 4983230072969 + 3 ^ 40 * 7103205 * 2
def baseEnd_7103205 : Nat := 1215786117473328803823487

theorem tailTrace_7103205 : CollatzResearch.WordTrace tailWord_7103205 prefixEnd_7103205 1215786117473328803823487 := by
  unfold tailWord_7103205
  simp only [CollatzResearch.WordTrace]
  refine ⟨259075170231308890676831069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172716780154205927117887379 259075170231308890676831069)
  ·
    refine ⟨97153188836740834003811651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259075170231308890676831069 97153188836740834003811651)
    ·
      refine ⟨145729783255111251005717477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97153188836740834003811651 145729783255111251005717477)
      ·
        refine ⟨27324334360333359563572027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145729783255111251005717477 27324334360333359563572027)
        ·
          refine ⟨40986501540500039345358041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27324334360333359563572027 40986501540500039345358041)
          ·
            refine ⟨30739876155375029509018531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40986501540500039345358041 30739876155375029509018531)
            ·
              refine ⟨46109814233062544263527797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30739876155375029509018531 46109814233062544263527797)
              ·
                refine ⟨4322795084349613524705731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46109814233062544263527797 4322795084349613524705731)
                ·
                  refine ⟨6484192626524420287058597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322795084349613524705731 6484192626524420287058597)
                  ·
                    refine ⟨1215786117473328803823487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484192626524420287058597 1215786117473328803823487)
                    ·
                      rfl

theorem cell23_7103205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_7103205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103205 prefixEnd_7103205 := by exact prefixLift 7103205
  have htrace : WordTrace (prefixWord ++ tailWord_7103205) baseStart_7103205 baseEnd_7103205 := by
    simpa [prefixWord, tailWord_7103205, baseEnd_7103205] using wordTrace_append hprefix tailTrace_7103205
  have hstable : (prefixWord ++ tailWord_7103205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103205).length < 2 ^ (prefixWord ++ tailWord_7103205).sum := by decide
  have hdescent : baseEnd_7103205 < baseStart_7103205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103218 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_7103218 : Nat := 118140960795 + 7103218 * 2 ^ 59
def prefixEnd_7103218 : Nat := 4983230072969 + 3 ^ 40 * 7103218 * 2
def baseEnd_7103218 : Nat := 405262780852054984511989

theorem tailTrace_7103218 : CollatzResearch.WordTrace tailWord_7103218 prefixEnd_7103218 405262780852054984511989 := by
  unfold tailWord_7103218
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768911095065448474263577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172717096253507862598036205 64768911095065448474263577)
  ·
    refine ⟨48576683321299086355697683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64768911095065448474263577 48576683321299086355697683)
    ·
      refine ⟨72865024981948629533546525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48576683321299086355697683 72865024981948629533546525)
      ·
        refine ⟨27324384368230736075079947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72865024981948629533546525 27324384368230736075079947)
        ·
          refine ⟨40986576552346104112619921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27324384368230736075079947 40986576552346104112619921)
          ·
            refine ⟨30739932414259578084464941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40986576552346104112619921 30739932414259578084464941)
            ·
              refine ⟨11527474655347341781674353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30739932414259578084464941 11527474655347341781674353)
              ·
                refine ⟨8645605991510506336255765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527474655347341781674353 8645605991510506336255765)
                ·
                  refine ⟨405262780852054984511989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8645605991510506336255765 405262780852054984511989)
                  ·
                    rfl

theorem cell23_7103218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_7103218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103218 prefixEnd_7103218 := by exact prefixLift 7103218
  have htrace : WordTrace (prefixWord ++ tailWord_7103218) baseStart_7103218 baseEnd_7103218 := by
    simpa [prefixWord, tailWord_7103218, baseEnd_7103218] using wordTrace_append hprefix tailTrace_7103218
  have hstable : (prefixWord ++ tailWord_7103218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103218).length < 2 ^ (prefixWord ++ tailWord_7103218).sum := by decide
  have hdescent : baseEnd_7103218 < baseStart_7103218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103281 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7103281 : Nat := 118140960795 + 7103281 * 2 ^ 59
def prefixEnd_7103281 : Nat := 4983230072969 + 3 ^ 40 * 7103281 * 2
def baseEnd_7103281 : Nat := 3647397376949728114120111

theorem tailTrace_7103281 : CollatzResearch.WordTrace tailWord_7103281 prefixEnd_7103281 3647397376949728114120111 := by
  unfold tailWord_7103281
  simp only [CollatzResearch.WordTrace]
  refine ⟨259077942179033555656597697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172718628119355703771065131 259077942179033555656597697)
  ·
    refine ⟨194308456634275166742448273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259077942179033555656597697 194308456634275166742448273)
    ·
      refine ⟨145731342475706375056836205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194308456634275166742448273 145731342475706375056836205)
      ·
        refine ⟨54649253428389890646313577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145731342475706375056836205 54649253428389890646313577)
        ·
          refine ⟨40986940071292417984735183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54649253428389890646313577 40986940071292417984735183)
          ·
            refine ⟨61480410106938626977102775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40986940071292417984735183 61480410106938626977102775)
            ·
              refine ⟨92220615160407940465654163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61480410106938626977102775 92220615160407940465654163)
              ·
                refine ⟨138330922740611910698481245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92220615160407940465654163 138330922740611910698481245)
                ·
                  refine ⟨51874096027729466511930467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138330922740611910698481245 51874096027729466511930467)
                  ·
                    refine ⟨77811144041594199767895701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51874096027729466511930467 77811144041594199767895701)
                    ·
                      refine ⟨3647397376949728114120111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77811144041594199767895701 3647397376949728114120111)
                      ·
                        rfl

theorem cell23_7103281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7103281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103281 prefixEnd_7103281 := by exact prefixLift 7103281
  have htrace : WordTrace (prefixWord ++ tailWord_7103281) baseStart_7103281 baseEnd_7103281 := by
    simpa [prefixWord, tailWord_7103281, baseEnd_7103281] using wordTrace_append hprefix tailTrace_7103281
  have hstable : (prefixWord ++ tailWord_7103281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103281).length < 2 ^ (prefixWord ++ tailWord_7103281).sum := by decide
  have hdescent : baseEnd_7103281 < baseStart_7103281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103288 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_7103288 : Nat := 118140960795 + 7103288 * 2 ^ 59
def prefixEnd_7103288 : Nat := 4983230072969 + 3 ^ 40 * 7103288 * 2
def baseEnd_7103288 : Nat := 3647400971314309586732579

theorem tailTrace_7103288 : CollatzResearch.WordTrace tailWord_7103288 prefixEnd_7103288 3647400971314309586732579 := by
  unfold tailWord_7103288
  simp only [CollatzResearch.WordTrace]
  refine ⟨129539098745004097926051259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172718798326672130568068345 129539098745004097926051259)
  ·
    refine ⟨194308648117506146889076889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129539098745004097926051259 194308648117506146889076889)
    ·
      refine ⟨145731486088129610166807667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194308648117506146889076889 145731486088129610166807667)
      ·
        refine ⟨218597229132194415250211501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145731486088129610166807667 218597229132194415250211501)
        ·
          refine ⟨81973960924572905718829313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218597229132194415250211501 81973960924572905718829313)
          ·
            refine ⟨61480470693429679289121985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81973960924572905718829313 61480470693429679289121985)
            ·
              refine ⟨46110353020072259466841489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61480470693429679289121985 46110353020072259466841489)
              ·
                refine ⟨34582764765054194600131117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46110353020072259466841489 34582764765054194600131117)
                ·
                  refine ⟨12968536786895322975049169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34582764765054194600131117 12968536786895322975049169)
                  ·
                    refine ⟨9726402590171492231286877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12968536786895322975049169 9726402590171492231286877)
                    ·
                      refine ⟨3647400971314309586732579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726402590171492231286877 3647400971314309586732579)
                      ·
                        rfl

theorem cell23_7103288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_7103288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103288 prefixEnd_7103288 := by exact prefixLift 7103288
  have htrace : WordTrace (prefixWord ++ tailWord_7103288) baseStart_7103288 baseEnd_7103288 := by
    simpa [prefixWord, tailWord_7103288, baseEnd_7103288] using wordTrace_append hprefix tailTrace_7103288
  have hstable : (prefixWord ++ tailWord_7103288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103288).length < 2 ^ (prefixWord ++ tailWord_7103288).sum := by decide
  have hdescent : baseEnd_7103288 < baseStart_7103288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103295 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 2, 4]
def baseStart_7103295 : Nat := 118140960795 + 7103295 * 2 ^ 59
def prefixEnd_7103295 : Nat := 4983230072969 + 3 ^ 40 * 7103295 * 2
def baseEnd_7103295 : Nat := 1215801521892963686448349

theorem tailTrace_7103295 : CollatzResearch.WordTrace tailWord_7103295 prefixEnd_7103295 1215801521892963686448349 := by
  unfold tailWord_7103295
  simp only [CollatzResearch.WordTrace]
  refine ⟨259078452800982836047607339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172718968533988557365071559 259078452800982836047607339)
  ·
    refine ⟨388617679201474254071411009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259078452800982836047607339 388617679201474254071411009)
    ·
      refine ⟨291463259401105690553558257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388617679201474254071411009 291463259401105690553558257)
      ·
        refine ⟨218597444550829267915168693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291463259401105690553558257 218597444550829267915168693)
        ·
          refine ⟨20493510426640243867047065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218597444550829267915168693 20493510426640243867047065)
          ·
            refine ⟨15370132819980182900285299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20493510426640243867047065 15370132819980182900285299)
            ·
              refine ⟨23055199229970274350427949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15370132819980182900285299 23055199229970274350427949)
              ·
                refine ⟨8645699711238852881410481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23055199229970274350427949 8645699711238852881410481)
                ·
                  refine ⟨6484274783429139661057861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645699711238852881410481 6484274783429139661057861)
                  ·
                    refine ⟨1215801521892963686448349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484274783429139661057861 1215801521892963686448349)
                    ·
                      rfl

theorem cell23_7103295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_7103295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103295 prefixEnd_7103295 := by exact prefixLift 7103295
  have htrace : WordTrace (prefixWord ++ tailWord_7103295) baseStart_7103295 baseEnd_7103295 := by
    simpa [prefixWord, tailWord_7103295, baseEnd_7103295] using wordTrace_append hprefix tailTrace_7103295
  have hstable : (prefixWord ++ tailWord_7103295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103295).length < 2 ^ (prefixWord ++ tailWord_7103295).sum := by decide
  have hdescent : baseEnd_7103295 < baseStart_7103295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103305 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_7103305 : Nat := 118140960795 + 7103305 * 2 ^ 59
def prefixEnd_7103305 : Nat := 4983230072969 + 3 ^ 40 * 7103305 * 2
def baseEnd_7103305 : Nat := 3647409700485436020220001

theorem tailTrace_7103305 : CollatzResearch.WordTrace tailWord_7103305 prefixEnd_7103305 3647409700485436020220001 := by
  unfold tailWord_7103305
  simp only [CollatzResearch.WordTrace]
  refine ⟨259078817530946607755471369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172719211687297738503647579 259078817530946607755471369)
  ·
    refine ⟨194309113148209955816603527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259078817530946607755471369 194309113148209955816603527)
    ·
      refine ⟨291463669722314933724905291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194309113148209955816603527 291463669722314933724905291)
      ·
        refine ⟨437195504583472400587357937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291463669722314933724905291 437195504583472400587357937)
        ·
          refine ⟨327896628437604300440518453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437195504583472400587357937 327896628437604300440518453)
          ·
            refine ⟨30740308916025403166298605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327896628437604300440518453 30740308916025403166298605)
            ·
              refine ⟨11527615843509526187361977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30740308916025403166298605 11527615843509526187361977)
              ·
                refine ⟨8645711882632144640521483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527615843509526187361977 8645711882632144640521483)
                ·
                  refine ⟨12968567823948216960782225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8645711882632144640521483 12968567823948216960782225)
                  ·
                    refine ⟨9726425867961162720586669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12968567823948216960782225 9726425867961162720586669)
                    ·
                      refine ⟨3647409700485436020220001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726425867961162720586669 3647409700485436020220001)
                      ·
                        rfl

theorem cell23_7103305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_7103305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103305 prefixEnd_7103305 := by exact prefixLift 7103305
  have htrace : WordTrace (prefixWord ++ tailWord_7103305) baseStart_7103305 baseEnd_7103305 := by
    simpa [prefixWord, tailWord_7103305, baseEnd_7103305] using wordTrace_append hprefix tailTrace_7103305
  have hstable : (prefixWord ++ tailWord_7103305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103305).length < 2 ^ (prefixWord ++ tailWord_7103305).sum := by decide
  have hdescent : baseEnd_7103305 < baseStart_7103305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103322 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_7103322 : Nat := 118140960795 + 7103322 * 2 ^ 59
def prefixEnd_7103322 : Nat := 4983230072969 + 3 ^ 40 * 7103322 * 2
def baseEnd_7103322 : Nat := 3647418429656562453707423

theorem tailTrace_7103322 : CollatzResearch.WordTrace tailWord_7103322 prefixEnd_7103322 3647418429656562453707423 := by
  unfold tailWord_7103322
  simp only [CollatzResearch.WordTrace]
  refine ⟨64769859392971254914710055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172719625047923346439226813 64769859392971254914710055)
  ·
    refine ⟨97154789089456882372065083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64769859392971254914710055 97154789089456882372065083)
    ·
      refine ⟨145732183634185323558097625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97154789089456882372065083 145732183634185323558097625)
      ·
        refine ⟨109299137725638992668573219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145732183634185323558097625 109299137725638992668573219)
        ·
          refine ⟨163948706588458489002859829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109299137725638992668573219 163948706588458489002859829)
          ·
            refine ⟨15370191242667983344018109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163948706588458489002859829 15370191242667983344018109)
            ·
              refine ⟨5763821716000493754006791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15370191242667983344018109 5763821716000493754006791)
              ·
                refine ⟨8645732574000740631010187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5763821716000493754006791 8645732574000740631010187)
                ·
                  refine ⟨12968598861001110946515281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8645732574000740631010187 12968598861001110946515281)
                  ·
                    refine ⟨9726449145750833209886461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12968598861001110946515281 9726449145750833209886461)
                    ·
                      refine ⟨3647418429656562453707423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726449145750833209886461 3647418429656562453707423)
                      ·
                        rfl

theorem cell23_7103322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_7103322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103322 prefixEnd_7103322 := by exact prefixLift 7103322
  have htrace : WordTrace (prefixWord ++ tailWord_7103322) baseStart_7103322 baseEnd_7103322 := by
    simpa [prefixWord, tailWord_7103322, baseEnd_7103322] using wordTrace_append hprefix tailTrace_7103322
  have hstable : (prefixWord ++ tailWord_7103322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103322).length < 2 ^ (prefixWord ++ tailWord_7103322).sum := by decide
  have hdescent : baseEnd_7103322 < baseStart_7103322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103336 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7103336 : Nat := 118140960795 + 7103336 * 2 ^ 59
def prefixEnd_7103336 : Nat := 4983230072969 + 3 ^ 40 * 7103336 * 2
def baseEnd_7103336 : Nat := 3647425618385725398932359

theorem tailTrace_7103336 : CollatzResearch.WordTrace tailWord_7103336 prefixEnd_7103336 3647425618385725398932359 := by
  unfold tailWord_7103336
  simp only [CollatzResearch.WordTrace]
  refine ⟨129539974096917150024924931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172719965462556200033233241 129539974096917150024924931)
  ·
    refine ⟨194309961145375725037387397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129539974096917150024924931 194309961145375725037387397)
    ·
      refine ⟨36433117714757948444510137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194309961145375725037387397 36433117714757948444510137)
      ·
        refine ⟨27324838286068461333382603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36433117714757948444510137 27324838286068461333382603)
        ·
          refine ⟨40987257429102692000073905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27324838286068461333382603 40987257429102692000073905)
          ·
            refine ⟨30740443071827019000055429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40987257429102692000073905 30740443071827019000055429)
            ·
              refine ⟨5763833075967566062510393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30740443071827019000055429 5763833075967566062510393)
              ·
                refine ⟨4322874806975674546882795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763833075967566062510393 4322874806975674546882795)
                ·
                  refine ⟨6484312210463511820324193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322874806975674546882795 6484312210463511820324193)
                  ·
                    refine ⟨4863234157847633865243145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484312210463511820324193 4863234157847633865243145)
                    ·
                      refine ⟨3647425618385725398932359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863234157847633865243145 3647425618385725398932359)
                      ·
                        rfl

theorem cell23_7103336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7103336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103336 prefixEnd_7103336 := by exact prefixLift 7103336
  have htrace : WordTrace (prefixWord ++ tailWord_7103336) baseStart_7103336 baseEnd_7103336 := by
    simpa [prefixWord, tailWord_7103336, baseEnd_7103336] using wordTrace_append hprefix tailTrace_7103336
  have hstable : (prefixWord ++ tailWord_7103336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103336).length < 2 ^ (prefixWord ++ tailWord_7103336).sum := by decide
  have hdescent : baseEnd_7103336 < baseStart_7103336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103342 : List Nat := [4, 1, 2, 3, 3, 1, 1, 8]
def baseStart_7103342 : Nat := 118140960795 + 7103342 * 2 ^ 59
def prefixEnd_7103342 : Nat := 4983230072969 + 3 ^ 40 * 7103342 * 2
def baseEnd_7103342 : Nat := 135089951824801939831753

theorem tailTrace_7103342 : CollatzResearch.WordTrace tailWord_7103342 prefixEnd_7103342 135089951824801939831753 := by
  unfold tailWord_7103342
  simp only [CollatzResearch.WordTrace]
  refine ⟨32385020878976570384321035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172720111354541708716378853 32385020878976570384321035)
  ·
    refine ⟨48577531318464855576481553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32385020878976570384321035 48577531318464855576481553)
    ·
      refine ⟨36433148488848641682361165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48577531318464855576481553 36433148488848641682361165)
      ·
        refine ⟨13662430683318240630885437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36433148488848641682361165 13662430683318240630885437)
        ·
          refine ⟨5123411506244340236582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13662430683318240630885437 5123411506244340236582039)
          ·
            refine ⟨7685117259366510354873059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123411506244340236582039 7685117259366510354873059)
            ·
              refine ⟨11527675889049765532309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685117259366510354873059 11527675889049765532309589)
              ·
                refine ⟨135089951824801939831753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11527675889049765532309589 135089951824801939831753)
                ·
                  rfl

theorem cell23_7103342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_7103342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103342 prefixEnd_7103342 := by exact prefixLift 7103342
  have htrace : WordTrace (prefixWord ++ tailWord_7103342) baseStart_7103342 baseEnd_7103342 := by
    simpa [prefixWord, tailWord_7103342, baseEnd_7103342] using wordTrace_append hprefix tailTrace_7103342
  have hstable : (prefixWord ++ tailWord_7103342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103342).length < 2 ^ (prefixWord ++ tailWord_7103342).sum := by decide
  have hdescent : baseEnd_7103342 < baseStart_7103342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103345 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_7103345 : Nat := 118140960795 + 7103345 * 2 ^ 59
def prefixEnd_7103345 : Nat := 4983230072969 + 3 ^ 40 * 7103345 * 2
def baseEnd_7103345 : Nat := 3647430239711615863719817

theorem tailTrace_7103345 : CollatzResearch.WordTrace tailWord_7103345 prefixEnd_7103345 3647430239711615863719817 := by
  unfold tailWord_7103345
  simp only [CollatzResearch.WordTrace]
  refine ⟨259080276450801694586927489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172720184300534463057951659 259080276450801694586927489)
  ·
    refine ⟨194310207338101270940195617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259080276450801694586927489 194310207338101270940195617)
    ·
      refine ⟨145732655503575953205146713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194310207338101270940195617 145732655503575953205146713)
      ·
        refine ⟨109299491627681964903860035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145732655503575953205146713 109299491627681964903860035)
        ·
          refine ⟨163949237441522947355790053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109299491627681964903860035 163949237441522947355790053)
          ·
            refine ⟨30740482020285552629210635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163949237441522947355790053 30740482020285552629210635)
            ·
              refine ⟨46110723030428328943815953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30740482020285552629210635 46110723030428328943815953)
              ·
                refine ⟨34583042272821246707861965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46110723030428328943815953 34583042272821246707861965)
                ·
                  refine ⟨12968640852307967515448237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34583042272821246707861965 12968640852307967515448237)
                  ·
                    refine ⟨4863240319615487818293089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12968640852307967515448237 4863240319615487818293089)
                    ·
                      refine ⟨3647430239711615863719817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863240319615487818293089 3647430239711615863719817)
                      ·
                        rfl

theorem cell23_7103345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_7103345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103345 prefixEnd_7103345 := by exact prefixLift 7103345
  have htrace : WordTrace (prefixWord ++ tailWord_7103345) baseStart_7103345 baseEnd_7103345 := by
    simpa [prefixWord, tailWord_7103345, baseEnd_7103345] using wordTrace_append hprefix tailTrace_7103345
  have hstable : (prefixWord ++ tailWord_7103345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103345).length < 2 ^ (prefixWord ++ tailWord_7103345).sum := by decide
  have hdescent : baseEnd_7103345 < baseStart_7103345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103386 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7103386 : Nat := 118140960795 + 7103386 * 2 ^ 59
def prefixEnd_7103386 : Nat := 4983230072969 + 3 ^ 40 * 7103386 * 2
def baseEnd_7103386 : Nat := 3647451292418450203307129

theorem tailTrace_7103386 : CollatzResearch.WordTrace tailWord_7103386 prefixEnd_7103386 3647451292418450203307129 := by
  unfold tailWord_7103386
  simp only [CollatzResearch.WordTrace]
  refine ⟨64770442960913289647292503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172721181229102105726113341 64770442960913289647292503)
  ·
    refine ⟨97155664441369934470938755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64770442960913289647292503 97155664441369934470938755)
    ·
      refine ⟨145733496662054901706408133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97155664441369934470938755 145733496662054901706408133)
      ·
        refine ⟨27325030624135294069951525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145733496662054901706408133 27325030624135294069951525)
        ·
          refine ⟨5123443242025367638115911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27325030624135294069951525 5123443242025367638115911)
          ·
            refine ⟨7685164863038051457173867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123443242025367638115911 7685164863038051457173867)
            ·
              refine ⟨11527747294557077185760801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685164863038051457173867 11527747294557077185760801)
              ·
                refine ⟨8645810470917807889320601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527747294557077185760801 8645810470917807889320601)
                ·
                  refine ⟨6484357853188355916990451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8645810470917807889320601 6484357853188355916990451)
                  ·
                    refine ⟨9726536779782533875485677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484357853188355916990451 9726536779782533875485677)
                    ·
                      refine ⟨3647451292418450203307129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726536779782533875485677 3647451292418450203307129)
                      ·
                        rfl

theorem cell23_7103386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7103386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103386 prefixEnd_7103386 := by exact prefixLift 7103386
  have htrace : WordTrace (prefixWord ++ tailWord_7103386) baseStart_7103386 baseEnd_7103386 := by
    simpa [prefixWord, tailWord_7103386, baseEnd_7103386] using wordTrace_append hprefix tailTrace_7103386
  have hstable : (prefixWord ++ tailWord_7103386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103386).length < 2 ^ (prefixWord ++ tailWord_7103386).sum := by decide
  have hdescent : baseEnd_7103386 < baseStart_7103386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
