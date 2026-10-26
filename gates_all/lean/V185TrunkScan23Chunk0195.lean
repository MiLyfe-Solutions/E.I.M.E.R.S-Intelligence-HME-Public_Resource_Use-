import V185TrunkScan23Chunk0194

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1154851 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1154851 : Nat := 118140960795 + 1154851 * 2 ^ 59
def prefixEnd_1154851 : Nat := 4983230072969 + 3 ^ 40 * 1154851 * 2
def baseEnd_1154851 : Nat := 592993647325566373851443

theorem tailTrace_1154851 : CollatzResearch.WordTrace tailWord_1154851 prefixEnd_1154851 592993647325566373851443 := by
  unfold tailWord_1154851
  simp only [CollatzResearch.WordTrace]
  refine ⟨42120876339179534693400407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28080584226119689795600271 42120876339179534693400407)
  ·
    refine ⟨63181314508769302040100611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42120876339179534693400407 63181314508769302040100611)
    ·
      refine ⟨94771971763153953060150917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63181314508769302040100611 94771971763153953060150917)
      ·
        refine ⟨17769744705591366198778297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94771971763153953060150917 17769744705591366198778297)
        ·
          refine ⟨13327308529193524649083723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17769744705591366198778297 13327308529193524649083723)
          ·
            refine ⟨19990962793790286973625585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13327308529193524649083723 19990962793790286973625585)
            ·
              refine ⟨14993222095342715230219189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19990962793790286973625585 14993222095342715230219189)
              ·
                refine ⟨1405614571438379552833049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14993222095342715230219189 1405614571438379552833049)
                ·
                  refine ⟨1054210928578784664624787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405614571438379552833049 1054210928578784664624787)
                  ·
                    refine ⟨1581316392868176996937181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054210928578784664624787 1581316392868176996937181)
                    ·
                      refine ⟨592993647325566373851443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581316392868176996937181 592993647325566373851443)
                      ·
                        rfl

theorem cell23_1154851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1154851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154851 prefixEnd_1154851 := by exact prefixLift 1154851
  have htrace : WordTrace (prefixWord ++ tailWord_1154851) baseStart_1154851 baseEnd_1154851 := by
    simpa [prefixWord, tailWord_1154851, baseEnd_1154851] using wordTrace_append hprefix tailTrace_1154851
  have hstable : (prefixWord ++ tailWord_1154851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154851).length < 2 ^ (prefixWord ++ tailWord_1154851).sum := by decide
  have hdescent : baseEnd_1154851 < baseStart_1154851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154868 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1154868 : Nat := 118140960795 + 1154868 * 2 ^ 59
def prefixEnd_1154868 : Nat := 4983230072969 + 3 ^ 40 * 1154868 * 2
def baseEnd_1154868 : Nat := 593002376496692807338865

theorem tailTrace_1154868 : CollatzResearch.WordTrace tailWord_1154868 prefixEnd_1154868 593002376496692807338865 := by
  unfold tailWord_1154868
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060748190058973298384629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28080997586745297731179505 21060748190058973298384629)
  ·
    refine ⟨1974445142818028746723559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21060748190058973298384629 1974445142818028746723559)
    ·
      refine ⟨2961667714227043120085339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974445142818028746723559 2961667714227043120085339)
      ·
        refine ⟨4442501571340564680128009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961667714227043120085339 4442501571340564680128009)
        ·
          refine ⟨3331876178505423510096007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4442501571340564680128009 3331876178505423510096007)
          ·
            refine ⟨4997814267758135265144011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3331876178505423510096007 4997814267758135265144011)
            ·
              refine ⟨7496721401637202897716017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997814267758135265144011 7496721401637202897716017)
              ·
                refine ⟨5622541051227902173287013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7496721401637202897716017 5622541051227902173287013)
                ·
                  refine ⟨1054226447105231657491315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5622541051227902173287013 1054226447105231657491315)
                  ·
                    refine ⟨1581339670657847486236973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054226447105231657491315 1581339670657847486236973)
                    ·
                      refine ⟨593002376496692807338865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581339670657847486236973 593002376496692807338865)
                      ·
                        rfl

theorem cell23_1154868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1154868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154868 prefixEnd_1154868 := by exact prefixLift 1154868
  have htrace : WordTrace (prefixWord ++ tailWord_1154868) baseStart_1154868 baseEnd_1154868 := by
    simpa [prefixWord, tailWord_1154868, baseEnd_1154868] using wordTrace_append hprefix tailTrace_1154868
  have hstable : (prefixWord ++ tailWord_1154868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154868).length < 2 ^ (prefixWord ++ tailWord_1154868).sum := by decide
  have hdescent : baseEnd_1154868 < baseStart_1154868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154869 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_1154869 : Nat := 118140960795 + 1154869 * 2 ^ 59
def prefixEnd_1154869 : Nat := 4983230072969 + 3 ^ 40 * 1154869 * 2
def baseEnd_1154869 : Nat := 593002889977347303426361

theorem tailTrace_1154869 : CollatzResearch.WordTrace tailWord_1154869 prefixEnd_1154869 593002889977347303426361 := by
  unfold tailWord_1154869
  simp only [CollatzResearch.WordTrace]
  refine ⟨42121532853114323767555661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28081021902076215845037107 42121532853114323767555661)
  ·
    refine ⟨15795574819917871412833373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42121532853114323767555661 15795574819917871412833373)
    ·
      refine ⟨5923340557469201779812515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15795574819917871412833373 5923340557469201779812515)
      ·
        refine ⟨8885010836203802669718773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5923340557469201779812515 8885010836203802669718773)
        ·
          refine ⟨832969765894106500286135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8885010836203802669718773 832969765894106500286135)
          ·
            refine ⟨1249454648841159750429203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832969765894106500286135 1249454648841159750429203)
            ·
              refine ⟨1874181973261739625643805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249454648841159750429203 1874181973261739625643805)
              ·
                refine ⟨702818239973152359616427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874181973261739625643805 702818239973152359616427)
                ·
                  refine ⟨1054227359959728539424641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702818239973152359616427 1054227359959728539424641)
                  ·
                    refine ⟨790670519969796404568481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054227359959728539424641 790670519969796404568481)
                    ·
                      refine ⟨593002889977347303426361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790670519969796404568481 593002889977347303426361)
                      ·
                        rfl

theorem cell23_1154869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_1154869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154869 prefixEnd_1154869 := by exact prefixLift 1154869
  have htrace : WordTrace (prefixWord ++ tailWord_1154869) baseStart_1154869 baseEnd_1154869 := by
    simpa [prefixWord, tailWord_1154869, baseEnd_1154869] using wordTrace_append hprefix tailTrace_1154869
  have hstable : (prefixWord ++ tailWord_1154869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154869).length < 2 ^ (prefixWord ++ tailWord_1154869).sum := by decide
  have hdescent : baseEnd_1154869 < baseStart_1154869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154886 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1154886 : Nat := 118140960795 + 1154886 * 2 ^ 59
def prefixEnd_1154886 : Nat := 4983230072969 + 3 ^ 40 * 1154886 * 2
def baseEnd_1154886 : Nat := 593011619148473736913783

theorem tailTrace_1154886 : CollatzResearch.WordTrace tailWord_1154886 prefixEnd_1154886 593011619148473736913783 := by
  unfold tailWord_1154886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316317277939147989716391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28081435262701823780616341 1316317277939147989716391)
  ·
    refine ⟨1974475916908721984574587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316317277939147989716391 1974475916908721984574587)
    ·
      refine ⟨2961713875363082976861881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974475916908721984574587 2961713875363082976861881)
      ·
        refine ⟨2221285406522312232646411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2961713875363082976861881 2221285406522312232646411)
        ·
          refine ⟨3331928109783468348969617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221285406522312232646411 3331928109783468348969617)
          ·
            refine ⟨2498946082337601261727213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331928109783468348969617 2498946082337601261727213)
            ·
              refine ⟨937104780876600473147705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2498946082337601261727213 937104780876600473147705)
              ·
                refine ⟨702828585657450354860779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937104780876600473147705 702828585657450354860779)
                ·
                  refine ⟨1054242878486175532291169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702828585657450354860779 1054242878486175532291169)
                  ·
                    refine ⟨790682158864631649218377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054242878486175532291169 790682158864631649218377)
                    ·
                      refine ⟨593011619148473736913783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790682158864631649218377 593011619148473736913783)
                      ·
                        rfl

theorem cell23_1154886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1154886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154886 prefixEnd_1154886 := by exact prefixLift 1154886
  have htrace : WordTrace (prefixWord ++ tailWord_1154886) baseStart_1154886 baseEnd_1154886 := by
    simpa [prefixWord, tailWord_1154886, baseEnd_1154886] using wordTrace_append hprefix tailTrace_1154886
  have hstable : (prefixWord ++ tailWord_1154886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154886).length < 2 ^ (prefixWord ++ tailWord_1154886).sum := by decide
  have hdescent : baseEnd_1154886 < baseStart_1154886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154942 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1154942 : Nat := 118140960795 + 1154942 * 2 ^ 59
def prefixEnd_1154942 : Nat := 4983230072969 + 3 ^ 40 * 1154942 * 2
def baseEnd_1154942 : Nat := 593040374065125517813525

theorem tailTrace_1154942 : CollatzResearch.WordTrace tailWord_1154942 prefixEnd_1154942 593040374065125517813525 := by
  unfold tailWord_1154942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265524422731232154370385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28082796921233238156642053 5265524422731232154370385)
  ·
    refine ⟨3949143317048424115777789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5265524422731232154370385 3949143317048424115777789)
    ·
      refine ⟨1480928743893159043416671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3949143317048424115777789 1480928743893159043416671)
      ·
        refine ⟨2221393115839738565125007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480928743893159043416671 2221393115839738565125007)
        ·
          refine ⟨3332089673759607847687511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221393115839738565125007 3332089673759607847687511)
          ·
            refine ⟨4998134510639411771531267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332089673759607847687511 4998134510639411771531267)
            ·
              refine ⟨7497201765959117657296901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998134510639411771531267 7497201765959117657296901)
              ·
                refine ⟨1405725331117334560743169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7497201765959117657296901 1405725331117334560743169)
                ·
                  refine ⟨1054293998338000920557377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405725331117334560743169 1054293998338000920557377)
                  ·
                    refine ⟨790720498753500690418033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054293998338000920557377 790720498753500690418033)
                    ·
                      refine ⟨593040374065125517813525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790720498753500690418033 593040374065125517813525)
                      ·
                        rfl

theorem cell23_1154942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1154942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154942 prefixEnd_1154942 := by exact prefixLift 1154942
  have htrace : WordTrace (prefixWord ++ tailWord_1154942) baseStart_1154942 baseEnd_1154942 := by
    simpa [prefixWord, tailWord_1154942, baseEnd_1154942] using wordTrace_append hprefix tailTrace_1154942
  have hstable : (prefixWord ++ tailWord_1154942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154942).length < 2 ^ (prefixWord ++ tailWord_1154942).sum := by decide
  have hdescent : baseEnd_1154942 < baseStart_1154942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154944 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_1154944 : Nat := 118140960795 + 1154944 * 2 ^ 59
def prefixEnd_1154944 : Nat := 4983230072969 + 3 ^ 40 * 1154944 * 2
def baseEnd_1154944 : Nat := 197680467008811503329505

theorem tailTrace_1154944 : CollatzResearch.WordTrace tailWord_1154944 prefixEnd_1154944 197680467008811503329505 := by
  unfold tailWord_1154944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062134163921305788267943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28082845551895074384357257 21062134163921305788267943)
  ·
    refine ⟨31593201245881958682401915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21062134163921305788267943 31593201245881958682401915)
    ·
      refine ⟨47389801868822938023602873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31593201245881958682401915 47389801868822938023602873)
      ·
        refine ⟨35542351401617203517702155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47389801868822938023602873 35542351401617203517702155)
        ·
          refine ⟨53313527102425805276553233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35542351401617203517702155 53313527102425805276553233)
          ·
            refine ⟨39985145326819353957414925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53313527102425805276553233 39985145326819353957414925)
            ·
              refine ⟨14994429497557257734030597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39985145326819353957414925 14994429497557257734030597)
              ·
                refine ⟨2811455530791985825130737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14994429497557257734030597 2811455530791985825130737)
                ·
                  refine ⟨2108591648093989368848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2811455530791985825130737 2108591648093989368848053)
                  ·
                    refine ⟨197680467008811503329505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2108591648093989368848053 197680467008811503329505)
                    ·
                      rfl

theorem cell23_1154944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_1154944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154944 prefixEnd_1154944 := by exact prefixLift 1154944
  have htrace : WordTrace (prefixWord ++ tailWord_1154944) baseStart_1154944 baseEnd_1154944 := by
    simpa [prefixWord, tailWord_1154944, baseEnd_1154944] using wordTrace_append hprefix tailTrace_1154944
  have hstable : (prefixWord ++ tailWord_1154944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154944).length < 2 ^ (prefixWord ++ tailWord_1154944).sum := by decide
  have hdescent : baseEnd_1154944 < baseStart_1154944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154948 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1154948 : Nat := 118140960795 + 1154948 * 2 ^ 59
def prefixEnd_1154948 : Nat := 4983230072969 + 3 ^ 40 * 1154948 * 2
def baseEnd_1154948 : Nat := 65893717216561388259833

theorem tailTrace_1154948 : CollatzResearch.WordTrace tailWord_1154948 prefixEnd_1154948 65893717216561388259833 := by
  unfold tailWord_1154948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062207109914060129840749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28082942813218746839787665 21062207109914060129840749)
  ·
    refine ⟨7898327666217772548690281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21062207109914060129840749 7898327666217772548690281)
    ·
      refine ⟨5923745749663329411517711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7898327666217772548690281 5923745749663329411517711)
      ·
        refine ⟨8885618624494994117276567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5923745749663329411517711 8885618624494994117276567)
        ·
          refine ⟨13328427936742491175914851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8885618624494994117276567 13328427936742491175914851)
          ·
            refine ⟨19992641905113736763872277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328427936742491175914851 19992641905113736763872277)
            ·
              refine ⟨937155089302206410806513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19992641905113736763872277 937155089302206410806513)
              ·
                refine ⟨702866316976654808104885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937155089302206410806513 702866316976654808104885)
                ·
                  refine ⟨65893717216561388259833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702866316976654808104885 65893717216561388259833)
                  ·
                    rfl

theorem cell23_1154948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1154948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154948 prefixEnd_1154948 := by exact prefixLift 1154948
  have htrace : WordTrace (prefixWord ++ tailWord_1154948) baseStart_1154948 baseEnd_1154948 := by
    simpa [prefixWord, tailWord_1154948, baseEnd_1154948] using wordTrace_append hprefix tailTrace_1154948
  have hstable : (prefixWord ++ tailWord_1154948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154948).length < 2 ^ (prefixWord ++ tailWord_1154948).sum := by decide
  have hdescent : baseEnd_1154948 < baseStart_1154948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154994 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1154994 : Nat := 118140960795 + 1154994 * 2 ^ 59
def prefixEnd_1154994 : Nat := 4983230072969 + 3 ^ 40 * 1154994 * 2
def baseEnd_1154994 : Nat := 593067075059159314363285

theorem tailTrace_1154994 : CollatzResearch.WordTrace tailWord_1154994 prefixEnd_1154994 593067075059159314363285 := by
  unfold tailWord_1154994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531522994415367528964009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28084061318440980077237357 10531522994415367528964009)
  ·
    refine ⟨7898642245811525646723007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10531522994415367528964009 7898642245811525646723007)
    ·
      refine ⟨11847963368717288470084511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7898642245811525646723007 11847963368717288470084511)
      ·
        refine ⟨17771945053075932705126767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11847963368717288470084511 17771945053075932705126767)
        ·
          refine ⟨26657917579613899057690151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17771945053075932705126767 26657917579613899057690151)
          ·
            refine ⟨39986876369420848586535227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26657917579613899057690151 39986876369420848586535227)
            ·
              refine ⟨59980314554131272879802841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39986876369420848586535227 59980314554131272879802841)
              ·
                refine ⟨44985235915598454659852131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59980314554131272879802841 44985235915598454659852131)
                ·
                  refine ⟨67477853873397681989778197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44985235915598454659852131 67477853873397681989778197)
                  ·
                    refine ⟨3163024400315516343270853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67477853873397681989778197 3163024400315516343270853)
                    ·
                      refine ⟨593067075059159314363285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3163024400315516343270853 593067075059159314363285)
                      ·
                        rfl

theorem cell23_1154994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1154994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154994 prefixEnd_1154994 := by exact prefixLift 1154994
  have htrace : WordTrace (prefixWord ++ tailWord_1154994) baseStart_1154994 baseEnd_1154994 := by
    simpa [prefixWord, tailWord_1154994, baseEnd_1154994] using wordTrace_append hprefix tailTrace_1154994
  have hstable : (prefixWord ++ tailWord_1154994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154994).length < 2 ^ (prefixWord ++ tailWord_1154994).sum := by decide
  have hdescent : baseEnd_1154994 < baseStart_1154994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155001 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1155001 : Nat := 118140960795 + 1155001 * 2 ^ 59
def prefixEnd_1155001 : Nat := 4983230072969 + 3 ^ 40 * 1155001 * 2
def baseEnd_1155001 : Nat := 593070669423740786975753

theorem tailTrace_1155001 : CollatzResearch.WordTrace tailWord_1155001 prefixEnd_1155001 593070669423740786975753 := by
  unfold tailWord_1155001
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126347288636110311360857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28084231525757406874240571 42126347288636110311360857)
  ·
    refine ⟨31594760466477082733520643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42126347288636110311360857 31594760466477082733520643)
    ·
      refine ⟨47392140699715624100280965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31594760466477082733520643 47392140699715624100280965)
      ·
        refine ⟨8886026381196679518802681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47392140699715624100280965 8886026381196679518802681)
        ·
          refine ⟨6664519785897509639102011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8886026381196679518802681 6664519785897509639102011)
          ·
            refine ⟨9996779678846264458653017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6664519785897509639102011 9996779678846264458653017)
            ·
              refine ⟨7497584759134698343989763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9996779678846264458653017 7497584759134698343989763)
              ·
                refine ⟨11246377138702047515984645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7497584759134698343989763 11246377138702047515984645)
                ·
                  refine ⟨2108695713506633909247121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11246377138702047515984645 2108695713506633909247121)
                  ·
                    refine ⟨1581521785129975431935341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2108695713506633909247121 1581521785129975431935341)
                    ·
                      refine ⟨593070669423740786975753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581521785129975431935341 593070669423740786975753)
                      ·
                        rfl

theorem cell23_1155001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1155001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155001 prefixEnd_1155001 := by exact prefixLift 1155001
  have htrace : WordTrace (prefixWord ++ tailWord_1155001) baseStart_1155001 baseEnd_1155001 := by
    simpa [prefixWord, tailWord_1155001, baseEnd_1155001] using wordTrace_append hprefix tailTrace_1155001
  have hstable : (prefixWord ++ tailWord_1155001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155001).length < 2 ^ (prefixWord ++ tailWord_1155001).sum := by decide
  have hdescent : baseEnd_1155001 < baseStart_1155001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155008 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 1, 4]
def baseStart_1155008 : Nat := 118140960795 + 1155008 * 2 ^ 59
def prefixEnd_1155008 : Nat := 4983230072969 + 3 ^ 40 * 1155008 * 2
def baseEnd_1155008 : Nat := 197691421262774086529407

theorem tailTrace_1155008 : CollatzResearch.WordTrace tailWord_1155008 prefixEnd_1155008 197691421262774086529407 := by
  unfold tailWord_1155008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063301299805375253432839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28084401733073833671243785 21063301299805375253432839)
  ·
    refine ⟨31594951949708062880149259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21063301299805375253432839 31594951949708062880149259)
    ·
      refine ⟨47392427924562094320223889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31594951949708062880149259 47392427924562094320223889)
      ·
        refine ⟨35544320943421570740167917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47392427924562094320223889 35544320943421570740167917)
        ·
          refine ⟨13329120353783089027562969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35544320943421570740167917 13329120353783089027562969)
          ·
            refine ⟨9996840265337316770672227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13329120353783089027562969 9996840265337316770672227)
            ·
              refine ⟨14995260398005975156008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9996840265337316770672227 14995260398005975156008341)
              ·
                refine ⟨702902831156530085437891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14995260398005975156008341 702902831156530085437891)
                ·
                  refine ⟨1054354246734795128156837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702902831156530085437891 1054354246734795128156837)
                  ·
                    refine ⟨197691421262774086529407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1054354246734795128156837 197691421262774086529407)
                    ·
                      rfl

theorem cell23_1155008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_1155008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155008 prefixEnd_1155008 := by exact prefixLift 1155008
  have htrace : WordTrace (prefixWord ++ tailWord_1155008) baseStart_1155008 baseEnd_1155008 := by
    simpa [prefixWord, tailWord_1155008, baseEnd_1155008] using wordTrace_append hprefix tailTrace_1155008
  have hstable : (prefixWord ++ tailWord_1155008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155008).length < 2 ^ (prefixWord ++ tailWord_1155008).sum := by decide
  have hdescent : baseEnd_1155008 < baseStart_1155008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155065 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_1155065 : Nat := 118140960795 + 1155065 * 2 ^ 59
def prefixEnd_1155065 : Nat := 4983230072969 + 3 ^ 40 * 1155065 * 2
def baseEnd_1155065 : Nat := 593103532185628536575459

theorem tailTrace_1155065 : CollatzResearch.WordTrace tailWord_1155065 prefixEnd_1155065 593103532185628536575459 := by
  unfold tailWord_1155065
  simp only [CollatzResearch.WordTrace]
  refine ⟨42128681560404249241690649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28085787706936166161127099 42128681560404249241690649)
  ·
    refine ⟨31596511170303186931267987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42128681560404249241690649 31596511170303186931267987)
    ·
      refine ⟨47394766755454780396901981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31596511170303186931267987 47394766755454780396901981)
      ·
        refine ⟨17773037533295542648838243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47394766755454780396901981 17773037533295542648838243)
        ·
          refine ⟨26659556299943313973257365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17773037533295542648838243 26659556299943313973257365)
          ·
            refine ⟨1249666701559842842496439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26659556299943313973257365 1249666701559842842496439)
            ·
              refine ⟨1874500052339764263744659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249666701559842842496439 1874500052339764263744659)
              ·
                refine ⟨2811750078509646395616989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874500052339764263744659 2811750078509646395616989)
                ·
                  refine ⟨1054406279441117398356371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2811750078509646395616989 1054406279441117398356371)
                  ·
                    refine ⟨1581609419161676097534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054406279441117398356371 1581609419161676097534557)
                    ·
                      refine ⟨593103532185628536575459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581609419161676097534557 593103532185628536575459)
                      ·
                        rfl

theorem cell23_1155065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_1155065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155065 prefixEnd_1155065 := by exact prefixLift 1155065
  have htrace : WordTrace (prefixWord ++ tailWord_1155065) baseStart_1155065 baseEnd_1155065 := by
    simpa [prefixWord, tailWord_1155065, baseEnd_1155065] using wordTrace_append hprefix tailTrace_1155065
  have hstable : (prefixWord ++ tailWord_1155065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155065).length < 2 ^ (prefixWord ++ tailWord_1155065).sum := by decide
  have hdescent : baseEnd_1155065 < baseStart_1155065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155111 : List Nat := [1, 1, 7, 1, 13]
def baseStart_1155111 : Nat := 118140960795 + 1155111 * 2 ^ 59
def prefixEnd_1155111 : Nat := 4983230072969 + 3 ^ 40 * 1155111 * 2
def baseEnd_1155111 : Nat := 813617492861091024143

theorem tailTrace_1155111 : CollatzResearch.WordTrace tailWord_1155111 prefixEnd_1155111 813617492861091024143 := by
  unfold tailWord_1155111
  simp only [CollatzResearch.WordTrace]
  refine ⟨42130359318237599097865187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28086906212158399398576791 42130359318237599097865187)
  ·
    refine ⟨63195538977356398646797781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42130359318237599097865187 63195538977356398646797781)
    ·
      refine ⟨1481145444781790593284323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63195538977356398646797781 1481145444781790593284323)
      ·
        refine ⟨2221718167172685889926485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481145444781790593284323 2221718167172685889926485)
        ·
          refine ⟨813617492861091024143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2221718167172685889926485 813617492861091024143)
          ·
            rfl

theorem cell23_1155111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 13].length) (baseStart_1155111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155111 prefixEnd_1155111 := by exact prefixLift 1155111
  have htrace : WordTrace (prefixWord ++ tailWord_1155111) baseStart_1155111 baseEnd_1155111 := by
    simpa [prefixWord, tailWord_1155111, baseEnd_1155111] using wordTrace_append hprefix tailTrace_1155111
  have hstable : (prefixWord ++ tailWord_1155111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155111).length < 2 ^ (prefixWord ++ tailWord_1155111).sum := by decide
  have hdescent : baseEnd_1155111 < baseStart_1155111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155128 : List Nat := [2, 1, 2, 1, 6, 2, 1, 8]
def baseStart_1155128 : Nat := 118140960795 + 1155128 * 2 ^ 59
def prefixEnd_1155128 : Nat := 4983230072969 + 3 ^ 40 * 1155128 * 2
def baseEnd_1155128 : Nat := 21967995609883770003247

theorem tailTrace_1155128 : CollatzResearch.WordTrace tailWord_1155128 prefixEnd_1155128 21967995609883770003247 := by
  unfold tailWord_1155128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065489679588005500617019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28087319572784007334156025 21065489679588005500617019)
  ·
    refine ⟨31598234519382008250925529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21065489679588005500617019 31598234519382008250925529)
    ·
      refine ⟨23698675889536506188194147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31598234519382008250925529 23698675889536506188194147)
      ·
        refine ⟨35548013834304759282291221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23698675889536506188194147 35548013834304759282291221)
        ·
          refine ⟨1666313148483035591357401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35548013834304759282291221 1666313148483035591357401)
          ·
            refine ⟨1249734861362276693518051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666313148483035591357401 1249734861362276693518051)
            ·
              refine ⟨1874602292043415040277077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249734861362276693518051 1874602292043415040277077)
              ·
                refine ⟨21967995609883770003247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1874602292043415040277077 21967995609883770003247)
                ·
                  rfl

theorem cell23_1155128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 8].length) (baseStart_1155128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155128 prefixEnd_1155128 := by exact prefixLift 1155128
  have htrace : WordTrace (prefixWord ++ tailWord_1155128) baseStart_1155128 baseEnd_1155128 := by
    simpa [prefixWord, tailWord_1155128, baseEnd_1155128] using wordTrace_append hprefix tailTrace_1155128
  have hstable : (prefixWord ++ tailWord_1155128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155128).length < 2 ^ (prefixWord ++ tailWord_1155128).sum := by decide
  have hdescent : baseEnd_1155128 < baseStart_1155128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155142 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1155142 : Nat := 118140960795 + 1155142 * 2 ^ 59
def prefixEnd_1155142 : Nat := 4983230072969 + 3 ^ 40 * 1155142 * 2
def baseEnd_1155142 : Nat := 593143070196024735312605

theorem tailTrace_1155142 : CollatzResearch.WordTrace tailWord_1155142 prefixEnd_1155142 593143070196024735312605 := by
  unfold tailWord_1155142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316609061910165356007615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28087659987416860928162453 1316609061910165356007615)
  ·
    refine ⟨1974913592865248034011423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1316609061910165356007615 1974913592865248034011423)
    ·
      refine ⟨2962370389297872051017135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974913592865248034011423 2962370389297872051017135)
      ·
        refine ⟨4443555583946808076525703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962370389297872051017135 4443555583946808076525703)
        ·
          refine ⟨6665333375920212114788555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443555583946808076525703 6665333375920212114788555)
          ·
            refine ⟨9998000063880318172182833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6665333375920212114788555 9998000063880318172182833)
            ·
              refine ⟨7498500047910238629137125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9998000063880318172182833 7498500047910238629137125)
              ·
                refine ⟨1405968758983169742963211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7498500047910238629137125 1405968758983169742963211)
                ·
                  refine ⟨2108953138474754614444817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405968758983169742963211 2108953138474754614444817)
                  ·
                    refine ⟨1581714853856065960833613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2108953138474754614444817 1581714853856065960833613)
                    ·
                      refine ⟨593143070196024735312605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581714853856065960833613 593143070196024735312605)
                      ·
                        rfl

theorem cell23_1155142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1155142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155142 prefixEnd_1155142 := by exact prefixLift 1155142
  have htrace : WordTrace (prefixWord ++ tailWord_1155142) baseStart_1155142 baseEnd_1155142 := by
    simpa [prefixWord, tailWord_1155142, baseEnd_1155142] using wordTrace_append hprefix tailTrace_1155142
  have hstable : (prefixWord ++ tailWord_1155142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155142).length < 2 ^ (prefixWord ++ tailWord_1155142).sum := by decide
  have hdescent : baseEnd_1155142 < baseStart_1155142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155166 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1155166 : Nat := 118140960795 + 1155166 * 2 ^ 59
def prefixEnd_1155166 : Nat := 4983230072969 + 3 ^ 40 * 1155166 * 2
def baseEnd_1155166 : Nat := 197718464577244213804165

theorem tailTrace_1155166 : CollatzResearch.WordTrace tailWord_1155166 prefixEnd_1155166 197718464577244213804165 := by
  unfold tailWord_1155166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266545666629792936389669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28088243555358895660744901 5266545666629792936389669)
  ·
    refine ⟨987477312493086175573063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5266545666629792936389669 987477312493086175573063)
    ·
      refine ⟨1481215968739629263359595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 987477312493086175573063 1481215968739629263359595)
      ·
        refine ⟨2221823953109443895039393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481215968739629263359595 2221823953109443895039393)
        ·
          refine ⟨1666367964832082921279545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221823953109443895039393 1666367964832082921279545)
          ·
            refine ⟨1249775973624062190959659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666367964832082921279545 1249775973624062190959659)
            ·
              refine ⟨1874663960436093286439489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249775973624062190959659 1874663960436093286439489)
              ·
                refine ⟨1405997970327069964829617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874663960436093286439489 1405997970327069964829617)
                ·
                  refine ⟨1054498477745302473622213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405997970327069964829617 1054498477745302473622213)
                  ·
                    refine ⟨197718464577244213804165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1054498477745302473622213 197718464577244213804165)
                    ·
                      rfl

theorem cell23_1155166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1155166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155166 prefixEnd_1155166 := by exact prefixLift 1155166
  have htrace : WordTrace (prefixWord ++ tailWord_1155166) baseStart_1155166 baseEnd_1155166 := by
    simpa [prefixWord, tailWord_1155166, baseEnd_1155166] using wordTrace_append hprefix tailTrace_1155166
  have hstable : (prefixWord ++ tailWord_1155166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155166).length < 2 ^ (prefixWord ++ tailWord_1155166).sum := by decide
  have hdescent : baseEnd_1155166 < baseStart_1155166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155171 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 6]
def baseStart_1155171 : Nat := 118140960795 + 1155171 * 2 ^ 59
def prefixEnd_1155171 : Nat := 4983230072969 + 3 ^ 40 * 1155171 * 2
def baseEnd_1155171 : Nat := 197719320378335040616657

theorem tailTrace_1155171 : CollatzResearch.WordTrace tailWord_1155171 prefixEnd_1155171 197719320378335040616657 := by
  unfold tailWord_1155171
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132547698020229345049367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28088365132013486230032911 42132547698020229345049367)
  ·
    refine ⟨63198821547030344017574051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42132547698020229345049367 63198821547030344017574051)
    ·
      refine ⟨94798232320545516026361077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63198821547030344017574051 94798232320545516026361077)
      ·
        refine ⟨8887334280051142127471351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94798232320545516026361077 8887334280051142127471351)
        ·
          refine ⟨13331001420076713191207027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887334280051142127471351 13331001420076713191207027)
          ·
            refine ⟨19996502130115069786810541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331001420076713191207027 19996502130115069786810541)
            ·
              refine ⟨7498688298793151170053953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19996502130115069786810541 7498688298793151170053953)
              ·
                refine ⟨5624016224094863377540465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7498688298793151170053953 5624016224094863377540465)
                ·
                  refine ⟨4218012168071147533155349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624016224094863377540465 4218012168071147533155349)
                  ·
                    refine ⟨197719320378335040616657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4218012168071147533155349 197719320378335040616657)
                    ·
                      rfl

theorem cell23_1155171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_1155171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155171 prefixEnd_1155171 := by exact prefixLift 1155171
  have htrace : WordTrace (prefixWord ++ tailWord_1155171) baseStart_1155171 baseEnd_1155171 := by
    simpa [prefixWord, tailWord_1155171, baseEnd_1155171] using wordTrace_append hprefix tailTrace_1155171
  have hstable : (prefixWord ++ tailWord_1155171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155171).length < 2 ^ (prefixWord ++ tailWord_1155171).sum := by decide
  have hdescent : baseEnd_1155171 < baseStart_1155171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155271 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1155271 : Nat := 118140960795 + 1155271 * 2 ^ 59
def prefixEnd_1155271 : Nat := 4983230072969 + 3 ^ 40 * 1155271 * 2
def baseEnd_1155271 : Nat := 593209309200454730599511

theorem tailTrace_1155271 : CollatzResearch.WordTrace tailWord_1155271 prefixEnd_1155271 593209309200454730599511 := by
  unfold tailWord_1155271
  simp only [CollatzResearch.WordTrace]
  refine ⟨42136194997657946423689667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28090796665105297615793111 42136194997657946423689667)
  ·
    refine ⟨63204292496486919635534501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42136194997657946423689667 63204292496486919635534501)
    ·
      refine ⟨11850804843091297431662719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63204292496486919635534501 11850804843091297431662719)
      ·
        refine ⟨17776207264636946147494079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11850804843091297431662719 17776207264636946147494079)
        ·
          refine ⟨26664310896955419221241119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17776207264636946147494079 26664310896955419221241119)
          ·
            refine ⟨39996466345433128831861679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26664310896955419221241119 39996466345433128831861679)
            ·
              refine ⟨59994699518149693247792519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39996466345433128831861679 59994699518149693247792519)
              ·
                refine ⟨89992049277224539871688779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59994699518149693247792519 89992049277224539871688779)
                ·
                  refine ⟨134988073915836809807533169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89992049277224539871688779 134988073915836809807533169)
                  ·
                    refine ⟨101241055436877607355649877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134988073915836809807533169 101241055436877607355649877)
                    ·
                      refine ⟨593209309200454730599511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 101241055436877607355649877 593209309200454730599511)
                      ·
                        rfl

theorem cell23_1155271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1155271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155271 prefixEnd_1155271 := by exact prefixLift 1155271
  have htrace : WordTrace (prefixWord ++ tailWord_1155271) baseStart_1155271 baseEnd_1155271 := by
    simpa [prefixWord, tailWord_1155271, baseEnd_1155271] using wordTrace_append hprefix tailTrace_1155271
  have hstable : (prefixWord ++ tailWord_1155271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155271).length < 2 ^ (prefixWord ++ tailWord_1155271).sum := by decide
  have hdescent : baseEnd_1155271 < baseStart_1155271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155286 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1155286 : Nat := 118140960795 + 1155286 * 2 ^ 59
def prefixEnd_1155286 : Nat := 4983230072969 + 3 ^ 40 * 1155286 * 2
def baseEnd_1155286 : Nat := 65913001267808019101327

theorem tailTrace_1155286 : CollatzResearch.WordTrace tailWord_1155286 prefixEnd_1155286 65913001267808019101327 := by
  unfold tailWord_1155286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633546380787725249092857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28091161395069069323657141 2633546380787725249092857)
  ·
    refine ⟨1975159785590793936819643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2633546380787725249092857 1975159785590793936819643)
    ·
      refine ⟨2962739678386190905229465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975159785590793936819643 2962739678386190905229465)
      ·
        refine ⟨2222054758789643178922099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962739678386190905229465 2222054758789643178922099)
        ·
          refine ⟨3333082138184464768383149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222054758789643178922099 3333082138184464768383149)
          ·
            refine ⟨1249905801819174288143681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3333082138184464768383149 1249905801819174288143681)
            ·
              refine ⟨937429351364380716107761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249905801819174288143681 937429351364380716107761)
              ·
                refine ⟨703072013523285537080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937429351364380716107761 703072013523285537080821)
                ·
                  refine ⟨65913001267808019101327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703072013523285537080821 65913001267808019101327)
                  ·
                    rfl

theorem cell23_1155286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1155286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155286 prefixEnd_1155286 := by exact prefixLift 1155286
  have htrace : WordTrace (prefixWord ++ tailWord_1155286) baseStart_1155286 baseEnd_1155286 := by
    simpa [prefixWord, tailWord_1155286, baseEnd_1155286] using wordTrace_append hprefix tailTrace_1155286
  have hstable : (prefixWord ++ tailWord_1155286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155286).length < 2 ^ (prefixWord ++ tailWord_1155286).sum := by decide
  have hdescent : baseEnd_1155286 < baseStart_1155286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155308 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 6]
def baseStart_1155308 : Nat := 118140960795 + 1155308 * 2 ^ 59
def prefixEnd_1155308 : Nat := 4983230072969 + 3 ^ 40 * 1155308 * 2
def baseEnd_1155308 : Nat := 65914256442741231759649

theorem tailTrace_1155308 : CollatzResearch.WordTrace tailWord_1155308 prefixEnd_1155308 65914256442741231759649 := by
  unfold tailWord_1155308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21068772249261950871393289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28091696332349267828524385 21068772249261950871393289)
  ·
    refine ⟨15801579186946463153544967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21068772249261950871393289 15801579186946463153544967)
    ·
      refine ⟨23702368780419694730317451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15801579186946463153544967 23702368780419694730317451)
      ·
        refine ⟨35553553170629542095476177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23702368780419694730317451 35553553170629542095476177)
        ·
          refine ⟨26665164877972156571607133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35553553170629542095476177 26665164877972156571607133)
          ·
            refine ⟨9999436829239558714352675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26665164877972156571607133 9999436829239558714352675)
            ·
              refine ⟨14999155243859338071529013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9999436829239558714352675 14999155243859338071529013)
              ·
                refine ⟨1406170804111812944205845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14999155243859338071529013 1406170804111812944205845)
                ·
                  refine ⟨65914256442741231759649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1406170804111812944205845 65914256442741231759649)
                  ·
                    rfl

theorem cell23_1155308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_1155308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155308 prefixEnd_1155308 := by exact prefixLift 1155308
  have htrace : WordTrace (prefixWord ++ tailWord_1155308) baseStart_1155308 baseEnd_1155308 := by
    simpa [prefixWord, tailWord_1155308, baseEnd_1155308] using wordTrace_append hprefix tailTrace_1155308
  have hstable : (prefixWord ++ tailWord_1155308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155308).length < 2 ^ (prefixWord ++ tailWord_1155308).sum := by decide
  have hdescent : baseEnd_1155308 < baseStart_1155308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155322 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_1155322 : Nat := 118140960795 + 1155322 * 2 ^ 59
def prefixEnd_1155322 : Nat := 4983230072969 + 3 ^ 40 * 1155322 * 2
def baseEnd_1155322 : Nat := 593235496713834031061777

theorem tailTrace_1155322 : CollatzResearch.WordTrace tailWord_1155322 prefixEnd_1155322 593235496713834031061777 := by
  unfold tailWord_1155322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534513780118295533449055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28092036746982121422530813 10534513780118295533449055)
  ·
    refine ⟨15801770670177443300173583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10534513780118295533449055 15801770670177443300173583)
    ·
      refine ⟨23702656005266164950260375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15801770670177443300173583 23702656005266164950260375)
      ·
        refine ⟨35553984007899247425390563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23702656005266164950260375 35553984007899247425390563)
        ·
          refine ⟨53330976011848871138085845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35553984007899247425390563 53330976011848871138085845)
          ·
            refine ⟨1249944750277707917298887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53330976011848871138085845 1249944750277707917298887)
            ·
              refine ⟨1874917125416561875948331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249944750277707917298887 1874917125416561875948331)
              ·
                refine ⟨2812375688124842813922497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874917125416561875948331 2812375688124842813922497)
                ·
                  refine ⟨2109281766093632110441873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812375688124842813922497 2109281766093632110441873)
                  ·
                    refine ⟨1581961324570224082831405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109281766093632110441873 1581961324570224082831405)
                    ·
                      refine ⟨593235496713834031061777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581961324570224082831405 593235496713834031061777)
                      ·
                        rfl

theorem cell23_1155322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_1155322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155322 prefixEnd_1155322 := by exact prefixLift 1155322
  have htrace : WordTrace (prefixWord ++ tailWord_1155322) baseStart_1155322 baseEnd_1155322 := by
    simpa [prefixWord, tailWord_1155322, baseEnd_1155322] using wordTrace_append hprefix tailTrace_1155322
  have hstable : (prefixWord ++ tailWord_1155322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155322).length < 2 ^ (prefixWord ++ tailWord_1155322).sum := by decide
  have hdescent : baseEnd_1155322 < baseStart_1155322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155352 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1155352 : Nat := 118140960795 + 1155352 * 2 ^ 59
def prefixEnd_1155352 : Nat := 4983230072969 + 3 ^ 40 * 1155352 * 2
def baseEnd_1155352 : Nat := 593250901133468913686639

theorem tailTrace_1155352 : CollatzResearch.WordTrace tailWord_1155352 prefixEnd_1155352 593250901133468913686639 := by
  unfold tailWord_1155352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21069574655182248628694155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28092766206909664838258873 21069574655182248628694155)
  ·
    refine ⟨31604361982773372943041233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21069574655182248628694155 31604361982773372943041233)
    ·
      refine ⟨23703271487080029707280925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31604361982773372943041233 23703271487080029707280925)
      ·
        refine ⟨8888726807655011140230347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23703271487080029707280925 8888726807655011140230347)
        ·
          refine ⟨13333090211482516710345521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8888726807655011140230347 13333090211482516710345521)
          ·
            refine ⟨9999817658611887532759141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13333090211482516710345521 9999817658611887532759141)
            ·
              refine ⟨1874965810989728912392339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9999817658611887532759141 1874965810989728912392339)
              ·
                refine ⟨2812448716484593368588509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874965810989728912392339 2812448716484593368588509)
                ·
                  refine ⟨1054668268681722513220691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2812448716484593368588509 1054668268681722513220691)
                  ·
                    refine ⟨1582002403022583769831037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054668268681722513220691 1582002403022583769831037)
                    ·
                      refine ⟨593250901133468913686639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582002403022583769831037 593250901133468913686639)
                      ·
                        rfl

theorem cell23_1155352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1155352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155352 prefixEnd_1155352 := by exact prefixLift 1155352
  have htrace : WordTrace (prefixWord ++ tailWord_1155352) baseStart_1155352 baseEnd_1155352 := by
    simpa [prefixWord, tailWord_1155352, baseEnd_1155352] using wordTrace_append hprefix tailTrace_1155352
  have hstable : (prefixWord ++ tailWord_1155352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155352).length < 2 ^ (prefixWord ++ tailWord_1155352).sum := by decide
  have hdescent : baseEnd_1155352 < baseStart_1155352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155362 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_1155362 : Nat := 118140960795 + 1155362 * 2 ^ 59
def prefixEnd_1155362 : Nat := 4983230072969 + 3 ^ 40 * 1155362 * 2
def baseEnd_1155362 : Nat := 593256035940013874561593

theorem tailTrace_1155362 : CollatzResearch.WordTrace tailWord_1155362 prefixEnd_1155362 593256035940013874561593 := by
  unfold tailWord_1155362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534878510082067241313085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28093009360218845976834893 10534878510082067241313085)
  ·
    refine ⟨3950579441280775215492407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10534878510082067241313085 3950579441280775215492407)
    ·
      refine ⟨5925869161921162823238611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950579441280775215492407 5925869161921162823238611)
      ·
        refine ⟨8888803742881744234857917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5925869161921162823238611 8888803742881744234857917)
        ·
          refine ⟨3333301403580654088071719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8888803742881744234857917 3333301403580654088071719)
          ·
            refine ⟨4999952105370981132107579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333301403580654088071719 4999952105370981132107579)
            ·
              refine ⟨7499928158056471698161369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999952105370981132107579 7499928158056471698161369)
              ·
                refine ⟨5624946118542353773621027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499928158056471698161369 5624946118542353773621027)
                ·
                  refine ⟨8437419177813530660431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624946118542353773621027 8437419177813530660431541)
                  ·
                    refine ⟨791008047920018499415457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8437419177813530660431541 791008047920018499415457)
                    ·
                      refine ⟨593256035940013874561593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791008047920018499415457 593256035940013874561593)
                      ·
                        rfl

theorem cell23_1155362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_1155362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155362 prefixEnd_1155362 := by exact prefixLift 1155362
  have htrace : WordTrace (prefixWord ++ tailWord_1155362) baseStart_1155362 baseEnd_1155362 := by
    simpa [prefixWord, tailWord_1155362, baseEnd_1155362] using wordTrace_append hprefix tailTrace_1155362
  have hstable : (prefixWord ++ tailWord_1155362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155362).length < 2 ^ (prefixWord ++ tailWord_1155362).sum := by decide
  have hdescent : baseEnd_1155362 < baseStart_1155362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155375 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_1155375 : Nat := 118140960795 + 1155375 * 2 ^ 59
def prefixEnd_1155375 : Nat := 4983230072969 + 3 ^ 40 * 1155375 * 2
def baseEnd_1155375 : Nat := 593262711188522323699033

theorem tailTrace_1155375 : CollatzResearch.WordTrace tailWord_1155375 prefixEnd_1155375 593262711188522323699033 := by
  unfold tailWord_1155375
  simp only [CollatzResearch.WordTrace]
  refine ⟨42139988189281172185475579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28093325459520781456983719 42139988189281172185475579)
  ·
    refine ⟨63209982283921758278213369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42139988189281172185475579 63209982283921758278213369)
    ·
      refine ⟨47407486712941318708660027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63209982283921758278213369 47407486712941318708660027)
      ·
        refine ⟨71111230069411978062990041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47407486712941318708660027 71111230069411978062990041)
        ·
          refine ⟨53333422552058983547242531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71111230069411978062990041 53333422552058983547242531)
          ·
            refine ⟨80000133828088475320863797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53333422552058983547242531 80000133828088475320863797)
            ·
              refine ⟨7500012546383294561330981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80000133828088475320863797 7500012546383294561330981)
              ·
                refine ⟨1406252352446867730249559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7500012546383294561330981 1406252352446867730249559)
                ·
                  refine ⟨2109378528670301595374339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406252352446867730249559 2109378528670301595374339)
                  ·
                    refine ⟨3164067793005452393061509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109378528670301595374339 3164067793005452393061509)
                    ·
                      refine ⟨593262711188522323699033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3164067793005452393061509 593262711188522323699033)
                      ·
                        rfl

theorem cell23_1155375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_1155375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155375 prefixEnd_1155375 := by exact prefixLift 1155375
  have htrace : WordTrace (prefixWord ++ tailWord_1155375) baseStart_1155375 baseEnd_1155375 := by
    simpa [prefixWord, tailWord_1155375, baseEnd_1155375] using wordTrace_append hprefix tailTrace_1155375
  have hstable : (prefixWord ++ tailWord_1155375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155375).length < 2 ^ (prefixWord ++ tailWord_1155375).sum := by decide
  have hdescent : baseEnd_1155375 < baseStart_1155375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155386 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_1155386 : Nat := 118140960795 + 1155386 * 2 ^ 59
def prefixEnd_1155386 : Nat := 4983230072969 + 3 ^ 40 * 1155386 * 2
def baseEnd_1155386 : Nat := 593268359475721780661483

theorem tailTrace_1155386 : CollatzResearch.WordTrace tailWord_1155386 prefixEnd_1155386 593268359475721780661483 := by
  unfold tailWord_1155386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535097348060330266031503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28093592928160880709417341 10535097348060330266031503)
  ·
    refine ⟨15802646022090495399047255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535097348060330266031503 15802646022090495399047255)
    ·
      refine ⟨23703969033135743098570883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15802646022090495399047255 23703969033135743098570883)
      ·
        refine ⟨35555953549703614647856325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23703969033135743098570883 35555953549703614647856325)
        ·
          refine ⟨6666741290569427746473061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35555953549703614647856325 6666741290569427746473061)
          ·
            refine ⟨1250013991981767702463699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6666741290569427746473061 1250013991981767702463699)
            ·
              refine ⟨1875020987972651553695549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250013991981767702463699 1875020987972651553695549)
              ·
                refine ⟨703132870489744332635831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1875020987972651553695549 703132870489744332635831)
                ·
                  refine ⟨1054699305734616498953747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703132870489744332635831 1054699305734616498953747)
                  ·
                    refine ⟨1582048958601924748430621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054699305734616498953747 1582048958601924748430621)
                    ·
                      refine ⟨593268359475721780661483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582048958601924748430621 593268359475721780661483)
                      ·
                        rfl

theorem cell23_1155386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_1155386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155386 prefixEnd_1155386 := by exact prefixLift 1155386
  have htrace : WordTrace (prefixWord ++ tailWord_1155386) baseStart_1155386 baseEnd_1155386 := by
    simpa [prefixWord, tailWord_1155386, baseEnd_1155386] using wordTrace_append hprefix tailTrace_1155386
  have hstable : (prefixWord ++ tailWord_1155386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155386).length < 2 ^ (prefixWord ++ tailWord_1155386).sum := by decide
  have hdescent : baseEnd_1155386 < baseStart_1155386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155396 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1155396 : Nat := 118140960795 + 1155396 * 2 ^ 59
def prefixEnd_1155396 : Nat := 4983230072969 + 3 ^ 40 * 1155396 * 2
def baseEnd_1155396 : Nat := 593273494282266741536437

theorem tailTrace_1155396 : CollatzResearch.WordTrace tailWord_1155396 prefixEnd_1155396 593273494282266741536437 := by
  unfold tailWord_1155396
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070377061102546385995021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28093836081470061847993361 21070377061102546385995021)
  ·
    refine ⟨7901391397913454894748133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21070377061102546385995021 7901391397913454894748133)
    ·
      refine ⟨1481510887108772792765275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7901391397913454894748133 1481510887108772792765275)
      ·
        refine ⟨2222266330663159189147913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481510887108772792765275 2222266330663159189147913)
        ·
          refine ⟨1666699747997369391860935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2222266330663159189147913 1666699747997369391860935)
          ·
            refine ⟨2500049621996054087791403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666699747997369391860935 2500049621996054087791403)
            ·
              refine ⟨3750074432994081131687105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500049621996054087791403 3750074432994081131687105)
              ·
                refine ⟨2812555824745560848765329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750074432994081131687105 2812555824745560848765329)
                ·
                  refine ⟨2109416868559170636573997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812555824745560848765329 2109416868559170636573997)
                  ·
                    refine ⟨791031325709688988715249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109416868559170636573997 791031325709688988715249)
                    ·
                      refine ⟨593273494282266741536437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791031325709688988715249 593273494282266741536437)
                      ·
                        rfl

theorem cell23_1155396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1155396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155396 prefixEnd_1155396 := by exact prefixLift 1155396
  have htrace : WordTrace (prefixWord ++ tailWord_1155396) baseStart_1155396 baseEnd_1155396 := by
    simpa [prefixWord, tailWord_1155396, baseEnd_1155396] using wordTrace_append hprefix tailTrace_1155396
  have hstable : (prefixWord ++ tailWord_1155396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155396).length < 2 ^ (prefixWord ++ tailWord_1155396).sum := by decide
  have hdescent : baseEnd_1155396 < baseStart_1155396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155409 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_1155409 : Nat := 118140960795 + 1155409 * 2 ^ 59
def prefixEnd_1155409 : Nat := 4983230072969 + 3 ^ 40 * 1155409 * 2
def baseEnd_1155409 : Nat := 593280169530775190673877

theorem tailTrace_1155409 : CollatzResearch.WordTrace tailWord_1155409 prefixEnd_1155409 593280169530775190673877 := by
  unfold tailWord_1155409
  simp only [CollatzResearch.WordTrace]
  refine ⟨42141228271157995992213281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28094152180771997328142187 42141228271157995992213281)
  ·
    refine ⟨31605921203368496994159961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42141228271157995992213281 31605921203368496994159961)
    ·
      refine ⟨23704440902526372745619971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31605921203368496994159961 23704440902526372745619971)
      ·
        refine ⟨35556661353789559118429957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23704440902526372745619971 35556661353789559118429957)
        ·
          refine ⟨6666874003835542334705617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35556661353789559118429957 6666874003835542334705617)
          ·
            refine ⟨5000155502876656751029213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6666874003835542334705617 5000155502876656751029213)
            ·
              refine ⟨1875058313578746281635955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5000155502876656751029213 1875058313578746281635955)
              ·
                refine ⟨2812587470368119422453933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875058313578746281635955 2812587470368119422453933)
                ·
                  refine ⟨1054720301388044783420225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2812587470368119422453933 1054720301388044783420225)
                  ·
                    refine ⟨791040226041033587565169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054720301388044783420225 791040226041033587565169)
                    ·
                      refine ⟨593280169530775190673877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791040226041033587565169 593280169530775190673877)
                      ·
                        rfl

theorem cell23_1155409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_1155409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155409 prefixEnd_1155409 := by exact prefixLift 1155409
  have htrace : WordTrace (prefixWord ++ tailWord_1155409) baseStart_1155409 baseEnd_1155409 := by
    simpa [prefixWord, tailWord_1155409, baseEnd_1155409] using wordTrace_append hprefix tailTrace_1155409
  have hstable : (prefixWord ++ tailWord_1155409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155409).length < 2 ^ (prefixWord ++ tailWord_1155409).sum := by decide
  have hdescent : baseEnd_1155409 < baseStart_1155409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155418 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1155418 : Nat := 118140960795 + 1155418 * 2 ^ 59
def prefixEnd_1155418 : Nat := 4983230072969 + 3 ^ 40 * 1155418 * 2
def baseEnd_1155418 : Nat := 593284790856665655461335

theorem tailTrace_1155418 : CollatzResearch.WordTrace tailWord_1155418 prefixEnd_1155418 593284790856665655461335 := by
  unfold tailWord_1155418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535389132031347632322727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28094371018750260352860605 10535389132031347632322727)
  ·
    refine ⟨15803083698047021448484091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535389132031347632322727 15803083698047021448484091)
    ·
      refine ⟨23704625547070532172726137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15803083698047021448484091 23704625547070532172726137)
      ·
        refine ⟨17778469160302899129544603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23704625547070532172726137 17778469160302899129544603)
        ·
          refine ⟨26667703740454348694316905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17778469160302899129544603 26667703740454348694316905)
          ·
            refine ⟨20000777805340761520737679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26667703740454348694316905 20000777805340761520737679)
            ·
              refine ⟨30001166708011142281106519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20000777805340761520737679 30001166708011142281106519)
              ·
                refine ⟨45001750062016713421659779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30001166708011142281106519 45001750062016713421659779)
                ·
                  refine ⟨67502625093025070132489669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45001750062016713421659779 67502625093025070132489669)
                  ·
                    refine ⟨12656742204942200649841813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67502625093025070132489669 12656742204942200649841813)
                    ·
                      refine ⟨593284790856665655461335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12656742204942200649841813 593284790856665655461335)
                      ·
                        rfl

theorem cell23_1155418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1155418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155418 prefixEnd_1155418 := by exact prefixLift 1155418
  have htrace : WordTrace (prefixWord ++ tailWord_1155418) baseStart_1155418 baseEnd_1155418 := by
    simpa [prefixWord, tailWord_1155418, baseEnd_1155418] using wordTrace_append hprefix tailTrace_1155418
  have hstable : (prefixWord ++ tailWord_1155418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155418).length < 2 ^ (prefixWord ++ tailWord_1155418).sum := by decide
  have hdescent : baseEnd_1155418 < baseStart_1155418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155429 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1155429 : Nat := 118140960795 + 1155429 * 2 ^ 59
def prefixEnd_1155429 : Nat := 4983230072969 + 3 ^ 40 * 1155429 * 2
def baseEnd_1155429 : Nat := 593290439143865112423785

theorem tailTrace_1155429 : CollatzResearch.WordTrace tailWord_1155429 prefixEnd_1155429 593290439143865112423785 := by
  unfold tailWord_1155429
  simp only [CollatzResearch.WordTrace]
  refine ⟨42141957731085539407941341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28094638487390359605294227 42141957731085539407941341)
  ·
    refine ⟨15803234149157077277978003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42141957731085539407941341 15803234149157077277978003)
    ·
      refine ⟨23704851223735615916967005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15803234149157077277978003 23704851223735615916967005)
      ·
        refine ⟨8889319208900855968862627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23704851223735615916967005 8889319208900855968862627)
        ·
          refine ⟨13333978813351283953293941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889319208900855968862627 13333978813351283953293941)
          ·
            refine ⟨1250060513751682870621307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13333978813351283953293941 1250060513751682870621307)
            ·
              refine ⟨1875090770627524305931961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250060513751682870621307 1875090770627524305931961)
              ·
                refine ⟨1406318077970643229448971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875090770627524305931961 1406318077970643229448971)
                ·
                  refine ⟨2109477116955964844173457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406318077970643229448971 2109477116955964844173457)
                  ·
                    refine ⟨1582107837716973633130093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109477116955964844173457 1582107837716973633130093)
                    ·
                      refine ⟨593290439143865112423785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582107837716973633130093 593290439143865112423785)
                      ·
                        rfl

theorem cell23_1155429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1155429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155429 prefixEnd_1155429 := by exact prefixLift 1155429
  have htrace : WordTrace (prefixWord ++ tailWord_1155429) baseStart_1155429 baseEnd_1155429 := by
    simpa [prefixWord, tailWord_1155429, baseEnd_1155429] using wordTrace_append hprefix tailTrace_1155429
  have hstable : (prefixWord ++ tailWord_1155429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155429).length < 2 ^ (prefixWord ++ tailWord_1155429).sum := by decide
  have hdescent : baseEnd_1155429 < baseStart_1155429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155435 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 7, 2]
def baseStart_1155435 : Nat := 118140960795 + 1155435 * 2 ^ 59
def prefixEnd_1155435 : Nat := 4983230072969 + 3 ^ 40 * 1155435 * 2
def baseEnd_1155435 : Nat := 593293520027792088948757

theorem tailTrace_1155435 : CollatzResearch.WordTrace tailWord_1155435 prefixEnd_1155435 593293520027792088948757 := by
  unfold tailWord_1155435
  simp only [CollatzResearch.WordTrace]
  refine ⟨42142176569063802432659759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28094784379375868288439839 42142176569063802432659759)
  ·
    refine ⟨63213264853595703648989639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42142176569063802432659759 63213264853595703648989639)
    ·
      refine ⟨94819897280393555473484459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63213264853595703648989639 94819897280393555473484459)
      ·
        refine ⟨142229845920590333210226689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94819897280393555473484459 142229845920590333210226689)
        ·
          refine ⟨106672384440442749907670017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142229845920590333210226689 106672384440442749907670017)
          ·
            refine ⟨80004288330332062430752513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106672384440442749907670017 80004288330332062430752513)
            ·
              refine ⟨60003216247749046823064385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80004288330332062430752513 60003216247749046823064385)
              ·
                refine ⟨45002412185811785117298289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60003216247749046823064385 45002412185811785117298289)
                ·
                  refine ⟨33751809139358838837973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45002412185811785117298289 33751809139358838837973717)
                  ·
                    refine ⟨791058026703722785265009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33751809139358838837973717 791058026703722785265009)
                    ·
                      refine ⟨593293520027792088948757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791058026703722785265009 593293520027792088948757)
                      ·
                        rfl

theorem cell23_1155435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7, 2].length) (baseStart_1155435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155435 prefixEnd_1155435 := by exact prefixLift 1155435
  have htrace : WordTrace (prefixWord ++ tailWord_1155435) baseStart_1155435 baseEnd_1155435 := by
    simpa [prefixWord, tailWord_1155435, baseEnd_1155435] using wordTrace_append hprefix tailTrace_1155435
  have hstable : (prefixWord ++ tailWord_1155435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155435).length < 2 ^ (prefixWord ++ tailWord_1155435).sum := by decide
  have hdescent : baseEnd_1155435 < baseStart_1155435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155442 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1155442 : Nat := 118140960795 + 1155442 * 2 ^ 59
def prefixEnd_1155442 : Nat := 4983230072969 + 3 ^ 40 * 1155442 * 2
def baseEnd_1155442 : Nat := 593297114392373561561225

theorem tailTrace_1155442 : CollatzResearch.WordTrace tailWord_1155442 prefixEnd_1155442 593297114392373561561225 := by
  unfold tailWord_1155442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535607970009610657041145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28094954586692295085443053 10535607970009610657041145)
  ·
    refine ⟨7901705977507207992780859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10535607970009610657041145 7901705977507207992780859)
    ·
      refine ⟨11852558966260811989171289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901705977507207992780859 11852558966260811989171289)
      ·
        refine ⟨8889419224695608991878467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11852558966260811989171289 8889419224695608991878467)
        ·
          refine ⟨13334128837043413487817701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8889419224695608991878467 13334128837043413487817701)
          ·
            refine ⟨2500149156945640028965819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13334128837043413487817701 2500149156945640028965819)
            ·
              refine ⟨3750223735418460043448729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500149156945640028965819 3750223735418460043448729)
              ·
                refine ⟨2812667801563845032586547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750223735418460043448729 2812667801563845032586547)
                ·
                  refine ⟨4219001702345767548879821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812667801563845032586547 4219001702345767548879821)
                  ·
                    refine ⟨1582125638379662830829933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4219001702345767548879821 1582125638379662830829933)
                    ·
                      refine ⟨593297114392373561561225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582125638379662830829933 593297114392373561561225)
                      ·
                        rfl

theorem cell23_1155442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1155442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155442 prefixEnd_1155442 := by exact prefixLift 1155442
  have htrace : WordTrace (prefixWord ++ tailWord_1155442) baseStart_1155442 baseEnd_1155442 := by
    simpa [prefixWord, tailWord_1155442, baseEnd_1155442] using wordTrace_append hprefix tailTrace_1155442
  have hstable : (prefixWord ++ tailWord_1155442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155442).length < 2 ^ (prefixWord ++ tailWord_1155442).sum := by decide
  have hdescent : baseEnd_1155442 < baseStart_1155442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155446 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1155446 : Nat := 118140960795 + 1155446 * 2 ^ 59
def prefixEnd_1155446 : Nat := 4983230072969 + 3 ^ 40 * 1155446 * 2
def baseEnd_1155446 : Nat := 593299168314991545911207

theorem tailTrace_1155446 : CollatzResearch.WordTrace tailWord_1155446 prefixEnd_1155446 593299168314991545911207 := by
  unfold tailWord_1155446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633911110751496956956887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28095051848015967540873461 2633911110751496956956887)
  ·
    refine ⟨3950866666127245435435331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633911110751496956956887 3950866666127245435435331)
    ·
      refine ⟨5926299999190868153152997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3950866666127245435435331 5926299999190868153152997)
      ·
        refine ⟨1111181249848287778716187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5926299999190868153152997 1111181249848287778716187)
        ·
          refine ⟨1666771874772431668074281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111181249848287778716187 1666771874772431668074281)
          ·
            refine ⟨1250078906079323751055711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666771874772431668074281 1250078906079323751055711)
            ·
              refine ⟨1875118359118985626583567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250078906079323751055711 1875118359118985626583567)
              ·
                refine ⟨2812677538678478439875351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875118359118985626583567 2812677538678478439875351)
                ·
                  refine ⟨4219016308017717659813027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2812677538678478439875351 4219016308017717659813027)
                  ·
                    refine ⟨6328524462026576489719541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4219016308017717659813027 6328524462026576489719541)
                    ·
                      refine ⟨593299168314991545911207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6328524462026576489719541 593299168314991545911207)
                      ·
                        rfl

theorem cell23_1155446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1155446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155446 prefixEnd_1155446 := by exact prefixLift 1155446
  have htrace : WordTrace (prefixWord ++ tailWord_1155446) baseStart_1155446 baseEnd_1155446 := by
    simpa [prefixWord, tailWord_1155446, baseEnd_1155446] using wordTrace_append hprefix tailTrace_1155446
  have hstable : (prefixWord ++ tailWord_1155446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155446).length < 2 ^ (prefixWord ++ tailWord_1155446).sum := by decide
  have hdescent : baseEnd_1155446 < baseStart_1155446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155465 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_1155465 : Nat := 118140960795 + 1155465 * 2 ^ 59
def prefixEnd_1155465 : Nat := 4983230072969 + 3 ^ 40 * 1155465 * 2
def baseEnd_1155465 : Nat := 593308924447426971573619

theorem tailTrace_1155465 : CollatzResearch.WordTrace tailWord_1155465 prefixEnd_1155465 593308924447426971573619 := by
  unfold tailWord_1155465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42143270758955117556251849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28095513839303411704167899 42143270758955117556251849)
  ·
    refine ⟨31607453069216338167188887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42143270758955117556251849 31607453069216338167188887)
    ·
      refine ⟨47411179603824507250783331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31607453069216338167188887 47411179603824507250783331)
      ·
        refine ⟨71116769405736760876174997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47411179603824507250783331 71116769405736760876174997)
        ·
          refine ⟨3333598565893910666070703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71116769405736760876174997 3333598565893910666070703)
          ·
            refine ⟨5000397848840865999106055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333598565893910666070703 5000397848840865999106055)
            ·
              refine ⟨7500596773261298998659083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5000397848840865999106055 7500596773261298998659083)
              ·
                refine ⟨11250895159891948497988625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7500596773261298998659083 11250895159891948497988625)
                ·
                  refine ⟨8438171369918961373491469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11250895159891948497988625 8438171369918961373491469)
                  ·
                    refine ⟨3164314263719610515059301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8438171369918961373491469 3164314263719610515059301)
                    ·
                      refine ⟨593308924447426971573619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3164314263719610515059301 593308924447426971573619)
                      ·
                        rfl

theorem cell23_1155465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_1155465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155465 prefixEnd_1155465 := by exact prefixLift 1155465
  have htrace : WordTrace (prefixWord ++ tailWord_1155465) baseStart_1155465 baseEnd_1155465 := by
    simpa [prefixWord, tailWord_1155465, baseEnd_1155465] using wordTrace_append hprefix tailTrace_1155465
  have hstable : (prefixWord ++ tailWord_1155465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155465).length < 2 ^ (prefixWord ++ tailWord_1155465).sum := by decide
  have hdescent : baseEnd_1155465 < baseStart_1155465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155486 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1155486 : Nat := 118140960795 + 1155486 * 2 ^ 59
def prefixEnd_1155486 : Nat := 4983230072969 + 3 ^ 40 * 1155486 * 2
def baseEnd_1155486 : Nat := 593319707541171389411023

theorem tailTrace_1155486 : CollatzResearch.WordTrace tailWord_1155486 prefixEnd_1155486 593319707541171389411023 := by
  unfold tailWord_1155486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5268004586484879767845789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28096024461252692095177541 5268004586484879767845789)
  ·
    refine ⟨1975501719931829912942171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5268004586484879767845789 1975501719931829912942171)
    ·
      refine ⟨2963252579897744869413257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975501719931829912942171 2963252579897744869413257)
      ·
        refine ⟨2222439434923308652059943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2963252579897744869413257 2222439434923308652059943)
        ·
          refine ⟨3333659152384962978089915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222439434923308652059943 3333659152384962978089915)
          ·
            refine ⟨5000488728577444467134873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3333659152384962978089915 5000488728577444467134873)
            ·
              refine ⟨3750366546433083350351155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5000488728577444467134873 3750366546433083350351155)
              ·
                refine ⟨5625549819649625025526733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750366546433083350351155 5625549819649625025526733)
                ·
                  refine ⟨2109581182368609384572525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5625549819649625025526733 2109581182368609384572525)
                  ·
                    refine ⟨791092943388228519214697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2109581182368609384572525 791092943388228519214697)
                    ·
                      refine ⟨593319707541171389411023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791092943388228519214697 593319707541171389411023)
                      ·
                        rfl

theorem cell23_1155486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1155486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155486 prefixEnd_1155486 := by exact prefixLift 1155486
  have htrace : WordTrace (prefixWord ++ tailWord_1155486) baseStart_1155486 baseEnd_1155486 := by
    simpa [prefixWord, tailWord_1155486, baseEnd_1155486] using wordTrace_append hprefix tailTrace_1155486
  have hstable : (prefixWord ++ tailWord_1155486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155486).length < 2 ^ (prefixWord ++ tailWord_1155486).sum := by decide
  have hdescent : baseEnd_1155486 < baseStart_1155486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155516 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1155516 : Nat := 118140960795 + 1155516 * 2 ^ 59
def prefixEnd_1155516 : Nat := 4983230072969 + 3 ^ 40 * 1155516 * 2
def baseEnd_1155516 : Nat := 593335111960806272035885

theorem tailTrace_1155516 : CollatzResearch.WordTrace tailWord_1155516 prefixEnd_1155516 593335111960806272035885 := by
  unfold tailWord_1155516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21072565440885176633179201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28096753921180235510905601 21072565440885176633179201)
  ·
    refine ⟨15804424080663882474884401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21072565440885176633179201 15804424080663882474884401)
    ·
      refine ⟨11853318060497911856163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804424080663882474884401 11853318060497911856163301)
      ·
        refine ⟨2222497136343358473030619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11853318060497911856163301 2222497136343358473030619)
        ·
          refine ⟨3333745704515037709545929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222497136343358473030619 3333745704515037709545929)
          ·
            refine ⟨2500309278386278282159447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333745704515037709545929 2500309278386278282159447)
            ·
              refine ⟨3750463917579417423239171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500309278386278282159447 3750463917579417423239171)
              ·
                refine ⟨5625695876369126134858757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750463917579417423239171 5625695876369126134858757)
                ·
                  refine ⟨1054817976819211150286017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5625695876369126134858757 1054817976819211150286017)
                  ·
                    refine ⟨791113482614408362714513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054817976819211150286017 791113482614408362714513)
                    ·
                      refine ⟨593335111960806272035885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791113482614408362714513 593335111960806272035885)
                      ·
                        rfl

theorem cell23_1155516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1155516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155516 prefixEnd_1155516 := by exact prefixLift 1155516
  have htrace : WordTrace (prefixWord ++ tailWord_1155516) baseStart_1155516 baseEnd_1155516 := by
    simpa [prefixWord, tailWord_1155516, baseEnd_1155516] using wordTrace_append hprefix tailTrace_1155516
  have hstable : (prefixWord ++ tailWord_1155516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155516).length < 2 ^ (prefixWord ++ tailWord_1155516).sum := by decide
  have hdescent : baseEnd_1155516 < baseStart_1155516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155573 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 5]
def baseStart_1155573 : Nat := 118140960795 + 1155573 * 2 ^ 59
def prefixEnd_1155573 : Nat := 4983230072969 + 3 ^ 40 * 1155573 * 2
def baseEnd_1155573 : Nat := 65929375595345838780347

theorem tailTrace_1155573 : CollatzResearch.WordTrace tailWord_1155573 prefixEnd_1155573 65929375595345838780347 := by
  unfold tailWord_1155573
  simp only [CollatzResearch.WordTrace]
  refine ⟨42147209842563852001183373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28098139895042568000788915 42147209842563852001183373)
  ·
    refine ⟨15805203690961444500443765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42147209842563852001183373 15805203690961444500443765)
    ·
      refine ⟨1481737846027635421916603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15805203690961444500443765 1481737846027635421916603)
      ·
        refine ⟨2222606769041453132874905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481737846027635421916603 2222606769041453132874905)
        ·
          refine ⟨1666955076781089849656179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2222606769041453132874905 1666955076781089849656179)
          ·
            refine ⟨2500432615171634774484269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666955076781089849656179 2500432615171634774484269)
            ·
              refine ⟨937662230689363040431601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500432615171634774484269 937662230689363040431601)
              ·
                refine ⟨703246673017022280323701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937662230689363040431601 703246673017022280323701)
                ·
                  refine ⟨65929375595345838780347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 703246673017022280323701 65929375595345838780347)
                  ·
                    rfl

theorem cell23_1155573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_1155573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155573 prefixEnd_1155573 := by exact prefixLift 1155573
  have htrace : WordTrace (prefixWord ++ tailWord_1155573) baseStart_1155573 baseEnd_1155573 := by
    simpa [prefixWord, tailWord_1155573, baseEnd_1155573] using wordTrace_append hprefix tailTrace_1155573
  have hstable : (prefixWord ++ tailWord_1155573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155573).length < 2 ^ (prefixWord ++ tailWord_1155573).sum := by decide
  have hdescent : baseEnd_1155573 < baseStart_1155573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155592 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_1155592 : Nat := 118140960795 + 1155592 * 2 ^ 59
def prefixEnd_1155592 : Nat := 4983230072969 + 3 ^ 40 * 1155592 * 2
def baseEnd_1155592 : Nat := 593374136490547974685535

theorem tailTrace_1155592 : CollatzResearch.WordTrace tailWord_1155592 prefixEnd_1155592 593374136490547974685535 := by
  unfold tailWord_1155592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21073951414747509123062515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28098601886330012164083353 21073951414747509123062515)
  ·
    refine ⟨31610927122121263684593773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21073951414747509123062515 31610927122121263684593773)
    ·
      refine ⟨11854097670795473881722665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31610927122121263684593773 11854097670795473881722665)
      ·
        refine ⟨8890573253096605411291999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11854097670795473881722665 8890573253096605411291999)
        ·
          refine ⟨13335859879644908116937999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890573253096605411291999 13335859879644908116937999)
          ·
            refine ⟨20003789819467362175406999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13335859879644908116937999 20003789819467362175406999)
            ·
              refine ⟨30005684729201043263110499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20003789819467362175406999 30005684729201043263110499)
              ·
                refine ⟨45008527093801564894665749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30005684729201043263110499 45008527093801564894665749)
                ·
                  refine ⟨2109774707521948354437457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45008527093801564894665749 2109774707521948354437457)
                  ·
                    refine ⟨1582331030641461265828093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109774707521948354437457 1582331030641461265828093)
                    ·
                      refine ⟨593374136490547974685535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582331030641461265828093 593374136490547974685535)
                      ·
                        rfl

theorem cell23_1155592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_1155592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155592 prefixEnd_1155592 := by exact prefixLift 1155592
  have htrace : WordTrace (prefixWord ++ tailWord_1155592) baseStart_1155592 baseEnd_1155592 := by
    simpa [prefixWord, tailWord_1155592, baseEnd_1155592] using wordTrace_append hprefix tailTrace_1155592
  have hstable : (prefixWord ++ tailWord_1155592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155592).length < 2 ^ (prefixWord ++ tailWord_1155592).sum := by decide
  have hdescent : baseEnd_1155592 < baseStart_1155592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155615 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1155615 : Nat := 118140960795 + 1155615 * 2 ^ 59
def prefixEnd_1155615 : Nat := 4983230072969 + 3 ^ 40 * 1155615 * 2
def baseEnd_1155615 : Nat := 593385946545601384697929

theorem tailTrace_1155615 : CollatzResearch.WordTrace tailWord_1155615 prefixEnd_1155615 593385946545601384697929 := by
  unfold tailWord_1155615
  simp only [CollatzResearch.WordTrace]
  refine ⟨42148741708411693174212299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28099161138941128782808199 42148741708411693174212299)
  ·
    refine ⟨63223112562617539761318449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42148741708411693174212299 63223112562617539761318449)
    ·
      refine ⟨47417334421963154820988837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63223112562617539761318449 47417334421963154820988837)
      ·
        refine ⟨8890750204118091528935407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47417334421963154820988837 8890750204118091528935407)
        ·
          refine ⟨13336125306177137293403111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8890750204118091528935407 13336125306177137293403111)
          ·
            refine ⟨20004187959265705940104667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13336125306177137293403111 20004187959265705940104667)
            ·
              refine ⟨30006281938898558910157001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20004187959265705940104667 30006281938898558910157001)
              ·
                refine ⟨22504711454173919182617751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30006281938898558910157001 22504711454173919182617751)
                ·
                  refine ⟨33757067181260878773926627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22504711454173919182617751 33757067181260878773926627)
                  ·
                    refine ⟨50635600771891318160889941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33757067181260878773926627 50635600771891318160889941)
                    ·
                      refine ⟨593385946545601384697929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50635600771891318160889941 593385946545601384697929)
                      ·
                        rfl

theorem cell23_1155615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1155615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155615 prefixEnd_1155615 := by exact prefixLift 1155615
  have htrace : WordTrace (prefixWord ++ tailWord_1155615) baseStart_1155615 baseEnd_1155615 := by
    simpa [prefixWord, tailWord_1155615, baseEnd_1155615] using wordTrace_append hprefix tailTrace_1155615
  have hstable : (prefixWord ++ tailWord_1155615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155615).length < 2 ^ (prefixWord ++ tailWord_1155615).sum := by decide
  have hdescent : baseEnd_1155615 < baseStart_1155615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155639 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_1155639 : Nat := 118140960795 + 1155639 * 2 ^ 59
def prefixEnd_1155639 : Nat := 4983230072969 + 3 ^ 40 * 1155639 * 2
def baseEnd_1155639 : Nat := 593398270081309290797819

theorem tailTrace_1155639 : CollatzResearch.WordTrace tailWord_1155639 prefixEnd_1155639 593398270081309290797819 := by
  unfold tailWord_1155639
  simp only [CollatzResearch.WordTrace]
  refine ⟨42149617060324745273085971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28099744706883163515390647 42149617060324745273085971)
  ·
    refine ⟨63224425590487117909628957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42149617060324745273085971 63224425590487117909628957)
    ·
      refine ⟨23709159596432669216110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63224425590487117909628957 23709159596432669216110859)
      ·
        refine ⟨35563739394649003824166289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23709159596432669216110859 35563739394649003824166289)
        ·
          refine ⟨26672804545986752868124717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35563739394649003824166289 26672804545986752868124717)
          ·
            refine ⟨10002301704745032325546769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26672804545986752868124717 10002301704745032325546769)
            ·
              refine ⟨7501726278558774244160077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002301704745032325546769 7501726278558774244160077)
              ·
                refine ⟨2813147354459540341560029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7501726278558774244160077 2813147354459540341560029)
                ·
                  refine ⟨1054930257922327628085011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2813147354459540341560029 1054930257922327628085011)
                  ·
                    refine ⟨1582395386883491442127517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054930257922327628085011 1582395386883491442127517)
                    ·
                      refine ⟨593398270081309290797819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582395386883491442127517 593398270081309290797819)
                      ·
                        rfl

theorem cell23_1155639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_1155639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155639 prefixEnd_1155639 := by exact prefixLift 1155639
  have htrace : WordTrace (prefixWord ++ tailWord_1155639) baseStart_1155639 baseEnd_1155639 := by
    simpa [prefixWord, tailWord_1155639, baseEnd_1155639] using wordTrace_append hprefix tailTrace_1155639
  have hstable : (prefixWord ++ tailWord_1155639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155639).length < 2 ^ (prefixWord ++ tailWord_1155639).sum := by decide
  have hdescent : baseEnd_1155639 < baseStart_1155639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155642 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_1155642 : Nat := 118140960795 + 1155642 * 2 ^ 59
def prefixEnd_1155642 : Nat := 4983230072969 + 3 ^ 40 * 1155642 * 2
def baseEnd_1155642 : Nat := 197799936841090926353435

theorem tailTrace_1155642 : CollatzResearch.WordTrace tailWord_1155642 prefixEnd_1155642 197799936841090926353435 := by
  unfold tailWord_1155642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537431619828469196361295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28099817652875917856963453 10537431619828469196361295)
  ·
    refine ⟨15806147429742703794541943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537431619828469196361295 15806147429742703794541943)
    ·
      refine ⟨23709221144614055691812915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15806147429742703794541943 23709221144614055691812915)
      ·
        refine ⟨35563831716921083537719373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23709221144614055691812915 35563831716921083537719373)
        ·
          refine ⟨13336436893845406326644765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35563831716921083537719373 13336436893845406326644765)
          ·
            refine ⟨5001163835192027372491787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13336436893845406326644765 5001163835192027372491787)
            ·
              refine ⟨7501745752788041058737681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001163835192027372491787 7501745752788041058737681)
              ·
                refine ⟨5626309314591030794053261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7501745752788041058737681 5626309314591030794053261)
                ·
                  refine ⟨2109865992971636547769973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5626309314591030794053261 2109865992971636547769973)
                  ·
                    refine ⟨197799936841090926353435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2109865992971636547769973 197799936841090926353435)
                    ·
                      rfl

theorem cell23_1155642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_1155642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155642 prefixEnd_1155642 := by exact prefixLift 1155642
  have htrace : WordTrace (prefixWord ++ tailWord_1155642) baseStart_1155642 baseEnd_1155642 := by
    simpa [prefixWord, tailWord_1155642, baseEnd_1155642] using wordTrace_append hprefix tailTrace_1155642
  have hstable : (prefixWord ++ tailWord_1155642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155642).length < 2 ^ (prefixWord ++ tailWord_1155642).sum := by decide
  have hdescent : baseEnd_1155642 < baseStart_1155642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155672 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1155672 : Nat := 118140960795 + 1155672 * 2 ^ 59
def prefixEnd_1155672 : Nat := 4983230072969 + 3 ^ 40 * 1155672 * 2
def baseEnd_1155672 : Nat := 197805071647635887228389

theorem tailTrace_1155672 : CollatzResearch.WordTrace tailWord_1155672 prefixEnd_1155672 197805071647635887228389 := by
  unfold tailWord_1155672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21075410334602595954518635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28100547112803461272691513 21075410334602595954518635)
  ·
    refine ⟨31613115501903893931777953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21075410334602595954518635 31613115501903893931777953)
    ·
      refine ⟨23709836626427920448833465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31613115501903893931777953 23709836626427920448833465)
      ·
        refine ⟨17782377469820940336625099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23709836626427920448833465 17782377469820940336625099)
        ·
          refine ⟨26673566204731410504937649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17782377469820940336625099 26673566204731410504937649)
          ·
            refine ⟨20005174653548557878703237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26673566204731410504937649 20005174653548557878703237)
            ·
              refine ⟨3750970247540354602256857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20005174653548557878703237 3750970247540354602256857)
              ·
                refine ⟨2813227685655265951692643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750970247540354602256857 2813227685655265951692643)
                ·
                  refine ⟨4219841528482898927538965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813227685655265951692643 4219841528482898927538965)
                  ·
                    refine ⟨197805071647635887228389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4219841528482898927538965 197805071647635887228389)
                    ·
                      rfl

theorem cell23_1155672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1155672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155672 prefixEnd_1155672 := by exact prefixLift 1155672
  have htrace : WordTrace (prefixWord ++ tailWord_1155672) baseStart_1155672 baseEnd_1155672 := by
    simpa [prefixWord, tailWord_1155672, baseEnd_1155672] using wordTrace_append hprefix tailTrace_1155672
  have hstable : (prefixWord ++ tailWord_1155672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155672).length < 2 ^ (prefixWord ++ tailWord_1155672).sum := by decide
  have hdescent : baseEnd_1155672 < baseStart_1155672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155676 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1155676 : Nat := 118140960795 + 1155676 * 2 ^ 59
def prefixEnd_1155676 : Nat := 4983230072969 + 3 ^ 40 * 1155676 * 2
def baseEnd_1155676 : Nat := 197805756288508548678383

theorem tailTrace_1155676 : CollatzResearch.WordTrace tailWord_1155676 prefixEnd_1155676 197805756288508548678383 := by
  unfold tailWord_1155676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21075483280595350296091441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28100644374127133728121921 21075483280595350296091441)
  ·
    refine ⟨15806612460446512722068581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21075483280595350296091441 15806612460446512722068581)
    ·
      refine ⟨2963739836333721135387859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15806612460446512722068581 2963739836333721135387859)
      ·
        refine ⟨4445609754500581703081789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963739836333721135387859 4445609754500581703081789)
        ·
          refine ⟨1667103657937718138655671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4445609754500581703081789 1667103657937718138655671)
          ·
            refine ⟨2500655486906577207983507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667103657937718138655671 2500655486906577207983507)
            ·
              refine ⟨3750983230359865811975261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500655486906577207983507 3750983230359865811975261)
              ·
                refine ⟨1406618711384949679490723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3750983230359865811975261 1406618711384949679490723)
                ·
                  refine ⟨2109928067077424519236085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406618711384949679490723 2109928067077424519236085)
                  ·
                    refine ⟨197805756288508548678383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2109928067077424519236085 197805756288508548678383)
                    ·
                      rfl

theorem cell23_1155676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1155676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155676 prefixEnd_1155676 := by exact prefixLift 1155676
  have htrace : WordTrace (prefixWord ++ tailWord_1155676) baseStart_1155676 baseEnd_1155676 := by
    simpa [prefixWord, tailWord_1155676, baseEnd_1155676] using wordTrace_append hprefix tailTrace_1155676
  have hstable : (prefixWord ++ tailWord_1155676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155676).length < 2 ^ (prefixWord ++ tailWord_1155676).sum := by decide
  have hdescent : baseEnd_1155676 < baseStart_1155676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155692 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1155692 : Nat := 118140960795 + 1155692 * 2 ^ 59
def prefixEnd_1155692 : Nat := 4983230072969 + 3 ^ 40 * 1155692 * 2
def baseEnd_1155692 : Nat := 593425484555997583435075

theorem tailTrace_1155692 : CollatzResearch.WordTrace tailWord_1155692 prefixEnd_1155692 593425484555997583435075 := by
  unfold tailWord_1155692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21075775064566367662382665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28101033419421823549843553 21075775064566367662382665)
  ·
    refine ⟨15806831298424775746786999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21075775064566367662382665 15806831298424775746786999)
    ·
      refine ⟨23710246947637163620180499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15806831298424775746786999 23710246947637163620180499)
      ·
        refine ⟨35565370421455745430270749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23710246947637163620180499 35565370421455745430270749)
        ·
          refine ⟨13337013908045904536351531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35565370421455745430270749 13337013908045904536351531)
          ·
            refine ⟨20005520862068856804527297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13337013908045904536351531 20005520862068856804527297)
            ·
              refine ⟨15004140646551642603395473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20005520862068856804527297 15004140646551642603395473)
              ·
                refine ⟨11253105484913731952546605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15004140646551642603395473 11253105484913731952546605)
                ·
                  refine ⟨4219914556842649482204977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11253105484913731952546605 4219914556842649482204977)
                  ·
                    refine ⟨3164935917631987111653733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4219914556842649482204977 3164935917631987111653733)
                    ·
                      refine ⟨593425484555997583435075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3164935917631987111653733 593425484555997583435075)
                      ·
                        rfl

theorem cell23_1155692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1155692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155692 prefixEnd_1155692 := by exact prefixLift 1155692
  have htrace : WordTrace (prefixWord ++ tailWord_1155692) baseStart_1155692 baseEnd_1155692 := by
    simpa [prefixWord, tailWord_1155692, baseEnd_1155692] using wordTrace_append hprefix tailTrace_1155692
  have hstable : (prefixWord ++ tailWord_1155692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155692).length < 2 ^ (prefixWord ++ tailWord_1155692).sum := by decide
  have hdescent : baseEnd_1155692 < baseStart_1155692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155709 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1155709 : Nat := 118140960795 + 1155709 * 2 ^ 59
def prefixEnd_1155709 : Nat := 4983230072969 + 3 ^ 40 * 1155709 * 2
def baseEnd_1155709 : Nat := 593434213727124016922497

theorem tailTrace_1155709 : CollatzResearch.WordTrace tailWord_1155709 prefixEnd_1155709 593434213727124016922497 := by
  unfold tailWord_1155709
  simp only [CollatzResearch.WordTrace]
  refine ⟨42152170170071147228134181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28101446780047431485422787 42152170170071147228134181)
  ·
    refine ⟨7903531906888340105275159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42152170170071147228134181 7903531906888340105275159)
    ·
      refine ⟨11855297860332510157912739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7903531906888340105275159 11855297860332510157912739)
      ·
        refine ⟨17782946790498765236869109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11855297860332510157912739 17782946790498765236869109)
        ·
          refine ⟨1667151261609259240956479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17782946790498765236869109 1667151261609259240956479)
          ·
            refine ⟨2500726892413888861434719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667151261609259240956479 2500726892413888861434719)
            ·
              refine ⟨3751090338620833292152079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500726892413888861434719 3751090338620833292152079)
              ·
                refine ⟨5626635507931249938228119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751090338620833292152079 5626635507931249938228119)
                ·
                  refine ⟨8439953261896874907342179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5626635507931249938228119 8439953261896874907342179)
                  ·
                    refine ⟨12659929892845312361013269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8439953261896874907342179 12659929892845312361013269)
                    ·
                      refine ⟨593434213727124016922497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12659929892845312361013269 593434213727124016922497)
                      ·
                        rfl

theorem cell23_1155709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1155709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155709 prefixEnd_1155709 := by exact prefixLift 1155709
  have htrace : WordTrace (prefixWord ++ tailWord_1155709) baseStart_1155709 baseEnd_1155709 := by
    simpa [prefixWord, tailWord_1155709, baseEnd_1155709] using wordTrace_append hprefix tailTrace_1155709
  have hstable : (prefixWord ++ tailWord_1155709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155709).length < 2 ^ (prefixWord ++ tailWord_1155709).sum := by decide
  have hdescent : baseEnd_1155709 < baseStart_1155709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155716 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1155716 : Nat := 118140960795 + 1155716 * 2 ^ 59
def prefixEnd_1155716 : Nat := 4983230072969 + 3 ^ 40 * 1155716 * 2
def baseEnd_1155716 : Nat := 593437808091705489534965

theorem tailTrace_1155716 : CollatzResearch.WordTrace tailWord_1155716 prefixEnd_1155716 593437808091705489534965 := by
  unfold tailWord_1155716
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076212740522893711819501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28101616987363858282426001 21076212740522893711819501)
  ·
    refine ⟨7903579777696085141932313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21076212740522893711819501 7903579777696085141932313)
    ·
      refine ⟨5927684833272063856449235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7903579777696085141932313 5927684833272063856449235)
      ·
        refine ⟨8891527249908095784673853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5927684833272063856449235 8891527249908095784673853)
        ·
          refine ⟨3334322718715535919252695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8891527249908095784673853 3334322718715535919252695)
          ·
            refine ⟨5001484078073303878879043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334322718715535919252695 5001484078073303878879043)
            ·
              refine ⟨7502226117109955818318565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001484078073303878879043 7502226117109955818318565)
              ·
                refine ⟨1406667396958116715934731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7502226117109955818318565 1406667396958116715934731)
                ·
                  refine ⟨2110001095437175073902097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406667396958116715934731 2110001095437175073902097)
                  ·
                    refine ⟨1582500821577881305426573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110001095437175073902097 1582500821577881305426573)
                    ·
                      refine ⟨593437808091705489534965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582500821577881305426573 593437808091705489534965)
                      ·
                        rfl

theorem cell23_1155716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1155716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155716 prefixEnd_1155716 := by exact prefixLift 1155716
  have htrace : WordTrace (prefixWord ++ tailWord_1155716) baseStart_1155716 baseEnd_1155716 := by
    simpa [prefixWord, tailWord_1155716, baseEnd_1155716] using wordTrace_append hprefix tailTrace_1155716
  have hstable : (prefixWord ++ tailWord_1155716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155716).length < 2 ^ (prefixWord ++ tailWord_1155716).sum := by decide
  have hdescent : baseEnd_1155716 < baseStart_1155716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155762 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_1155762 : Nat := 118140960795 + 1155762 * 2 ^ 59
def prefixEnd_1155762 : Nat := 4983230072969 + 3 ^ 40 * 1155762 * 2
def baseEnd_1155762 : Nat := 197820476067270769853251

theorem tailTrace_1155762 : CollatzResearch.WordTrace tailWord_1155762 prefixEnd_1155762 197820476067270769853251 := by
  unfold tailWord_1155762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538525809719784319953385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28102735492586091519875693 10538525809719784319953385)
  ·
    refine ⟨7903894357289838239965039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10538525809719784319953385 7903894357289838239965039)
    ·
      refine ⟨11855841535934757359947559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7903894357289838239965039 11855841535934757359947559)
      ·
        refine ⟨17783762303902136039921339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11855841535934757359947559 17783762303902136039921339)
        ·
          refine ⟨26675643455853204059882009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17783762303902136039921339 26675643455853204059882009)
          ·
            refine ⟨20006732591889903044911507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26675643455853204059882009 20006732591889903044911507)
            ·
              refine ⟨30010098887834854567367261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20006732591889903044911507 30010098887834854567367261)
              ·
                refine ⟨11253787082938070462762723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30010098887834854567367261 11253787082938070462762723)
                ·
                  refine ⟨16880680624407105694144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11253787082938070462762723 16880680624407105694144085)
                  ·
                    refine ⟨197820476067270769853251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16880680624407105694144085 197820476067270769853251)
                    ·
                      rfl

theorem cell23_1155762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_1155762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155762 prefixEnd_1155762 := by exact prefixLift 1155762
  have htrace : WordTrace (prefixWord ++ tailWord_1155762) baseStart_1155762 baseEnd_1155762 := by
    simpa [prefixWord, tailWord_1155762, baseEnd_1155762] using wordTrace_append hprefix tailTrace_1155762
  have hstable : (prefixWord ++ tailWord_1155762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155762).length < 2 ^ (prefixWord ++ tailWord_1155762).sum := by decide
  have hdescent : baseEnd_1155762 < baseStart_1155762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155763 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 2, 1, 3]
def baseStart_1155763 : Nat := 118140960795 + 1155763 * 2 ^ 59
def prefixEnd_1155763 : Nat := 4983230072969 + 3 ^ 40 * 1155763 * 2
def baseEnd_1155763 : Nat := 593461941682466805647249

theorem tailTrace_1155763 : CollatzResearch.WordTrace tailWord_1155763 prefixEnd_1155763 593461941682466805647249 := by
  unfold tailWord_1155763
  simp only [CollatzResearch.WordTrace]
  refine ⟨42154139711875514450599943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28102759807917009633733295 42154139711875514450599943)
  ·
    refine ⟨63231209567813271675899915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42154139711875514450599943 63231209567813271675899915)
    ·
      refine ⟨94846814351719907513849873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63231209567813271675899915 94846814351719907513849873)
      ·
        refine ⟨71135110763789930635387405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94846814351719907513849873 71135110763789930635387405)
        ·
          refine ⟨26675666536421223988270277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71135110763789930635387405 26675666536421223988270277)
          ·
            refine ⟨5001687475578979497800677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26675666536421223988270277 5001687475578979497800677)
            ·
              refine ⟨937816401671058655837627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5001687475578979497800677 937816401671058655837627)
              ·
                refine ⟨1406724602506587983756441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937816401671058655837627 1406724602506587983756441)
                ·
                  refine ⟨1055043451879940987817331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1406724602506587983756441 1055043451879940987817331)
                  ·
                    refine ⟨1582565177819911481725997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1055043451879940987817331 1582565177819911481725997)
                    ·
                      refine ⟨593461941682466805647249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582565177819911481725997 593461941682466805647249)
                      ·
                        rfl

theorem cell23_1155763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 1, 3].length) (baseStart_1155763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155763 prefixEnd_1155763 := by exact prefixLift 1155763
  have htrace : WordTrace (prefixWord ++ tailWord_1155763) baseStart_1155763 baseEnd_1155763 := by
    simpa [prefixWord, tailWord_1155763, baseEnd_1155763] using wordTrace_append hprefix tailTrace_1155763
  have hstable : (prefixWord ++ tailWord_1155763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155763).length < 2 ^ (prefixWord ++ tailWord_1155763).sum := by decide
  have hdescent : baseEnd_1155763 < baseStart_1155763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155773 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_1155773 : Nat := 118140960795 + 1155773 * 2 ^ 59
def prefixEnd_1155773 : Nat := 4983230072969 + 3 ^ 40 * 1155773 * 2
def baseEnd_1155773 : Nat := 593467076489011766522203

theorem tailTrace_1155773 : CollatzResearch.WordTrace tailWord_1155773 prefixEnd_1155773 593467076489011766522203 := by
  unfold tailWord_1155773
  simp only [CollatzResearch.WordTrace]
  refine ⟨42154504441839286158463973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28103002961226190772309315 42154504441839286158463973)
  ·
    refine ⟨7903969582844866154711995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42154504441839286158463973 7903969582844866154711995)
    ·
      refine ⟨11855954374267299232067993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7903969582844866154711995 11855954374267299232067993)
      ·
        refine ⟨8891965780700474424050995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11855954374267299232067993 8891965780700474424050995)
        ·
          refine ⟨13337948671050711636076493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8891965780700474424050995 13337948671050711636076493)
          ·
            refine ⟨5001730751644016863528685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13337948671050711636076493 5001730751644016863528685)
            ·
              refine ⟨1875649031866506323823257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5001730751644016863528685 1875649031866506323823257)
              ·
                refine ⟨1406736773899879742867443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875649031866506323823257 1406736773899879742867443)
                ·
                  refine ⟨2110105160849819614301165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406736773899879742867443 2110105160849819614301165)
                  ·
                    refine ⟨791289435318682355362937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110105160849819614301165 791289435318682355362937)
                    ·
                      refine ⟨593467076489011766522203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791289435318682355362937 593467076489011766522203)
                      ·
                        rfl

theorem cell23_1155773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_1155773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155773 prefixEnd_1155773 := by exact prefixLift 1155773
  have htrace : WordTrace (prefixWord ++ tailWord_1155773) baseStart_1155773 baseEnd_1155773 := by
    simpa [prefixWord, tailWord_1155773, baseEnd_1155773] using wordTrace_append hprefix tailTrace_1155773
  have hstable : (prefixWord ++ tailWord_1155773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155773).length < 2 ^ (prefixWord ++ tailWord_1155773).sum := by decide
  have hdescent : baseEnd_1155773 < baseStart_1155773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155786 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_1155786 : Nat := 118140960795 + 1155786 * 2 ^ 59
def prefixEnd_1155786 : Nat := 4983230072969 + 3 ^ 40 * 1155786 * 2
def baseEnd_1155786 : Nat := 593473751737520215659643

theorem tailTrace_1155786 : CollatzResearch.WordTrace tailWord_1155786 prefixEnd_1155786 593473751737520215659643 := by
  unfold tailWord_1155786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538744647698047344671803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28103319060528126252458141 10538744647698047344671803)
  ·
    refine ⟨15808116971547071017007705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538744647698047344671803 15808116971547071017007705)
    ·
      refine ⟨11856087728660303262755779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15808116971547071017007705 11856087728660303262755779)
      ·
        refine ⟨17784131592990454894133669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11856087728660303262755779 17784131592990454894133669)
        ·
          refine ⟨3334524673685710292650063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17784131592990454894133669 3334524673685710292650063)
          ·
            refine ⟨5001787010528565438975095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334524673685710292650063 5001787010528565438975095)
            ·
              refine ⟨7502680515792848158462643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001787010528565438975095 7502680515792848158462643)
              ·
                refine ⟨11254020773689272237693965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7502680515792848158462643 11254020773689272237693965)
                ·
                  refine ⟨4220257790133477089135237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11254020773689272237693965 4220257790133477089135237)
                  ·
                    refine ⟨791298335650026954212857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4220257790133477089135237 791298335650026954212857)
                    ·
                      refine ⟨593473751737520215659643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791298335650026954212857 593473751737520215659643)
                      ·
                        rfl

theorem cell23_1155786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_1155786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155786 prefixEnd_1155786 := by exact prefixLift 1155786
  have htrace : WordTrace (prefixWord ++ tailWord_1155786) baseStart_1155786 baseEnd_1155786 := by
    simpa [prefixWord, tailWord_1155786, baseEnd_1155786] using wordTrace_append hprefix tailTrace_1155786
  have hstable : (prefixWord ++ tailWord_1155786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155786).length < 2 ^ (prefixWord ++ tailWord_1155786).sum := by decide
  have hdescent : baseEnd_1155786 < baseStart_1155786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155790 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_1155790 : Nat := 118140960795 + 1155790 * 2 ^ 59
def prefixEnd_1155790 : Nat := 4983230072969 + 3 ^ 40 * 1155790 * 2
def baseEnd_1155790 : Nat := 593475805660138200009625

theorem tailTrace_1155790 : CollatzResearch.WordTrace tailWord_1155790 prefixEnd_1155790 593475805660138200009625 := by
  unfold tailWord_1155790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269390560347212257729103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28103416321851798707888549 5269390560347212257729103)
  ·
    refine ⟨7904085840520818386593655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5269390560347212257729103 7904085840520818386593655)
    ·
      refine ⟨11856128760781227579890483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7904085840520818386593655 11856128760781227579890483)
      ·
        refine ⟨17784193141171841369835725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11856128760781227579890483 17784193141171841369835725)
        ·
          refine ⟨6669072427939440513688397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17784193141171841369835725 6669072427939440513688397)
          ·
            refine ⟨2500902160477290192633149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6669072427939440513688397 2500902160477290192633149)
            ·
              refine ⟨937838310178983822237431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500902160477290192633149 937838310178983822237431)
              ·
                refine ⟨1406757465268475733356147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937838310178983822237431 1406757465268475733356147)
                ·
                  refine ⟨2110136197902713600034221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406757465268475733356147 2110136197902713600034221)
                  ·
                    refine ⟨791301074213517600012833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110136197902713600034221 791301074213517600012833)
                    ·
                      refine ⟨593475805660138200009625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791301074213517600012833 593475805660138200009625)
                      ·
                        rfl

theorem cell23_1155790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_1155790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155790 prefixEnd_1155790 := by exact prefixLift 1155790
  have htrace : WordTrace (prefixWord ++ tailWord_1155790) baseStart_1155790 baseEnd_1155790 := by
    simpa [prefixWord, tailWord_1155790, baseEnd_1155790] using wordTrace_append hprefix tailTrace_1155790
  have hstable : (prefixWord ++ tailWord_1155790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155790).length < 2 ^ (prefixWord ++ tailWord_1155790).sum := by decide
  have hdescent : baseEnd_1155790 < baseStart_1155790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155816 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1155816 : Nat := 118140960795 + 1155816 * 2 ^ 59
def prefixEnd_1155816 : Nat := 4983230072969 + 3 ^ 40 * 1155816 * 2
def baseEnd_1155816 : Nat := 593489156157155098284505

theorem tailTrace_1155816 : CollatzResearch.WordTrace tailWord_1155816 prefixEnd_1155816 593489156157155098284505 := by
  unfold tailWord_1155816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21078036390341752251139651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28104048520455669668186201 21078036390341752251139651)
  ·
    refine ⟨31617054585512628376709477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21078036390341752251139651 31617054585512628376709477)
    ·
      refine ⟨5928197734783617820633027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31617054585512628376709477 5928197734783617820633027)
      ·
        refine ⟨8892296602175426730949541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928197734783617820633027 8892296602175426730949541)
        ·
          refine ⟨1667305612907892512053039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8892296602175426730949541 1667305612907892512053039)
          ·
            refine ⟨2500958419361838768079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667305612907892512053039 2500958419361838768079559)
            ·
              refine ⟨3751437629042758152119339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500958419361838768079559 3751437629042758152119339)
              ·
                refine ⟨5627156443564137228179009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3751437629042758152119339 5627156443564137228179009)
                ·
                  refine ⟨4220367332673102921134257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5627156443564137228179009 4220367332673102921134257)
                  ·
                    refine ⟨3165275499504827190850693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4220367332673102921134257 3165275499504827190850693)
                    ·
                      refine ⟨593489156157155098284505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3165275499504827190850693 593489156157155098284505)
                      ·
                        rfl

theorem cell23_1155816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1155816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155816 prefixEnd_1155816 := by exact prefixLift 1155816
  have htrace : WordTrace (prefixWord ++ tailWord_1155816) baseStart_1155816 baseEnd_1155816 := by
    simpa [prefixWord, tailWord_1155816, baseEnd_1155816] using wordTrace_append hprefix tailTrace_1155816
  have hstable : (prefixWord ++ tailWord_1155816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155816).length < 2 ^ (prefixWord ++ tailWord_1155816).sum := by decide
  have hdescent : baseEnd_1155816 < baseStart_1155816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155859 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4]
def baseStart_1155859 : Nat := 118140960795 + 1155859 * 2 ^ 59
def prefixEnd_1155859 : Nat := 4983230072969 + 3 ^ 40 * 1155859 * 2
def baseEnd_1155859 : Nat := 593511235825298430046807

theorem tailTrace_1155859 : CollatzResearch.WordTrace tailWord_1155859 prefixEnd_1155859 593511235825298430046807 := by
  unfold tailWord_1155859
  simp only [CollatzResearch.WordTrace]
  refine ⟨42157641119527722846094631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28105094079685148564063087 42157641119527722846094631)
  ·
    refine ⟨63236461679291584269141947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42157641119527722846094631 63236461679291584269141947)
    ·
      refine ⟨94854692518937376403712921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63236461679291584269141947 94854692518937376403712921)
      ·
        refine ⟨71141019389203032302784691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94854692518937376403712921 71141019389203032302784691)
        ·
          refine ⟨106711529083804548454177037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71141019389203032302784691 106711529083804548454177037)
          ·
            refine ⟨40016823406426705670316389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106711529083804548454177037 40016823406426705670316389)
            ·
              refine ⟨7503154388705007313184323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40016823406426705670316389 7503154388705007313184323)
              ·
                refine ⟨11254731583057510969776485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7503154388705007313184323 11254731583057510969776485)
                ·
                  refine ⟨2110262171823283306833091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11254731583057510969776485 2110262171823283306833091)
                  ·
                    refine ⟨3165393257734924960249637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110262171823283306833091 3165393257734924960249637)
                    ·
                      refine ⟨593511235825298430046807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3165393257734924960249637 593511235825298430046807)
                      ·
                        rfl

theorem cell23_1155859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_1155859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155859 prefixEnd_1155859 := by exact prefixLift 1155859
  have htrace : WordTrace (prefixWord ++ tailWord_1155859) baseStart_1155859 baseEnd_1155859 := by
    simpa [prefixWord, tailWord_1155859, baseEnd_1155859] using wordTrace_append hprefix tailTrace_1155859
  have hstable : (prefixWord ++ tailWord_1155859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155859).length < 2 ^ (prefixWord ++ tailWord_1155859).sum := by decide
  have hdescent : baseEnd_1155859 < baseStart_1155859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155889 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1155889 : Nat := 118140960795 + 1155889 * 2 ^ 59
def prefixEnd_1155889 : Nat := 4983230072969 + 3 ^ 40 * 1155889 * 2
def baseEnd_1155889 : Nat := 593526640244933312671669

theorem tailTrace_1155889 : CollatzResearch.WordTrace tailWord_1155889 prefixEnd_1155889 593526640244933312671669 := by
  unfold tailWord_1155889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42158735309419037969686721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28105823539612691979791147 42158735309419037969686721)
  ·
    refine ⟨31619051482064278477265041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42158735309419037969686721 31619051482064278477265041)
    ·
      refine ⟨23714288611548208857948781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31619051482064278477265041 23714288611548208857948781)
      ·
        refine ⟨8892858229330578321730793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23714288611548208857948781 8892858229330578321730793)
        ·
          refine ⟨6669643671997933741298095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8892858229330578321730793 6669643671997933741298095)
          ·
            refine ⟨10004465507996900611947143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6669643671997933741298095 10004465507996900611947143)
            ·
              refine ⟨15006698261995350917920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10004465507996900611947143 15006698261995350917920715)
              ·
                refine ⟨22510047392993026376881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15006698261995350917920715 22510047392993026376881073)
                ·
                  refine ⟨16882535544744769782660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22510047392993026376881073 16882535544744769782660805)
                  ·
                    refine ⟨3165475414639644334248901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16882535544744769782660805 3165475414639644334248901)
                    ·
                      refine ⟨593526640244933312671669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3165475414639644334248901 593526640244933312671669)
                      ·
                        rfl

theorem cell23_1155889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1155889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155889 prefixEnd_1155889 := by exact prefixLift 1155889
  have htrace : WordTrace (prefixWord ++ tailWord_1155889) baseStart_1155889 baseEnd_1155889 := by
    simpa [prefixWord, tailWord_1155889, baseEnd_1155889] using wordTrace_append hprefix tailTrace_1155889
  have hstable : (prefixWord ++ tailWord_1155889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155889).length < 2 ^ (prefixWord ++ tailWord_1155889).sum := by decide
  have hdescent : baseEnd_1155889 < baseStart_1155889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155896 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1155896 : Nat := 118140960795 + 1155896 * 2 ^ 59
def prefixEnd_1155896 : Nat := 4983230072969 + 3 ^ 40 * 1155896 * 2
def baseEnd_1155896 : Nat := 593530234609514785284137

theorem tailTrace_1155896 : CollatzResearch.WordTrace tailWord_1155896 prefixEnd_1155896 593530234609514785284137 := by
  unfold tailWord_1155896
  simp only [CollatzResearch.WordTrace]
  refine ⟨21079495310196839082595771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28105993746929118776794361 21079495310196839082595771)
  ·
    refine ⟨31619242965295258623893657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21079495310196839082595771 31619242965295258623893657)
    ·
      refine ⟨23714432223971443967920243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31619242965295258623893657 23714432223971443967920243)
      ·
        refine ⟨35571648335957165951880365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23714432223971443967920243 35571648335957165951880365)
        ·
          refine ⟨13339368125983937231955137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35571648335957165951880365 13339368125983937231955137)
          ·
            refine ⟨10004526094487952923966353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13339368125983937231955137 10004526094487952923966353)
            ·
              refine ⟨7503394570865964692974765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10004526094487952923966353 7503394570865964692974765)
              ·
                refine ⟨2813772964074736759865537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7503394570865964692974765 2813772964074736759865537)
                ·
                  refine ⟨2110329723056052569899153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2813772964074736759865537 2110329723056052569899153)
                  ·
                    refine ⟨1582747292292039427424365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110329723056052569899153 1582747292292039427424365)
                    ·
                      refine ⟨593530234609514785284137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582747292292039427424365 593530234609514785284137)
                      ·
                        rfl

theorem cell23_1155896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1155896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155896 prefixEnd_1155896 := by exact prefixLift 1155896
  have htrace : WordTrace (prefixWord ++ tailWord_1155896) baseStart_1155896 baseEnd_1155896 := by
    simpa [prefixWord, tailWord_1155896, baseEnd_1155896] using wordTrace_append hprefix tailTrace_1155896
  have hstable : (prefixWord ++ tailWord_1155896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155896).length < 2 ^ (prefixWord ++ tailWord_1155896).sum := by decide
  have hdescent : baseEnd_1155896 < baseStart_1155896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155953 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_1155953 : Nat := 118140960795 + 1155953 * 2 ^ 59
def prefixEnd_1155953 : Nat := 4983230072969 + 3 ^ 40 * 1155953 * 2
def baseEnd_1155953 : Nat := 593559503006821062271375

theorem tailTrace_1155953 : CollatzResearch.WordTrace tailWord_1155953 prefixEnd_1155953 593559503006821062271375 := by
  unfold tailWord_1155953
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161069581187176900016513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28107379720791451266677675 42161069581187176900016513)
  ·
    refine ⟨31620802185890382675012385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42161069581187176900016513 31620802185890382675012385)
    ·
      refine ⟨23715601639417787006259289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31620802185890382675012385 23715601639417787006259289)
      ·
        refine ⟨17786701229563340254694467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23715601639417787006259289 17786701229563340254694467)
        ·
          refine ⟨26680051844345010382041701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786701229563340254694467 26680051844345010382041701)
          ·
            refine ⟨5002509720814689446632819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26680051844345010382041701 5002509720814689446632819)
            ·
              refine ⟨7503764581222034169949229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5002509720814689446632819 7503764581222034169949229)
              ·
                refine ⟨2813911717958262813730961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7503764581222034169949229 2813911717958262813730961)
                ·
                  refine ⟨2110433788468697110298221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2813911717958262813730961 2110433788468697110298221)
                  ·
                    refine ⟨791412670675761416361833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110433788468697110298221 791412670675761416361833)
                    ·
                      refine ⟨593559503006821062271375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791412670675761416361833 593559503006821062271375)
                      ·
                        rfl

theorem cell23_1155953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_1155953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155953 prefixEnd_1155953 := by exact prefixLift 1155953
  have htrace : WordTrace (prefixWord ++ tailWord_1155953) baseStart_1155953 baseEnd_1155953 := by
    simpa [prefixWord, tailWord_1155953, baseEnd_1155953] using wordTrace_append hprefix tailTrace_1155953
  have hstable : (prefixWord ++ tailWord_1155953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155953).length < 2 ^ (prefixWord ++ tailWord_1155953).sum := by decide
  have hdescent : baseEnd_1155953 < baseStart_1155953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155977 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 1, 1, 3]
def baseStart_1155977 : Nat := 118140960795 + 1155977 * 2 ^ 59
def prefixEnd_1155977 : Nat := 4983230072969 + 3 ^ 40 * 1155977 * 2
def baseEnd_1155977 : Nat := 593571826542528968371265

theorem tailTrace_1155977 : CollatzResearch.WordTrace tailWord_1155977 prefixEnd_1155977 593571826542528968371265 := by
  unfold tailWord_1155977
  simp only [CollatzResearch.WordTrace]
  refine ⟨42161944933100228998890185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28107963288733485999260123 42161944933100228998890185)
  ·
    refine ⟨31621458699825171749167639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42161944933100228998890185 31621458699825171749167639)
    ·
      refine ⟨47432188049737757623751459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31621458699825171749167639 47432188049737757623751459)
      ·
        refine ⟨71148282074606636435627189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47432188049737757623751459 71148282074606636435627189)
        ·
          refine ⟨6670151444494372165840049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71148282074606636435627189 6670151444494372165840049)
          ·
            refine ⟨5002613583370779124380037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6670151444494372165840049 5002613583370779124380037)
            ·
              refine ⟨937990046882021085821257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5002613583370779124380037 937990046882021085821257)
              ·
                refine ⟨703492535161515814365943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937990046882021085821257 703492535161515814365943)
                ·
                  refine ⟨1055238802742273721548915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703492535161515814365943 1055238802742273721548915)
                  ·
                    refine ⟨1582858204113410582323373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1055238802742273721548915 1582858204113410582323373)
                    ·
                      refine ⟨593571826542528968371265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582858204113410582323373 593571826542528968371265)
                      ·
                        rfl

theorem cell23_1155977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 1, 3].length) (baseStart_1155977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155977 prefixEnd_1155977 := by exact prefixLift 1155977
  have htrace : WordTrace (prefixWord ++ tailWord_1155977) baseStart_1155977 baseEnd_1155977 := by
    simpa [prefixWord, tailWord_1155977, baseEnd_1155977] using wordTrace_append hprefix tailTrace_1155977
  have hstable : (prefixWord ++ tailWord_1155977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155977).length < 2 ^ (prefixWord ++ tailWord_1155977).sum := by decide
  have hdescent : baseEnd_1155977 < baseStart_1155977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155979 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_1155979 : Nat := 118140960795 + 1155979 * 2 ^ 59
def prefixEnd_1155979 : Nat := 4983230072969 + 3 ^ 40 * 1155979 * 2
def baseEnd_1155979 : Nat := 593572853503837960546255

theorem tailTrace_1155979 : CollatzResearch.WordTrace tailWord_1155979 prefixEnd_1155979 593572853503837960546255 := by
  unfold tailWord_1155979
  simp only [CollatzResearch.WordTrace]
  refine ⟨42162017879092983340462991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28108011919395322226975327 42162017879092983340462991)
  ·
    refine ⟨63243026818639475010694487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42162017879092983340462991 63243026818639475010694487)
    ·
      refine ⟨94864540227959212516041731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63243026818639475010694487 94864540227959212516041731)
      ·
        refine ⟨142296810341938818774062597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94864540227959212516041731 142296810341938818774062597)
        ·
          refine ⟨26680651939113528520136737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142296810341938818774062597 26680651939113528520136737)
          ·
            refine ⟨20010488954335146390102553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26680651939113528520136737 20010488954335146390102553)
            ·
              refine ⟨15007866715751359792576915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20010488954335146390102553 15007866715751359792576915)
              ·
                refine ⟨22511800073627039688865373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15007866715751359792576915 22511800073627039688865373)
                ·
                  refine ⟨8441925027610139883324515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22511800073627039688865373 8441925027610139883324515)
                  ·
                    refine ⟨12662887541415209824986773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8441925027610139883324515 12662887541415209824986773)
                    ·
                      refine ⟨593572853503837960546255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12662887541415209824986773 593572853503837960546255)
                      ·
                        rfl

theorem cell23_1155979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_1155979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1155979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1155979 prefixEnd_1155979 := by exact prefixLift 1155979
  have htrace : WordTrace (prefixWord ++ tailWord_1155979) baseStart_1155979 baseEnd_1155979 := by
    simpa [prefixWord, tailWord_1155979, baseEnd_1155979] using wordTrace_append hprefix tailTrace_1155979
  have hstable : (prefixWord ++ tailWord_1155979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155979).length < 2 ^ (prefixWord ++ tailWord_1155979).sum := by decide
  have hdescent : baseEnd_1155979 < baseStart_1155979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156017 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1156017 : Nat := 118140960795 + 1156017 * 2 ^ 59
def prefixEnd_1156017 : Nat := 4983230072969 + 3 ^ 40 * 1156017 * 2
def baseEnd_1156017 : Nat := 593592365768708811871081

theorem tailTrace_1156017 : CollatzResearch.WordTrace tailWord_1156017 prefixEnd_1156017 593592365768708811871081 := by
  unfold tailWord_1156017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42163403852955315830346305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28108935901970210553564203 42163403852955315830346305)
  ·
    refine ⟨31622552889716486872759729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42163403852955315830346305 31622552889716486872759729)
    ·
      refine ⟨23716914667287365154569797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31622552889716486872759729 23716914667287365154569797)
      ·
        refine ⟨4446921500116380966481837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23716914667287365154569797 4446921500116380966481837)
        ·
          refine ⟨1667595562543642862430689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4446921500116380966481837 1667595562543642862430689)
          ·
            refine ⟨1250696671907732146823017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667595562543642862430689 1250696671907732146823017)
            ·
              refine ⟨938022503930799110117263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250696671907732146823017 938022503930799110117263)
              ·
                refine ⟨1407033755896198665175895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938022503930799110117263 1407033755896198665175895)
                ·
                  refine ⟨2110550633844297997763843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407033755896198665175895 2110550633844297997763843)
                  ·
                    refine ⟨3165825950766446996645765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110550633844297997763843 3165825950766446996645765)
                    ·
                      refine ⟨593592365768708811871081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3165825950766446996645765 593592365768708811871081)
                      ·
                        rfl

theorem cell23_1156017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1156017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156017 prefixEnd_1156017 := by exact prefixLift 1156017
  have htrace : WordTrace (prefixWord ++ tailWord_1156017) baseStart_1156017 baseEnd_1156017 := by
    simpa [prefixWord, tailWord_1156017, baseEnd_1156017] using wordTrace_append hprefix tailTrace_1156017
  have hstable : (prefixWord ++ tailWord_1156017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156017).length < 2 ^ (prefixWord ++ tailWord_1156017).sum := by decide
  have hdescent : baseEnd_1156017 < baseStart_1156017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156019 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 9]
def baseStart_1156019 : Nat := 118140960795 + 1156019 * 2 ^ 59
def prefixEnd_1156019 : Nat := 4983230072969 + 3 ^ 40 * 1156019 * 2
def baseEnd_1156019 : Nat := 197864464243339268015357

theorem tailTrace_1156019 : CollatzResearch.WordTrace tailWord_1156019 prefixEnd_1156019 197864464243339268015357 := by
  unfold tailWord_1156019
  simp only [CollatzResearch.WordTrace]
  refine ⟨42163476798948070171919111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28108984532632046781279407 42163476798948070171919111)
  ·
    refine ⟨63245215198422105257878667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42163476798948070171919111 63245215198422105257878667)
    ·
      refine ⟨94867822797633157886818001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63245215198422105257878667 94867822797633157886818001)
      ·
        refine ⟨71150867098224868415113501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94867822797633157886818001 71150867098224868415113501)
        ·
          refine ⟨26681575161834325655667563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71150867098224868415113501 26681575161834325655667563)
          ·
            refine ⟨40022362742751488483501345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26681575161834325655667563 40022362742751488483501345)
            ·
              refine ⟨30016772057063616362626009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40022362742751488483501345 30016772057063616362626009)
              ·
                refine ⟨22512579042797712271969507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30016772057063616362626009 22512579042797712271969507)
                ·
                  refine ⟨33768868564196568407954261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22512579042797712271969507 33768868564196568407954261)
                  ·
                    refine ⟨197864464243339268015357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33768868564196568407954261 197864464243339268015357)
                    ·
                      rfl

theorem cell23_1156019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_1156019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156019 prefixEnd_1156019 := by exact prefixLift 1156019
  have htrace : WordTrace (prefixWord ++ tailWord_1156019) baseStart_1156019 baseEnd_1156019 := by
    simpa [prefixWord, tailWord_1156019, baseEnd_1156019] using wordTrace_append hprefix tailTrace_1156019
  have hstable : (prefixWord ++ tailWord_1156019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156019).length < 2 ^ (prefixWord ++ tailWord_1156019).sum := by decide
  have hdescent : baseEnd_1156019 < baseStart_1156019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156050 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1156050 : Nat := 118140960795 + 1156050 * 2 ^ 59
def prefixEnd_1156050 : Nat := 4983230072969 + 3 ^ 40 * 1156050 * 2
def baseEnd_1156050 : Nat := 593609310630307182758429

theorem tailTrace_1156050 : CollatzResearch.WordTrace tailWord_1156050 prefixEnd_1156050 593609310630307182758429 := by
  unfold tailWord_1156050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10541151865458940616574401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28109738307890508310865069 10541151865458940616574401)
  ·
    refine ⟨7905863899094205462430801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10541151865458940616574401 7905863899094205462430801)
    ·
      refine ⟨5929397924320654096823101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7905863899094205462430801 5929397924320654096823101)
      ·
        refine ⟨2223524221620245286308663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5929397924320654096823101 2223524221620245286308663)
        ·
          refine ⟨3335286332430367929462995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223524221620245286308663 3335286332430367929462995)
          ·
            refine ⟨5002929498645551894194493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335286332430367929462995 5002929498645551894194493)
            ·
              refine ⟨1876098561992081960322935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5002929498645551894194493 1876098561992081960322935)
              ·
                refine ⟨2814147842988122940484403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876098561992081960322935 2814147842988122940484403)
                ·
                  refine ⟨4221221764482184410726605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814147842988122940484403 4221221764482184410726605)
                  ·
                    refine ⟨1582958161680819154022477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4221221764482184410726605 1582958161680819154022477)
                    ·
                      refine ⟨593609310630307182758429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582958161680819154022477 593609310630307182758429)
                      ·
                        rfl

theorem cell23_1156050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1156050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156050 prefixEnd_1156050 := by exact prefixLift 1156050
  have htrace : WordTrace (prefixWord ++ tailWord_1156050) baseStart_1156050 baseEnd_1156050 := by
    simpa [prefixWord, tailWord_1156050, baseEnd_1156050] using wordTrace_append hprefix tailTrace_1156050
  have hstable : (prefixWord ++ tailWord_1156050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156050).length < 2 ^ (prefixWord ++ tailWord_1156050).sum := by decide
  have hdescent : baseEnd_1156050 < baseStart_1156050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156076 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_1156076 : Nat := 118140960795 + 1156076 * 2 ^ 59
def prefixEnd_1156076 : Nat := 4983230072969 + 3 ^ 40 * 1156076 * 2
def baseEnd_1156076 : Nat := 593622661127324081033309

theorem tailTrace_1156076 : CollatzResearch.WordTrace tailWord_1156076 prefixEnd_1156076 593622661127324081033309 := by
  unfold tailWord_1156076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082777879870784453372041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28110370506494379271162721 21082777879870784453372041)
  ·
    refine ⟨15812083409903088340029031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21082777879870784453372041 15812083409903088340029031)
    ·
      refine ⟨23718125114854632510043547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15812083409903088340029031 23718125114854632510043547)
      ·
        refine ⟨35577187672281948765065321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23718125114854632510043547 35577187672281948765065321)
        ·
          refine ⟨26682890754211461573798991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35577187672281948765065321 26682890754211461573798991)
          ·
            refine ⟨40024336131317192360698487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26682890754211461573798991 40024336131317192360698487)
            ·
              refine ⟨60036504196975788541047731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40024336131317192360698487 60036504196975788541047731)
              ·
                refine ⟨90054756295463682811571597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60036504196975788541047731 90054756295463682811571597)
                ·
                  refine ⟨33770533610798881054339349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90054756295463682811571597 33770533610798881054339349)
                  ·
                    refine ⟨1582993763006197549422157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33770533610798881054339349 1582993763006197549422157)
                    ·
                      refine ⟨593622661127324081033309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1582993763006197549422157 593622661127324081033309)
                      ·
                        rfl

theorem cell23_1156076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_1156076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156076 prefixEnd_1156076 := by exact prefixLift 1156076
  have htrace : WordTrace (prefixWord ++ tailWord_1156076) baseStart_1156076 baseEnd_1156076 := by
    simpa [prefixWord, tailWord_1156076, baseEnd_1156076] using wordTrace_append hprefix tailTrace_1156076
  have hstable : (prefixWord ++ tailWord_1156076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156076).length < 2 ^ (prefixWord ++ tailWord_1156076).sum := by decide
  have hdescent : baseEnd_1156076 < baseStart_1156076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156107 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 2, 2, 2]
def baseStart_1156107 : Nat := 118140960795 + 1156107 * 2 ^ 59
def prefixEnd_1156107 : Nat := 4983230072969 + 3 ^ 40 * 1156107 * 2
def baseEnd_1156107 : Nat := 593638579027613459745667

theorem tailTrace_1156107 : CollatzResearch.WordTrace tailWord_1156107 prefixEnd_1156107 593638579027613459745667 := by
  unfold tailWord_1156107
  simp only [CollatzResearch.WordTrace]
  refine ⟨42166686422629261201122575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28111124281752840800748383 42166686422629261201122575)
  ·
    refine ⟨63250029633943891801683863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42166686422629261201122575 63250029633943891801683863)
    ·
      refine ⟨94875044450915837702525795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63250029633943891801683863 94875044450915837702525795)
      ·
        refine ⟨142312566676373756553788693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94875044450915837702525795 142312566676373756553788693)
        ·
          refine ⟨6670901562955019838458845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142312566676373756553788693 6670901562955019838458845)
          ·
            refine ⟨2501588086108132439422067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6670901562955019838458845 2501588086108132439422067)
            ·
              refine ⟨3752382129162198659133101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501588086108132439422067 3752382129162198659133101)
              ·
                refine ⟨1407143298435824497174913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3752382129162198659133101 1407143298435824497174913)
                ·
                  refine ⟨1055357473826868372881185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1407143298435824497174913 1055357473826868372881185)
                  ·
                    refine ⟨791518105370151279660889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055357473826868372881185 791518105370151279660889)
                    ·
                      refine ⟨593638579027613459745667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791518105370151279660889 593638579027613459745667)
                      ·
                        rfl

theorem cell23_1156107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 2, 2].length) (baseStart_1156107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156107 prefixEnd_1156107 := by exact prefixLift 1156107
  have htrace : WordTrace (prefixWord ++ tailWord_1156107) baseStart_1156107 baseEnd_1156107 := by
    simpa [prefixWord, tailWord_1156107, baseEnd_1156107] using wordTrace_append hprefix tailTrace_1156107
  have hstable : (prefixWord ++ tailWord_1156107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156107).length < 2 ^ (prefixWord ++ tailWord_1156107).sum := by decide
  have hdescent : baseEnd_1156107 < baseStart_1156107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156153 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1156153 : Nat := 118140960795 + 1156153 * 2 ^ 59
def prefixEnd_1156153 : Nat := 4983230072969 + 3 ^ 40 * 1156153 * 2
def baseEnd_1156153 : Nat := 593662199137720279770455

theorem tailTrace_1156153 : CollatzResearch.WordTrace tailWord_1156153 prefixEnd_1156153 593662199137720279770455 := by
  unfold tailWord_1156153
  simp only [CollatzResearch.WordTrace]
  refine ⟨42168364180462611057297113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28112242786975074038198075 42168364180462611057297113)
  ·
    refine ⟨31626273135346958292972835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42168364180462611057297113 31626273135346958292972835)
    ·
      refine ⟨47439409703020437439459253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31626273135346958292972835 47439409703020437439459253)
      ·
        refine ⟨4447444659658166009949305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47439409703020437439459253 4447444659658166009949305)
        ·
          refine ⟨3335583494743624507461979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447444659658166009949305 3335583494743624507461979)
          ·
            refine ⟨5003375242115436761192969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335583494743624507461979 5003375242115436761192969)
            ·
              refine ⟨3752531431586577570894727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003375242115436761192969 3752531431586577570894727)
              ·
                refine ⟨5628797147379866356342091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752531431586577570894727 5628797147379866356342091)
                ·
                  refine ⟨8443195721069799534513137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5628797147379866356342091 8443195721069799534513137)
                  ·
                    refine ⟨6332396790802349650884853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8443195721069799534513137 6332396790802349650884853)
                    ·
                      refine ⟨593662199137720279770455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6332396790802349650884853 593662199137720279770455)
                      ·
                        rfl

theorem cell23_1156153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1156153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156153 prefixEnd_1156153 := by exact prefixLift 1156153
  have htrace : WordTrace (prefixWord ++ tailWord_1156153) baseStart_1156153 baseEnd_1156153 := by
    simpa [prefixWord, tailWord_1156153, baseEnd_1156153] using wordTrace_append hprefix tailTrace_1156153
  have hstable : (prefixWord ++ tailWord_1156153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156153).length < 2 ^ (prefixWord ++ tailWord_1156153).sum := by decide
  have hdescent : baseEnd_1156153 < baseStart_1156153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156176 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1156176 : Nat := 118140960795 + 1156176 * 2 ^ 59
def prefixEnd_1156176 : Nat := 4983230072969 + 3 ^ 40 * 1156176 * 2
def baseEnd_1156176 : Nat := 593674009192773689782849

theorem tailTrace_1156176 : CollatzResearch.WordTrace tailWord_1156176 prefixEnd_1156176 593674009192773689782849 := by
  unfold tailWord_1156176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21084601529689642992692191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28112802039586190656922921 21084601529689642992692191)
  ·
    refine ⟨31626902294534464489038287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21084601529689642992692191 31626902294534464489038287)
    ·
      refine ⟨47440353441801696733557431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31626902294534464489038287 47440353441801696733557431)
      ·
        refine ⟨71160530162702545100336147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47440353441801696733557431 71160530162702545100336147)
        ·
          refine ⟨106740795244053817650504221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71160530162702545100336147 106740795244053817650504221)
          ·
            refine ⟨40027798216520181618939083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106740795244053817650504221 40027798216520181618939083)
            ·
              refine ⟨60041697324780272428408625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40027798216520181618939083 60041697324780272428408625)
              ·
                refine ⟨45031272993585204321306469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60041697324780272428408625 45031272993585204321306469)
                ·
                  refine ⟨8443363686297225810244963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45031272993585204321306469 8443363686297225810244963)
                  ·
                    refine ⟨12665045529445838715367445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8443363686297225810244963 12665045529445838715367445)
                    ·
                      refine ⟨593674009192773689782849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12665045529445838715367445 593674009192773689782849)
                      ·
                        rfl

theorem cell23_1156176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1156176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156176 prefixEnd_1156176 := by exact prefixLift 1156176
  have htrace : WordTrace (prefixWord ++ tailWord_1156176) baseStart_1156176 baseEnd_1156176 := by
    simpa [prefixWord, tailWord_1156176, baseEnd_1156176] using wordTrace_append hprefix tailTrace_1156176
  have hstable : (prefixWord ++ tailWord_1156176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156176).length < 2 ^ (prefixWord ++ tailWord_1156176).sum := by decide
  have hdescent : baseEnd_1156176 < baseStart_1156176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156180 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1156180 : Nat := 118140960795 + 1156180 * 2 ^ 59
def prefixEnd_1156180 : Nat := 4983230072969 + 3 ^ 40 * 1156180 * 2
def baseEnd_1156180 : Nat := 593676063115391674132831

theorem tailTrace_1156180 : CollatzResearch.WordTrace tailWord_1156180 prefixEnd_1156180 593676063115391674132831 := by
  unfold tailWord_1156180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21084674475682397334264997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28112899300909863112353329 21084674475682397334264997)
  ·
    refine ⟨3953376464190449500174687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21084674475682397334264997 3953376464190449500174687)
    ·
      refine ⟨5930064696285674250262031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953376464190449500174687 5930064696285674250262031)
      ·
        refine ⟨8895097044428511375393047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930064696285674250262031 8895097044428511375393047)
        ·
          refine ⟨13342645566642767063089571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8895097044428511375393047 13342645566642767063089571)
          ·
            refine ⟨20013968349964150594634357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13342645566642767063089571 20013968349964150594634357)
            ·
              refine ⟨1876309532809139118246971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20013968349964150594634357 1876309532809139118246971)
              ·
                refine ⟨2814464299213708677370457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876309532809139118246971 2814464299213708677370457)
                ·
                  refine ⟨2110848224410281508027843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814464299213708677370457 2110848224410281508027843)
                  ·
                    refine ⟨3166272336615422262041765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110848224410281508027843 3166272336615422262041765)
                    ·
                      refine ⟨593676063115391674132831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3166272336615422262041765 593676063115391674132831)
                      ·
                        rfl

theorem cell23_1156180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1156180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156180 prefixEnd_1156180 := by exact prefixLift 1156180
  have htrace : WordTrace (prefixWord ++ tailWord_1156180) baseStart_1156180 baseEnd_1156180 := by
    simpa [prefixWord, tailWord_1156180, baseEnd_1156180] using wordTrace_append hprefix tailTrace_1156180
  have hstable : (prefixWord ++ tailWord_1156180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156180).length < 2 ^ (prefixWord ++ tailWord_1156180).sum := by decide
  have hdescent : baseEnd_1156180 < baseStart_1156180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156220 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 6]
def baseStart_1156220 : Nat := 118140960795 + 1156220 * 2 ^ 59
def prefixEnd_1156220 : Nat := 4983230072969 + 3 ^ 40 * 1156220 * 2
def baseEnd_1156220 : Nat := 65966289149063501959183

theorem tailTrace_1156220 : CollatzResearch.WordTrace tailWord_1156220 prefixEnd_1156220 65966289149063501959183 := by
  unfold tailWord_1156220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085403935609940749993057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28113871914146587666657409 21085403935609940749993057)
  ·
    refine ⟨15814052951707455562494793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21085403935609940749993057 15814052951707455562494793)
    ·
      refine ⟨11860539713780591671871095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15814052951707455562494793 11860539713780591671871095)
      ·
        refine ⟨17790809570670887507806643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860539713780591671871095 17790809570670887507806643)
        ·
          refine ⟨26686214356006331261709965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17790809570670887507806643 26686214356006331261709965)
          ·
            refine ⟨10007330383502374223141237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26686214356006331261709965 10007330383502374223141237)
            ·
              refine ⟨938187223453347583419491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10007330383502374223141237 938187223453347583419491)
              ·
                refine ⟨1407280835180021375129237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938187223453347583419491 1407280835180021375129237)
                ·
                  refine ⟨65966289149063501959183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1407280835180021375129237 65966289149063501959183)
                  ·
                    rfl

theorem cell23_1156220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_1156220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156220 prefixEnd_1156220 := by exact prefixLift 1156220
  have htrace : WordTrace (prefixWord ++ tailWord_1156220) baseStart_1156220 baseEnd_1156220 := by
    simpa [prefixWord, tailWord_1156220, baseEnd_1156220] using wordTrace_append hprefix tailTrace_1156220
  have hstable : (prefixWord ++ tailWord_1156220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156220).length < 2 ^ (prefixWord ++ tailWord_1156220).sum := by decide
  have hdescent : baseEnd_1156220 < baseStart_1156220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156257 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1156257 : Nat := 118140960795 + 1156257 * 2 ^ 59
def prefixEnd_1156257 : Nat := 4983230072969 + 3 ^ 40 * 1156257 * 2
def baseEnd_1156257 : Nat := 593715601125787872869977

theorem tailTrace_1156257 : CollatzResearch.WordTrace tailWord_1156257 prefixEnd_1156257 593715601125787872869977 := by
  unfold tailWord_1156257
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172157372085836819083025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28114771581390557879388683 42172157372085836819083025)
  ·
    refine ⟨31629118029064377614312269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42172157372085836819083025 31629118029064377614312269)
    ·
      refine ⟨11860919260899141605367101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31629118029064377614312269 11860919260899141605367101)
      ·
        refine ⟨4447844722837178102012663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11860919260899141605367101 4447844722837178102012663)
        ·
          refine ⟨6671767084255767153018995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447844722837178102012663 6671767084255767153018995)
          ·
            refine ⟨10007650626383650729528493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671767084255767153018995 10007650626383650729528493)
            ·
              refine ⟨3752868984893869023573185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10007650626383650729528493 3752868984893869023573185)
              ·
                refine ⟨2814651738670401767679889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752868984893869023573185 2814651738670401767679889)
                ·
                  refine ⟨2110988804002801325759917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814651738670401767679889 2110988804002801325759917)
                  ·
                    refine ⟨791620801501050497159969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110988804002801325759917 791620801501050497159969)
                    ·
                      refine ⟨593715601125787872869977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791620801501050497159969 593715601125787872869977)
                      ·
                        rfl

theorem cell23_1156257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1156257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156257 prefixEnd_1156257 := by exact prefixLift 1156257
  have htrace : WordTrace (prefixWord ++ tailWord_1156257) baseStart_1156257 baseEnd_1156257 := by
    simpa [prefixWord, tailWord_1156257, baseEnd_1156257] using wordTrace_append hprefix tailTrace_1156257
  have hstable : (prefixWord ++ tailWord_1156257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156257).length < 2 ^ (prefixWord ++ tailWord_1156257).sum := by decide
  have hdescent : baseEnd_1156257 < baseStart_1156257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156287 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 3, 2, 2]
def baseStart_1156287 : Nat := 118140960795 + 1156287 * 2 ^ 59
def prefixEnd_1156287 : Nat := 4983230072969 + 3 ^ 40 * 1156287 * 2
def baseEnd_1156287 : Nat := 593731005545422755494839

theorem tailTrace_1156287 : CollatzResearch.WordTrace tailWord_1156287 prefixEnd_1156287 593731005545422755494839 := by
  unfold tailWord_1156287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42173251561977151942675115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28115501041318101295116743 42173251561977151942675115)
  ·
    refine ⟨63259877342965727914012673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42173251561977151942675115 63259877342965727914012673)
    ·
      refine ⟨47444908007224295935509505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63259877342965727914012673 47444908007224295935509505)
      ·
        refine ⟨35583681005418221951632129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47444908007224295935509505 35583681005418221951632129)
        ·
          refine ⟨26687760754063666463724097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35583681005418221951632129 26687760754063666463724097)
          ·
            refine ⟨20015820565547749847793073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26687760754063666463724097 20015820565547749847793073)
            ·
              refine ⟨15011865424160812385844805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20015820565547749847793073 15011865424160812385844805)
              ·
                refine ⟨2814724767030152322345901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15011865424160812385844805 2814724767030152322345901)
                ·
                  refine ⟨1055521787636307120879713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2814724767030152322345901 1055521787636307120879713)
                  ·
                    refine ⟨791641340727230340659785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055521787636307120879713 791641340727230340659785)
                    ·
                      refine ⟨593731005545422755494839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791641340727230340659785 593731005545422755494839)
                      ·
                        rfl

theorem cell23_1156287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_1156287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156287 prefixEnd_1156287 := by exact prefixLift 1156287
  have htrace : WordTrace (prefixWord ++ tailWord_1156287) baseStart_1156287 baseEnd_1156287 := by
    simpa [prefixWord, tailWord_1156287, baseEnd_1156287] using wordTrace_append hprefix tailTrace_1156287
  have hstable : (prefixWord ++ tailWord_1156287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156287).length < 2 ^ (prefixWord ++ tailWord_1156287).sum := by decide
  have hdescent : baseEnd_1156287 < baseStart_1156287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156310 : List Nat := [5, 2, 1, 2, 13]
def baseStart_1156310 : Nat := 118140960795 + 1156310 * 2 ^ 59
def prefixEnd_1156310 : Nat := 4983230072969 + 3 ^ 40 * 1156310 * 2
def baseEnd_1156310 : Nat := 814462024143314355977

theorem tailTrace_1156310 : CollatzResearch.WordTrace tailWord_1156310 prefixEnd_1156310 814462024143314355977 := by
  unfold tailWord_1156310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635880652555864179422649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28116060293929217913841589 2635880652555864179422649)
  ·
    refine ⟨1976910489416898134566987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635880652555864179422649 1976910489416898134566987)
    ·
      refine ⟨2965365734125347201850481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976910489416898134566987 2965365734125347201850481)
      ·
        refine ⟨2224024300594010401387861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965365734125347201850481 2224024300594010401387861)
        ·
          refine ⟨814462024143314355977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2224024300594010401387861 814462024143314355977)
          ·
            rfl

theorem cell23_1156310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 13].length) (baseStart_1156310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156310 prefixEnd_1156310 := by exact prefixLift 1156310
  have htrace : WordTrace (prefixWord ++ tailWord_1156310) baseStart_1156310 baseEnd_1156310 := by
    simpa [prefixWord, tailWord_1156310, baseEnd_1156310] using wordTrace_append hprefix tailTrace_1156310
  have hstable : (prefixWord ++ tailWord_1156310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156310).length < 2 ^ (prefixWord ++ tailWord_1156310).sum := by decide
  have hdescent : baseEnd_1156310 < baseStart_1156310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156321 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_1156321 : Nat := 118140960795 + 1156321 * 2 ^ 59
def prefixEnd_1156321 : Nat := 4983230072969 + 3 ^ 40 * 1156321 * 2
def baseEnd_1156321 : Nat := 593748463887675622469683

theorem tailTrace_1156321 : CollatzResearch.WordTrace tailWord_1156321 prefixEnd_1156321 593748463887675622469683 := by
  unfold tailWord_1156321
  simp only [CollatzResearch.WordTrace]
  refine ⟨42174491643853975749412817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28116327762569317166275211 42174491643853975749412817)
  ·
    refine ⟨31630868732890481812059613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42174491643853975749412817 31630868732890481812059613)
    ·
      refine ⟨11861575774833930679522355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31630868732890481812059613 11861575774833930679522355)
      ·
        refine ⟨17792363662250896019283533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861575774833930679522355 17792363662250896019283533)
        ·
          refine ⟨6672136373344086007231325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17792363662250896019283533 6672136373344086007231325)
          ·
            refine ⟨2502051140004032252711747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6672136373344086007231325 2502051140004032252711747)
            ·
              refine ⟨3753076710006048379067621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502051140004032252711747 3753076710006048379067621)
              ·
                refine ⟨703701883126134071075179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3753076710006048379067621 703701883126134071075179)
                ·
                  refine ⟨1055552824689201106612769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703701883126134071075179 1055552824689201106612769)
                  ·
                    refine ⟨791664618516900829959577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055552824689201106612769 791664618516900829959577)
                    ·
                      refine ⟨593748463887675622469683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791664618516900829959577 593748463887675622469683)
                      ·
                        rfl

theorem cell23_1156321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_1156321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156321 prefixEnd_1156321 := by exact prefixLift 1156321
  have htrace : WordTrace (prefixWord ++ tailWord_1156321) baseStart_1156321 baseEnd_1156321 := by
    simpa [prefixWord, tailWord_1156321, baseEnd_1156321] using wordTrace_append hprefix tailTrace_1156321
  have hstable : (prefixWord ++ tailWord_1156321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156321).length < 2 ^ (prefixWord ++ tailWord_1156321).sum := by decide
  have hdescent : baseEnd_1156321 < baseStart_1156321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156327 : List Nat := [1, 1, 5, 3, 2, 2, 1, 8]
def baseStart_1156327 : Nat := 118140960795 + 1156327 * 2 ^ 59
def prefixEnd_1156327 : Nat := 4983230072969 + 3 ^ 40 * 1156327 * 2
def baseEnd_1156327 : Nat := 21990797954503799962765

theorem tailTrace_1156327 : CollatzResearch.WordTrace tailWord_1156327 prefixEnd_1156327 21990797954503799962765 := by
  unfold tailWord_1156327
  simp only [CollatzResearch.WordTrace]
  refine ⟨42174710481832238774131235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28116473654554825849420823 42174710481832238774131235)
  ·
    refine ⟨63262065722748358161196853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42174710481832238774131235 63262065722748358161196853)
    ·
      refine ⟨5930818661507658577612205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63262065722748358161196853 5930818661507658577612205)
      ·
        refine ⟨2224056998065371966604577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5930818661507658577612205 2224056998065371966604577)
        ·
          refine ⟨1668042748549028974953433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224056998065371966604577 1668042748549028974953433)
          ·
            refine ⟨1251032061411771731215075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668042748549028974953433 1251032061411771731215075)
            ·
              refine ⟨1876548092117657596822613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251032061411771731215075 1876548092117657596822613)
              ·
                refine ⟨21990797954503799962765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1876548092117657596822613 21990797954503799962765)
                ·
                  rfl

theorem cell23_1156327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 8].length) (baseStart_1156327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156327 prefixEnd_1156327 := by exact prefixLift 1156327
  have htrace : WordTrace (prefixWord ++ tailWord_1156327) baseStart_1156327 baseEnd_1156327 := by
    simpa [prefixWord, tailWord_1156327, baseEnd_1156327] using wordTrace_append hprefix tailTrace_1156327
  have hstable : (prefixWord ++ tailWord_1156327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156327).length < 2 ^ (prefixWord ++ tailWord_1156327).sum := by decide
  have hdescent : baseEnd_1156327 < baseStart_1156327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156364 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_1156364 : Nat := 118140960795 + 1156364 * 2 ^ 59
def prefixEnd_1156364 : Nat := 4983230072969 + 3 ^ 40 * 1156364 * 2
def baseEnd_1156364 : Nat := 593770543555818954231985

theorem tailTrace_1156364 : CollatzResearch.WordTrace tailWord_1156364 prefixEnd_1156364 593770543555818954231985 := by
  unfold tailWord_1156364
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088029991349097046614073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28117373321798796062152097 21088029991349097046614073)
  ·
    refine ⟨15816022493511822784960555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21088029991349097046614073 15816022493511822784960555)
    ·
      refine ⟨23724033740267734177440833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15816022493511822784960555 23724033740267734177440833)
      ·
        refine ⟨17793025305200800633080625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23724033740267734177440833 17793025305200800633080625)
        ·
          refine ⟨13344768978900600474810469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17793025305200800633080625 13344768978900600474810469)
          ·
            refine ⟨2502144183543862589026963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13344768978900600474810469 2502144183543862589026963)
            ·
              refine ⟨3753216275315793883540445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502144183543862589026963 3753216275315793883540445)
              ·
                refine ⟨1407456103243422706327667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3753216275315793883540445 1407456103243422706327667)
                ·
                  refine ⟨2111184154865134059491501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407456103243422706327667 2111184154865134059491501)
                  ·
                    refine ⟨791694058074425272309313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111184154865134059491501 791694058074425272309313)
                    ·
                      refine ⟨593770543555818954231985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791694058074425272309313 593770543555818954231985)
                      ·
                        rfl

theorem cell23_1156364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_1156364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156364 prefixEnd_1156364 := by exact prefixLift 1156364
  have htrace : WordTrace (prefixWord ++ tailWord_1156364) baseStart_1156364 baseEnd_1156364 := by
    simpa [prefixWord, tailWord_1156364, baseEnd_1156364] using wordTrace_append hprefix tailTrace_1156364
  have hstable : (prefixWord ++ tailWord_1156364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156364).length < 2 ^ (prefixWord ++ tailWord_1156364).sum := by decide
  have hdescent : baseEnd_1156364 < baseStart_1156364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156380 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1156380 : Nat := 118140960795 + 1156380 * 2 ^ 59
def prefixEnd_1156380 : Nat := 4983230072969 + 3 ^ 40 * 1156380 * 2
def baseEnd_1156380 : Nat := 593778759246290891631911

theorem tailTrace_1156380 : CollatzResearch.WordTrace tailWord_1156380 prefixEnd_1156380 593778759246290891631911 := by
  unfold tailWord_1156380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088321775320114412905297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28117762367093485883873729 21088321775320114412905297)
  ·
    refine ⟨15816241331490085809678973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21088321775320114412905297 15816241331490085809678973)
    ·
      refine ⟨5931090499308782178629615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15816241331490085809678973 5931090499308782178629615)
      ·
        refine ⟨8896635748963173267944423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5931090499308782178629615 8896635748963173267944423)
        ·
          refine ⟨13344953623444759901916635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896635748963173267944423 13344953623444759901916635)
          ·
            refine ⟨20017430435167139852874953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13344953623444759901916635 20017430435167139852874953)
            ·
              refine ⟨15013072826375354889656215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20017430435167139852874953 15013072826375354889656215)
              ·
                refine ⟨22519609239563032334484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15013072826375354889656215 22519609239563032334484323)
                ·
                  refine ⟨33779413859344548501726485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22519609239563032334484323 33779413859344548501726485)
                  ·
                    refine ⟨1583410024656775711018429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33779413859344548501726485 1583410024656775711018429)
                    ·
                      refine ⟨593778759246290891631911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1583410024656775711018429 593778759246290891631911)
                      ·
                        rfl

theorem cell23_1156380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1156380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156380 prefixEnd_1156380 := by exact prefixLift 1156380
  have htrace : WordTrace (prefixWord ++ tailWord_1156380) baseStart_1156380 baseEnd_1156380 := by
    simpa [prefixWord, tailWord_1156380, baseEnd_1156380] using wordTrace_append hprefix tailTrace_1156380
  have hstable : (prefixWord ++ tailWord_1156380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156380).length < 2 ^ (prefixWord ++ tailWord_1156380).sum := by decide
  have hdescent : baseEnd_1156380 < baseStart_1156380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156440 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1156440 : Nat := 118140960795 + 1156440 * 2 ^ 59
def prefixEnd_1156440 : Nat := 4983230072969 + 3 ^ 40 * 1156440 * 2
def baseEnd_1156440 : Nat := 593809568085560656881635

theorem tailTrace_1156440 : CollatzResearch.WordTrace tailWord_1156440 prefixEnd_1156440 593809568085560656881635 := by
  unfold tailWord_1156440
  simp only [CollatzResearch.WordTrace]
  refine ⟨21089415965211429536497387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28119221286948572715329849 21089415965211429536497387)
  ·
    refine ⟨31634123947817144304746081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21089415965211429536497387 31634123947817144304746081)
    ·
      refine ⟨23725592960862858228559561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31634123947817144304746081 23725592960862858228559561)
      ·
        refine ⟨17794194720647143671419671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23725592960862858228559561 17794194720647143671419671)
        ·
          refine ⟨26691292080970715507129507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17794194720647143671419671 26691292080970715507129507)
          ·
            refine ⟨40036938121456073260694261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26691292080970715507129507 40036938121456073260694261)
            ·
              refine ⟨3753462948886506868190087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40036938121456073260694261 3753462948886506868190087)
              ·
                refine ⟨5630194423329760302285131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753462948886506868190087 5630194423329760302285131)
                ·
                  refine ⟨8445291634994640453427697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5630194423329760302285131 8445291634994640453427697)
                  ·
                    refine ⟨6333968726245980340070773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8445291634994640453427697 6333968726245980340070773)
                    ·
                      refine ⟨593809568085560656881635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6333968726245980340070773 593809568085560656881635)
                      ·
                        rfl

theorem cell23_1156440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1156440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156440 prefixEnd_1156440 := by exact prefixLift 1156440
  have htrace : WordTrace (prefixWord ++ tailWord_1156440) baseStart_1156440 baseEnd_1156440 := by
    simpa [prefixWord, tailWord_1156440, baseEnd_1156440] using wordTrace_append hprefix tailTrace_1156440
  have hstable : (prefixWord ++ tailWord_1156440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156440).length < 2 ^ (prefixWord ++ tailWord_1156440).sum := by decide
  have hdescent : baseEnd_1156440 < baseStart_1156440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156544 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2]
def baseStart_1156544 : Nat := 118140960795 + 1156544 * 2 ^ 59
def prefixEnd_1156544 : Nat := 4983230072969 + 3 ^ 40 * 1156544 * 2
def baseEnd_1156544 : Nat := 593862970073628249981157

theorem tailTrace_1156544 : CollatzResearch.WordTrace tailWord_1156544 prefixEnd_1156544 593862970073628249981157 := by
  unfold tailWord_1156544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091312561023042417390343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28121750081364056556520457 21091312561023042417390343)
  ·
    refine ⟨31636968841534563626085515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21091312561023042417390343 31636968841534563626085515)
    ·
      refine ⟨47455453262301845439128273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31636968841534563626085515 47455453262301845439128273)
      ·
        refine ⟨35591589946726384079346205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47455453262301845439128273 35591589946726384079346205)
        ·
          refine ⟨13346846230022394029754827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35591589946726384079346205 13346846230022394029754827)
          ·
            refine ⟨20020269345033591044632241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13346846230022394029754827 20020269345033591044632241)
            ·
              refine ⟨15015202008775193283474181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20020269345033591044632241 15015202008775193283474181)
              ·
                refine ⟨2815350376645348740651409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15015202008775193283474181 2815350376645348740651409)
                ·
                  refine ⟨2111512782484011555488557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2815350376645348740651409 2111512782484011555488557)
                  ·
                    refine ⟨791817293431504333308209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111512782484011555488557 791817293431504333308209)
                    ·
                      refine ⟨593862970073628249981157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 791817293431504333308209 593862970073628249981157)
                      ·
                        rfl

theorem cell23_1156544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_1156544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156544 prefixEnd_1156544 := by exact prefixLift 1156544
  have htrace : WordTrace (prefixWord ++ tailWord_1156544) baseStart_1156544 baseEnd_1156544 := by
    simpa [prefixWord, tailWord_1156544, baseEnd_1156544] using wordTrace_append hprefix tailTrace_1156544
  have hstable : (prefixWord ++ tailWord_1156544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156544).length < 2 ^ (prefixWord ++ tailWord_1156544).sum := by decide
  have hdescent : baseEnd_1156544 < baseStart_1156544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156551 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_1156551 : Nat := 118140960795 + 1156551 * 2 ^ 59
def prefixEnd_1156551 : Nat := 4983230072969 + 3 ^ 40 * 1156551 * 2
def baseEnd_1156551 : Nat := 593866564438209722593625

theorem tailTrace_1156551 : CollatzResearch.WordTrace tailWord_1156551 prefixEnd_1156551 593866564438209722593625 := by
  unfold tailWord_1156551
  simp only [CollatzResearch.WordTrace]
  refine ⟨42182880433020725030285507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28121920288680483353523671 42182880433020725030285507)
  ·
    refine ⟨63274320649531087545428261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42182880433020725030285507 63274320649531087545428261)
    ·
      refine ⟨11863935121787078914767799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63274320649531087545428261 11863935121787078914767799)
      ·
        refine ⟨17795902682680618372151699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11863935121787078914767799 17795902682680618372151699)
        ·
          refine ⟨26693854024020927558227549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17795902682680618372151699 26693854024020927558227549)
          ·
            refine ⟨10010195259007847834335331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26693854024020927558227549 10010195259007847834335331)
            ·
              refine ⟨15015292888511771751502997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10010195259007847834335331 15015292888511771751502997)
              ·
                refine ⟨703841854148989300851703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15015292888511771751502997 703841854148989300851703)
                ·
                  refine ⟨1055762781223483951277555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703841854148989300851703 1055762781223483951277555)
                  ·
                    refine ⟨1583644171835225926916333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1055762781223483951277555 1583644171835225926916333)
                    ·
                      refine ⟨593866564438209722593625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1583644171835225926916333 593866564438209722593625)
                      ·
                        rfl

theorem cell23_1156551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_1156551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156551 prefixEnd_1156551 := by exact prefixLift 1156551
  have htrace : WordTrace (prefixWord ++ tailWord_1156551) baseStart_1156551 baseEnd_1156551 := by
    simpa [prefixWord, tailWord_1156551, baseEnd_1156551] using wordTrace_append hprefix tailTrace_1156551
  have hstable : (prefixWord ++ tailWord_1156551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156551).length < 2 ^ (prefixWord ++ tailWord_1156551).sum := by decide
  have hdescent : baseEnd_1156551 < baseStart_1156551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156594 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1156594 : Nat := 118140960795 + 1156594 * 2 ^ 59
def prefixEnd_1156594 : Nat := 4983230072969 + 3 ^ 40 * 1156594 * 2
def baseEnd_1156594 : Nat := 593888644106353054355927

theorem tailTrace_1156594 : CollatzResearch.WordTrace tailWord_1156594 prefixEnd_1156594 593888644106353054355927 := by
  unfold tailWord_1156594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546112192966235843525209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28122965847909962249400557 10546112192966235843525209)
  ·
    refine ⟨7909584144724676882643907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10546112192966235843525209 7909584144724676882643907)
    ·
      refine ⟨11864376217087015323965861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909584144724676882643907 11864376217087015323965861)
      ·
        refine ⟨2224570540703815373243599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11864376217087015323965861 2224570540703815373243599)
        ·
          refine ⟨3336855811055723059865399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2224570540703815373243599 3336855811055723059865399)
          ·
            refine ⟨5005283716583584589798099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336855811055723059865399 5005283716583584589798099)
            ·
              refine ⟨7507925574875376884697149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005283716583584589798099 7507925574875376884697149)
              ·
                refine ⟨2815472090578266331761431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7507925574875376884697149 2815472090578266331761431)
                ·
                  refine ⟨4223208135867399497642147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815472090578266331761431 4223208135867399497642147)
                  ·
                    refine ⟨6334812203801099246463221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223208135867399497642147 6334812203801099246463221)
                    ·
                      refine ⟨593888644106353054355927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6334812203801099246463221 593888644106353054355927)
                      ·
                        rfl

theorem cell23_1156594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1156594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156594 prefixEnd_1156594 := by exact prefixLift 1156594
  have htrace : WordTrace (prefixWord ++ tailWord_1156594) baseStart_1156594 baseEnd_1156594 := by
    simpa [prefixWord, tailWord_1156594, baseEnd_1156594] using wordTrace_append hprefix tailTrace_1156594
  have hstable : (prefixWord ++ tailWord_1156594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156594).length < 2 ^ (prefixWord ++ tailWord_1156594).sum := by decide
  have hdescent : baseEnd_1156594 < baseStart_1156594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156607 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_1156607 : Nat := 118140960795 + 1156607 * 2 ^ 59
def prefixEnd_1156607 : Nat := 4983230072969 + 3 ^ 40 * 1156607 * 2
def baseEnd_1156607 : Nat := 593895319354861503493367

theorem tailTrace_1156607 : CollatzResearch.WordTrace tailWord_1156607 prefixEnd_1156607 593895319354861503493367 := by
  unfold tailWord_1156607
  simp only [CollatzResearch.WordTrace]
  refine ⟨42184922920817846594324075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28123281947211897729549383 42184922920817846594324075)
  ·
    refine ⟨63277384381226769891486113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42184922920817846594324075 63277384381226769891486113)
    ·
      refine ⟨47458038285920077418614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63277384381226769891486113 47458038285920077418614585)
      ·
        refine ⟨35593528714440058063960939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47458038285920077418614585 35593528714440058063960939)
        ·
          refine ⟨53390293071660087095941409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35593528714440058063960939 53390293071660087095941409)
          ·
            refine ⟨40042719803745065321956057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53390293071660087095941409 40042719803745065321956057)
            ·
              refine ⟨30032039852808798991467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40042719803745065321956057 30032039852808798991467043)
              ·
                refine ⟨45048059779213198487200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30032039852808798991467043 45048059779213198487200565)
                ·
                  refine ⟨4223255604301237358175053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45048059779213198487200565 4223255604301237358175053)
                  ·
                    refine ⟨1583720851612964009315645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4223255604301237358175053 1583720851612964009315645)
                    ·
                      refine ⟨593895319354861503493367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1583720851612964009315645 593895319354861503493367)
                      ·
                        rfl

theorem cell23_1156607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_1156607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156607 prefixEnd_1156607 := by exact prefixLift 1156607
  have htrace : WordTrace (prefixWord ++ tailWord_1156607) baseStart_1156607 baseEnd_1156607 := by
    simpa [prefixWord, tailWord_1156607, baseEnd_1156607] using wordTrace_append hprefix tailTrace_1156607
  have hstable : (prefixWord ++ tailWord_1156607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156607).length < 2 ^ (prefixWord ++ tailWord_1156607).sum := by decide
  have hdescent : baseEnd_1156607 < baseStart_1156607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156618 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_1156618 : Nat := 118140960795 + 1156618 * 2 ^ 59
def prefixEnd_1156618 : Nat := 4983230072969 + 3 ^ 40 * 1156618 * 2
def baseEnd_1156618 : Nat := 197966989214020320151939

theorem tailTrace_1156618 : CollatzResearch.WordTrace tailWord_1156618 prefixEnd_1156618 197966989214020320151939 := by
  unfold tailWord_1156618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546331030944498868243627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28123549415851996981983005 10546331030944498868243627)
  ·
    refine ⟨15819496546416748302365441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10546331030944498868243627 15819496546416748302365441)
    ·
      refine ⟨11864622409812561226774081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15819496546416748302365441 11864622409812561226774081)
      ·
        refine ⟨8898466807359420920080561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11864622409812561226774081 8898466807359420920080561)
        ·
          refine ⟨6673850105519565690060421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8898466807359420920080561 6673850105519565690060421)
          ·
            refine ⟨1251346894784918566886329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6673850105519565690060421 1251346894784918566886329)
            ·
              refine ⟨938510171088688925164747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251346894784918566886329 938510171088688925164747)
              ·
                refine ⟨1407765256633033387747121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938510171088688925164747 1407765256633033387747121)
                ·
                  refine ⟨1055823942474775040810341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1407765256633033387747121 1055823942474775040810341)
                  ·
                    refine ⟨197966989214020320151939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1055823942474775040810341 197966989214020320151939)
                    ·
                      rfl

theorem cell23_1156618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_1156618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156618 prefixEnd_1156618 := by exact prefixLift 1156618
  have htrace : WordTrace (prefixWord ++ tailWord_1156618) baseStart_1156618 baseEnd_1156618 := by
    simpa [prefixWord, tailWord_1156618, baseEnd_1156618] using wordTrace_append hprefix tailTrace_1156618
  have hstable : (prefixWord ++ tailWord_1156618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156618).length < 2 ^ (prefixWord ++ tailWord_1156618).sum := by decide
  have hdescent : baseEnd_1156618 < baseStart_1156618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156628 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1156628 : Nat := 118140960795 + 1156628 * 2 ^ 59
def prefixEnd_1156628 : Nat := 4983230072969 + 3 ^ 40 * 1156628 * 2
def baseEnd_1156628 : Nat := 593906102448605921330771

theorem tailTrace_1156628 : CollatzResearch.WordTrace tailWord_1156628 prefixEnd_1156628 593906102448605921330771 := by
  unfold tailWord_1156628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21092844426870883590419269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28123792569161178120559025 21092844426870883590419269)
  ·
    refine ⟨3954908330038290673203613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21092844426870883590419269 3954908330038290673203613)
    ·
      refine ⟨1483090623764359002451355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3954908330038290673203613 1483090623764359002451355)
      ·
        refine ⟨2224635935646538503677033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483090623764359002451355 2224635935646538503677033)
        ·
          refine ⟨1668476951734903877757775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224635935646538503677033 1668476951734903877757775)
          ·
            refine ⟨2502715427602355816636663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668476951734903877757775 2502715427602355816636663)
            ·
              refine ⟨3754073141403533724954995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502715427602355816636663 3754073141403533724954995)
              ·
                refine ⟨5631109712105300587432493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754073141403533724954995 5631109712105300587432493)
                ·
                  refine ⟨2111666142039487720287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5631109712105300587432493 2111666142039487720287185)
                  ·
                    refine ⟨1583749606529615790215389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2111666142039487720287185 1583749606529615790215389)
                    ·
                      refine ⟨593906102448605921330771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1583749606529615790215389 593906102448605921330771)
                      ·
                        rfl

theorem cell23_1156628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1156628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156628 prefixEnd_1156628 := by exact prefixLift 1156628
  have htrace : WordTrace (prefixWord ++ tailWord_1156628) baseStart_1156628 baseEnd_1156628 := by
    simpa [prefixWord, tailWord_1156628, baseEnd_1156628] using wordTrace_append hprefix tailTrace_1156628
  have hstable : (prefixWord ++ tailWord_1156628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156628).length < 2 ^ (prefixWord ++ tailWord_1156628).sum := by decide
  have hdescent : baseEnd_1156628 < baseStart_1156628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156657 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1156657 : Nat := 118140960795 + 1156657 * 2 ^ 59
def prefixEnd_1156657 : Nat := 4983230072969 + 3 ^ 40 * 1156657 * 2
def baseEnd_1156657 : Nat := 197973664462528769289379

theorem tailTrace_1156657 : CollatzResearch.WordTrace tailWord_1156657 prefixEnd_1156657 197973664462528769289379 := by
  unfold tailWord_1156657
  simp only [CollatzResearch.WordTrace]
  refine ⟨42186746570636705133644225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28124497713757803422429483 42186746570636705133644225)
  ·
    refine ⟨31640059927977528850233169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42186746570636705133644225 31640059927977528850233169)
    ·
      refine ⟨23730044945983146637674877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31640059927977528850233169 23730044945983146637674877)
      ·
        refine ⟨8898766854743679989128079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23730044945983146637674877 8898766854743679989128079)
        ·
          refine ⟨13348150282115519983692119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8898766854743679989128079 13348150282115519983692119)
          ·
            refine ⟨20022225423173279975538179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13348150282115519983692119 20022225423173279975538179)
            ·
              refine ⟨30033338134759919963307269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20022225423173279975538179 30033338134759919963307269)
              ·
                refine ⟨5631250900267484993120113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30033338134759919963307269 5631250900267484993120113)
                ·
                  refine ⟨4223438175200613744840085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5631250900267484993120113 4223438175200613744840085)
                  ·
                    refine ⟨197973664462528769289379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4223438175200613744840085 197973664462528769289379)
                    ·
                      rfl

theorem cell23_1156657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1156657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156657 prefixEnd_1156657 := by exact prefixLift 1156657
  have htrace : WordTrace (prefixWord ++ tailWord_1156657) baseStart_1156657 baseEnd_1156657 := by
    simpa [prefixWord, tailWord_1156657, baseEnd_1156657] using wordTrace_append hprefix tailTrace_1156657
  have hstable : (prefixWord ++ tailWord_1156657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156657).length < 2 ^ (prefixWord ++ tailWord_1156657).sum := by decide
  have hdescent : baseEnd_1156657 < baseStart_1156657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156727 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1156727 : Nat := 118140960795 + 1156727 * 2 ^ 59
def prefixEnd_1156727 : Nat := 4983230072969 + 3 ^ 40 * 1156727 * 2
def baseEnd_1156727 : Nat := 593956937033401033992815

theorem tailTrace_1156727 : CollatzResearch.WordTrace tailWord_1156727 prefixEnd_1156727 593956937033401033992815 := by
  unfold tailWord_1156727
  simp only [CollatzResearch.WordTrace]
  refine ⟨42189299680383107088692435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28126199786922071392461623 42189299680383107088692435)
  ·
    refine ⟨63283949520574660633038653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42189299680383107088692435 63283949520574660633038653)
    ·
      refine ⟨23731481070215497737389495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63283949520574660633038653 23731481070215497737389495)
      ·
        refine ⟨35597221605323246606084243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23731481070215497737389495 35597221605323246606084243)
        ·
          refine ⟨53395832407984869909126365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35597221605323246606084243 53395832407984869909126365)
          ·
            refine ⟨20023437152994326215922387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53395832407984869909126365 20023437152994326215922387)
            ·
              refine ⟨30035155729491489323883581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20023437152994326215922387 30035155729491489323883581)
              ·
                refine ⟨11263183398559308496456343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30035155729491489323883581 11263183398559308496456343)
                ·
                  refine ⟨16894775097838962744684515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11263183398559308496456343 16894775097838962744684515)
                  ·
                    refine ⟨25342162646758444117026773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16894775097838962744684515 25342162646758444117026773)
                    ·
                      refine ⟨593956937033401033992815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25342162646758444117026773 593956937033401033992815)
                      ·
                        rfl

theorem cell23_1156727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1156727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156727 prefixEnd_1156727 := by exact prefixLift 1156727
  have htrace : WordTrace (prefixWord ++ tailWord_1156727) baseStart_1156727 baseEnd_1156727 := by
    simpa [prefixWord, tailWord_1156727, baseEnd_1156727] using wordTrace_append hprefix tailTrace_1156727
  have hstable : (prefixWord ++ tailWord_1156727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156727).length < 2 ^ (prefixWord ++ tailWord_1156727).sum := by decide
  have hdescent : baseEnd_1156727 < baseStart_1156727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156747 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 8]
def baseStart_1156747 : Nat := 118140960795 + 1156747 * 2 ^ 59
def prefixEnd_1156747 : Nat := 4983230072969 + 3 ^ 40 * 1156747 * 2
def baseEnd_1156747 : Nat := 197989068882163651914241

theorem tailTrace_1156747 : CollatzResearch.WordTrace tailWord_1156747 prefixEnd_1156747 197989068882163651914241 := by
  unfold tailWord_1156747
  simp only [CollatzResearch.WordTrace]
  refine ⟨42190029140310650504420495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28126686093540433669613663 42190029140310650504420495)
  ·
    refine ⟨63285043710465975756630743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42190029140310650504420495 63285043710465975756630743)
    ·
      refine ⟨94927565565698963634946115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63285043710465975756630743 94927565565698963634946115)
      ·
        refine ⟨142391348348548445452419173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94927565565698963634946115 142391348348548445452419173)
        ·
          refine ⟨26698377815352833522328595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142391348348548445452419173 26698377815352833522328595)
          ·
            refine ⟨40047566723029250283492893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26698377815352833522328595 40047566723029250283492893)
            ·
              refine ⟨15017837521135968856309835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40047566723029250283492893 15017837521135968856309835)
              ·
                refine ⟨22526756281703953284464753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15017837521135968856309835 22526756281703953284464753)
                ·
                  refine ⟨16895067211277964963348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22526756281703953284464753 16895067211277964963348565)
                  ·
                    refine ⟨197989068882163651914241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16895067211277964963348565 197989068882163651914241)
                    ·
                      rfl

theorem cell23_1156747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_1156747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156747 prefixEnd_1156747 := by exact prefixLift 1156747
  have htrace : WordTrace (prefixWord ++ tailWord_1156747) baseStart_1156747 baseEnd_1156747 := by
    simpa [prefixWord, tailWord_1156747, baseEnd_1156747] using wordTrace_append hprefix tailTrace_1156747
  have hstable : (prefixWord ++ tailWord_1156747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156747).length < 2 ^ (prefixWord ++ tailWord_1156747).sum := by decide
  have hdescent : baseEnd_1156747 < baseStart_1156747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156777 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 12]
def baseStart_1156777 : Nat := 118140960795 + 1156777 * 2 ^ 59
def prefixEnd_1156777 : Nat := 4983230072969 + 3 ^ 40 * 1156777 * 2
def baseEnd_1156777 : Nat := 65998067896236204263065

theorem tailTrace_1156777 : CollatzResearch.WordTrace tailWord_1156777 prefixEnd_1156777 65998067896236204263065 := by
  unfold tailWord_1156777
  simp only [CollatzResearch.WordTrace]
  refine ⟨42191123330201965628012585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28127415553467977085341723 42191123330201965628012585)
  ·
    refine ⟨31643342497651474221009439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42191123330201965628012585 31643342497651474221009439)
    ·
      refine ⟨47465013746477211331514159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31643342497651474221009439 47465013746477211331514159)
      ·
        refine ⟨71197520619715816997271239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47465013746477211331514159 71197520619715816997271239)
        ·
          refine ⟨106796280929573725495906859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71197520619715816997271239 106796280929573725495906859)
          ·
            refine ⟨160194421394360588243860289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106796280929573725495906859 160194421394360588243860289)
            ·
              refine ⟨120145816045770441182895217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160194421394360588243860289 120145816045770441182895217)
              ·
                refine ⟨90109362034327830887171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120145816045770441182895217 90109362034327830887171413)
                ·
                  refine ⟨65998067896236204263065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 90109362034327830887171413 65998067896236204263065)
                  ·
                    rfl

theorem cell23_1156777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_1156777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156777 prefixEnd_1156777 := by exact prefixLift 1156777
  have htrace : WordTrace (prefixWord ++ tailWord_1156777) baseStart_1156777 baseEnd_1156777 := by
    simpa [prefixWord, tailWord_1156777, baseEnd_1156777] using wordTrace_append hprefix tailTrace_1156777
  have hstable : (prefixWord ++ tailWord_1156777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156777).length < 2 ^ (prefixWord ++ tailWord_1156777).sum := by decide
  have hdescent : baseEnd_1156777 < baseStart_1156777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156802 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1156802 : Nat := 118140960795 + 1156802 * 2 ^ 59
def prefixEnd_1156802 : Nat := 4983230072969 + 3 ^ 40 * 1156802 * 2
def baseEnd_1156802 : Nat := 197998482694162746851657

theorem tailTrace_1156802 : CollatzResearch.WordTrace tailWord_1156802 prefixEnd_1156802 197998482694162746851657 := by
  unfold tailWord_1156802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548008788777848724418165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28128023436740929931781773 10548008788777848724418165)
  ·
    refine ⟨988875823947923317914203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10548008788777848724418165 988875823947923317914203)
    ·
      refine ⟨1483313735921884976871305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988875823947923317914203 1483313735921884976871305)
      ·
        refine ⟨1112485301941413732653479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483313735921884976871305 1112485301941413732653479)
        ·
          refine ⟨1668727952912120598980219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112485301941413732653479 1668727952912120598980219)
          ·
            refine ⟨2503091929368180898470329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668727952912120598980219 2503091929368180898470329)
            ·
              refine ⟨1877318947026135673852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503091929368180898470329 1877318947026135673852747)
              ·
                refine ⟨2815978420539203510779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877318947026135673852747 2815978420539203510779121)
                ·
                  refine ⟨2111983815404402633084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2815978420539203510779121 2111983815404402633084341)
                  ·
                    refine ⟨197998482694162746851657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2111983815404402633084341 197998482694162746851657)
                    ·
                      rfl

theorem cell23_1156802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1156802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156802 prefixEnd_1156802 := by exact prefixLift 1156802
  have htrace : WordTrace (prefixWord ++ tailWord_1156802) baseStart_1156802 baseEnd_1156802 := by
    simpa [prefixWord, tailWord_1156802, baseEnd_1156802] using wordTrace_append hprefix tailTrace_1156802
  have hstable : (prefixWord ++ tailWord_1156802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156802).length < 2 ^ (prefixWord ++ tailWord_1156802).sum := by decide
  have hdescent : baseEnd_1156802 < baseStart_1156802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156861 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_1156861 : Nat := 118140960795 + 1156861 * 2 ^ 59
def prefixEnd_1156861 : Nat := 4983230072969 + 3 ^ 40 * 1156861 * 2
def baseEnd_1156861 : Nat := 594025743441103509717199

theorem tailTrace_1156861 : CollatzResearch.WordTrace tailWord_1156861 prefixEnd_1156861 594025743441103509717199 := by
  unfold tailWord_1156861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42194187061897647974070437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28129458041265098649380291 42194187061897647974070437)
  ·
    refine ⟨7911410074105808995138207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42194187061897647974070437 7911410074105808995138207)
    ·
      refine ⟨11867115111158713492707311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7911410074105808995138207 11867115111158713492707311)
      ·
        refine ⟨17800672666738070239060967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11867115111158713492707311 17800672666738070239060967)
        ·
          refine ⟨26701009000107105358591451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17800672666738070239060967 26701009000107105358591451)
          ·
            refine ⟨40051513500160658037887177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26701009000107105358591451 40051513500160658037887177)
            ·
              refine ⟨30038635125120493528415383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40051513500160658037887177 30038635125120493528415383)
              ·
                refine ⟨45057952687680740292623075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30038635125120493528415383 45057952687680740292623075)
                ·
                  refine ⟨67586929031521110438934613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45057952687680740292623075 67586929031521110438934613)
                  ·
                    refine ⟨792034324588138012956265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67586929031521110438934613 792034324588138012956265)
                    ·
                      refine ⟨594025743441103509717199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792034324588138012956265 594025743441103509717199)
                      ·
                        rfl

theorem cell23_1156861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_1156861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156861 prefixEnd_1156861 := by exact prefixLift 1156861
  have htrace : WordTrace (prefixWord ++ tailWord_1156861) baseStart_1156861 baseEnd_1156861 := by
    simpa [prefixWord, tailWord_1156861, baseEnd_1156861] using wordTrace_append hprefix tailTrace_1156861
  have hstable : (prefixWord ++ tailWord_1156861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156861).length < 2 ^ (prefixWord ++ tailWord_1156861).sum := by decide
  have hdescent : baseEnd_1156861 < baseStart_1156861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1156864 : Nat := 118140960795 + 1156864 * 2 ^ 59
def prefixEnd_1156864 : Nat := 4983230072969 + 3 ^ 40 * 1156864 * 2
def baseEnd_1156864 : Nat := 594027283883066997979685

theorem tailTrace_1156864 : CollatzResearch.WordTrace tailWord_1156864 prefixEnd_1156864 594027283883066997979685 := by
  unfold tailWord_1156864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097148240443389743214823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28129530987257852990953097 21097148240443389743214823)
  ·
    refine ⟨31645722360665084614822235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097148240443389743214823 31645722360665084614822235)
    ·
      refine ⟨47468583540997626922233353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31645722360665084614822235 47468583540997626922233353)
      ·
        refine ⟨35601437655748220191675015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47468583540997626922233353 35601437655748220191675015)
        ·
          refine ⟨53402156483622330287512523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35601437655748220191675015 53402156483622330287512523)
          ·
            refine ⟨80103234725433495431268785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53402156483622330287512523 80103234725433495431268785)
            ·
              refine ⟨60077426044075121573451589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80103234725433495431268785 60077426044075121573451589)
              ·
                refine ⟨11264517383264085295022173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60077426044075121573451589 11264517383264085295022173)
                ·
                  refine ⟨4224194018724031985633315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11264517383264085295022173 4224194018724031985633315)
                  ·
                    refine ⟨6336291028086047978449973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224194018724031985633315 6336291028086047978449973)
                    ·
                      refine ⟨594027283883066997979685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6336291028086047978449973 594027283883066997979685)
                      ·
                        rfl

theorem cell23_1156864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1156864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156864 prefixEnd_1156864 := by exact prefixLift 1156864
  have htrace : WordTrace (prefixWord ++ tailWord_1156864) baseStart_1156864 baseEnd_1156864 := by
    simpa [prefixWord, tailWord_1156864, baseEnd_1156864] using wordTrace_append hprefix tailTrace_1156864
  have hstable : (prefixWord ++ tailWord_1156864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156864).length < 2 ^ (prefixWord ++ tailWord_1156864).sum := by decide
  have hdescent : baseEnd_1156864 < baseStart_1156864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156888 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_1156888 : Nat := 118140960795 + 1156888 * 2 ^ 59
def prefixEnd_1156888 : Nat := 4983230072969 + 3 ^ 40 * 1156888 * 2
def baseEnd_1156888 : Nat := 198013202472924968026525

theorem tailTrace_1156888 : CollatzResearch.WordTrace tailWord_1156888 prefixEnd_1156888 198013202472924968026525 := by
  unfold tailWord_1156888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097585916399915792651659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28130114555199887723535545 21097585916399915792651659)
  ·
    refine ⟨31646378874599873688977489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097585916399915792651659 31646378874599873688977489)
    ·
      refine ⟨23734784155949905266733117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31646378874599873688977489 23734784155949905266733117)
      ·
        refine ⟨8900544058481214475024919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23734784155949905266733117 8900544058481214475024919)
        ·
          refine ⟨13350816087721821712537379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8900544058481214475024919 13350816087721821712537379)
          ·
            refine ⟨20026224131582732568806069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13350816087721821712537379 20026224131582732568806069)
            ·
              refine ⟨1877458512335881178325569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20026224131582732568806069 1877458512335881178325569)
              ·
                refine ⟨1408093884251910883744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877458512335881178325569 1408093884251910883744177)
                ·
                  refine ⟨1056070413188933162808133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408093884251910883744177 1056070413188933162808133)
                  ·
                    refine ⟨198013202472924968026525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056070413188933162808133 198013202472924968026525)
                    ·
                      rfl

theorem cell23_1156888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_1156888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156888 prefixEnd_1156888 := by exact prefixLift 1156888
  have htrace : WordTrace (prefixWord ++ tailWord_1156888) baseStart_1156888 baseEnd_1156888 := by
    simpa [prefixWord, tailWord_1156888, baseEnd_1156888] using wordTrace_append hprefix tailTrace_1156888
  have hstable : (prefixWord ++ tailWord_1156888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156888).length < 2 ^ (prefixWord ++ tailWord_1156888).sum := by decide
  have hdescent : baseEnd_1156888 < baseStart_1156888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156895 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 3, 2, 2]
def baseStart_1156895 : Nat := 118140960795 + 1156895 * 2 ^ 59
def prefixEnd_1156895 : Nat := 4983230072969 + 3 ^ 40 * 1156895 * 2
def baseEnd_1156895 : Nat := 594043201783356376692043

theorem tailTrace_1156895 : CollatzResearch.WordTrace tailWord_1156895 prefixEnd_1156895 594043201783356376692043 := by
  unfold tailWord_1156895
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195427143774471780808139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28130284762516314520538759 42195427143774471780808139)
  ·
    refine ⟨63293140715661707671212209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42195427143774471780808139 63293140715661707671212209)
    ·
      refine ⟨47469855536746280753409157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63293140715661707671212209 47469855536746280753409157)
      ·
        refine ⟨8900597913139927641264217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47469855536746280753409157 8900597913139927641264217)
        ·
          refine ⟨6675448434854945730948163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8900597913139927641264217 6675448434854945730948163)
          ·
            refine ⟨10013172652282418596422245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675448434854945730948163 10013172652282418596422245)
            ·
              refine ⟨1877469872302953486829171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10013172652282418596422245 1877469872302953486829171)
              ·
                refine ⟨2816204808454430230243757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877469872302953486829171 2816204808454430230243757)
                ·
                  refine ⟨1056076803170411336341409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2816204808454430230243757 1056076803170411336341409)
                  ·
                    refine ⟨792057602377808502256057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056076803170411336341409 792057602377808502256057)
                    ·
                      refine ⟨594043201783356376692043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792057602377808502256057 594043201783356376692043)
                      ·
                        rfl

theorem cell23_1156895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_1156895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156895 prefixEnd_1156895 := by exact prefixLift 1156895
  have htrace : WordTrace (prefixWord ++ tailWord_1156895) baseStart_1156895 baseEnd_1156895 := by
    simpa [prefixWord, tailWord_1156895, baseEnd_1156895] using wordTrace_append hprefix tailTrace_1156895
  have hstable : (prefixWord ++ tailWord_1156895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156895).length < 2 ^ (prefixWord ++ tailWord_1156895).sum := by decide
  have hdescent : baseEnd_1156895 < baseStart_1156895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156908 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_1156908 : Nat := 118140960795 + 1156908 * 2 ^ 59
def prefixEnd_1156908 : Nat := 4983230072969 + 3 ^ 40 * 1156908 * 2
def baseEnd_1156908 : Nat := 594049877031864825829483

theorem tailTrace_1156908 : CollatzResearch.WordTrace tailWord_1156908 prefixEnd_1156908 594049877031864825829483 := by
  unfold tailWord_1156908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097950646363687500515689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28130600861818250000687585 21097950646363687500515689)
  ·
    refine ⟨15823462984772765625386767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21097950646363687500515689 15823462984772765625386767)
    ·
      refine ⟨23735194477159148438080151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15823462984772765625386767 23735194477159148438080151)
      ·
        refine ⟨35602791715738722657120227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23735194477159148438080151 35602791715738722657120227)
        ·
          refine ⟨53404187573608083985680341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35602791715738722657120227 53404187573608083985680341)
          ·
            refine ⟨1251660646256439468414383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53404187573608083985680341 1251660646256439468414383)
            ·
              refine ⟨1877490969384659202621575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251660646256439468414383 1877490969384659202621575)
              ·
                refine ⟨2816236454076988803932363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877490969384659202621575 2816236454076988803932363)
                ·
                  refine ⟨4224354681115483205898545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816236454076988803932363 4224354681115483205898545)
                  ·
                    refine ⟨3168266010836612404423909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224354681115483205898545 3168266010836612404423909)
                    ·
                      refine ⟨594049877031864825829483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3168266010836612404423909 594049877031864825829483)
                      ·
                        rfl

theorem cell23_1156908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_1156908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156908 prefixEnd_1156908 := by exact prefixLift 1156908
  have htrace : WordTrace (prefixWord ++ tailWord_1156908) baseStart_1156908 baseEnd_1156908 := by
    simpa [prefixWord, tailWord_1156908, baseEnd_1156908] using wordTrace_append hprefix tailTrace_1156908
  have hstable : (prefixWord ++ tailWord_1156908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156908).length < 2 ^ (prefixWord ++ tailWord_1156908).sum := by decide
  have hdescent : baseEnd_1156908 < baseStart_1156908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156915 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 3]
def baseStart_1156915 : Nat := 118140960795 + 1156915 * 2 ^ 59
def prefixEnd_1156915 : Nat := 4983230072969 + 3 ^ 40 * 1156915 * 2
def baseEnd_1156915 : Nat := 594053471396446298441951

theorem tailTrace_1156915 : CollatzResearch.WordTrace tailWord_1156915 prefixEnd_1156915 594053471396446298441951 := by
  unfold tailWord_1156915
  simp only [CollatzResearch.WordTrace]
  refine ⟨42196156603702015196536199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28130771069134676797690799 42196156603702015196536199)
  ·
    refine ⟨63294234905553022794804299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42196156603702015196536199 63294234905553022794804299)
    ·
      refine ⟨94941352358329534192206449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63294234905553022794804299 94941352358329534192206449)
      ·
        refine ⟨71206014268747150644154837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94941352358329534192206449 71206014268747150644154837)
        ·
          refine ⟨1668890959423761343222379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71206014268747150644154837 1668890959423761343222379)
          ·
            refine ⟨2503336439135642014833569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668890959423761343222379 2503336439135642014833569)
            ·
              refine ⟨1877502329351731511125177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503336439135642014833569 1877502329351731511125177)
              ·
                refine ⟨1408126747013798633343883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877502329351731511125177 1408126747013798633343883)
                ·
                  refine ⟨2112190120520697950015825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408126747013798633343883 2112190120520697950015825)
                  ·
                    refine ⟨1584142590390523462511869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112190120520697950015825 1584142590390523462511869)
                    ·
                      refine ⟨594053471396446298441951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584142590390523462511869 594053471396446298441951)
                      ·
                        rfl

theorem cell23_1156915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_1156915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156915 prefixEnd_1156915 := by exact prefixLift 1156915
  have htrace : WordTrace (prefixWord ++ tailWord_1156915) baseStart_1156915 baseEnd_1156915 := by
    simpa [prefixWord, tailWord_1156915, baseEnd_1156915] using wordTrace_append hprefix tailTrace_1156915
  have hstable : (prefixWord ++ tailWord_1156915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156915).length < 2 ^ (prefixWord ++ tailWord_1156915).sum := by decide
  have hdescent : baseEnd_1156915 < baseStart_1156915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156918 : List Nat := [5, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1156918 : Nat := 118140960795 + 1156918 * 2 ^ 59
def prefixEnd_1156918 : Nat := 4983230072969 + 3 ^ 40 * 1156918 * 2
def baseEnd_1156918 : Nat := 22002037475496658766831

theorem tailTrace_1156918 : CollatzResearch.WordTrace tailWord_1156918 prefixEnd_1156918 22002037475496658766831 := by
  unfold tailWord_1156918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637266626418196669305963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28130844015127431139263605 2637266626418196669305963)
  ·
    refine ⟨3955899939627295003958945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2637266626418196669305963 3955899939627295003958945)
    ·
      refine ⟨2966924954720471252969209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3955899939627295003958945 2966924954720471252969209)
      ·
        refine ⟨2225193716040353439726907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2966924954720471252969209 2225193716040353439726907)
        ·
          refine ⟨3337790574060530159590361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225193716040353439726907 3337790574060530159590361)
          ·
            refine ⟨2503342930545397619692771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337790574060530159590361 2503342930545397619692771)
            ·
              refine ⟨3755014395818096429539157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503342930545397619692771 3755014395818096429539157)
              ·
                refine ⟨22002037475496658766831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3755014395818096429539157 22002037475496658766831)
                ·
                  rfl

theorem cell23_1156918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1156918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156918 prefixEnd_1156918 := by exact prefixLift 1156918
  have htrace : WordTrace (prefixWord ++ tailWord_1156918) baseStart_1156918 baseEnd_1156918 := by
    simpa [prefixWord, tailWord_1156918, baseEnd_1156918] using wordTrace_append hprefix tailTrace_1156918
  have hstable : (prefixWord ++ tailWord_1156918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156918).length < 2 ^ (prefixWord ++ tailWord_1156918).sum := by decide
  have hdescent : baseEnd_1156918 < baseStart_1156918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156962 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1156962 : Nat := 118140960795 + 1156962 * 2 ^ 59
def prefixEnd_1156962 : Nat := 4983230072969 + 3 ^ 40 * 1156962 * 2
def baseEnd_1156962 : Nat := 594077604987207614554235

theorem tailTrace_1156962 : CollatzResearch.WordTrace tailWord_1156962 prefixEnd_1156962 594077604987207614554235 := by
  unfold tailWord_1156962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549467708632935555874285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28131913889687828148998093 10549467708632935555874285)
  ·
    refine ⟨3956050390737350833452857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10549467708632935555874285 3956050390737350833452857)
    ·
      refine ⟨2967037793053013125089643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3956050390737350833452857 2967037793053013125089643)
      ·
        refine ⟨4450556689579519687634465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967037793053013125089643 4450556689579519687634465)
        ·
          refine ⟨3337917517184639765725849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450556689579519687634465 3337917517184639765725849)
          ·
            refine ⟨2503438137888479824294387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337917517184639765725849 2503438137888479824294387)
            ·
              refine ⟨3755157206832719736441581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503438137888479824294387 3755157206832719736441581)
              ·
                refine ⟨1408183952562269901165593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755157206832719736441581 1408183952562269901165593)
                ·
                  refine ⟨1056137964421702425874195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408183952562269901165593 1056137964421702425874195)
                  ·
                    refine ⟨1584206946632553638811293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056137964421702425874195 1584206946632553638811293)
                    ·
                      refine ⟨594077604987207614554235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584206946632553638811293 594077604987207614554235)
                      ·
                        rfl

theorem cell23_1156962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1156962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156962 prefixEnd_1156962 := by exact prefixLift 1156962
  have htrace : WordTrace (prefixWord ++ tailWord_1156962) baseStart_1156962 baseEnd_1156962 := by
    simpa [prefixWord, tailWord_1156962, baseEnd_1156962] using wordTrace_append hprefix tailTrace_1156962
  have hstable : (prefixWord ++ tailWord_1156962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156962).length < 2 ^ (prefixWord ++ tailWord_1156962).sum := by decide
  have hdescent : baseEnd_1156962 < baseStart_1156962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156972 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_1156972 : Nat := 118140960795 + 1156972 * 2 ^ 59
def prefixEnd_1156972 : Nat := 4983230072969 + 3 ^ 40 * 1156972 * 2
def baseEnd_1156972 : Nat := 594082739793752575429189

theorem tailTrace_1156972 : CollatzResearch.WordTrace tailWord_1156972 prefixEnd_1156972 594082739793752575429189 := by
  unfold tailWord_1156972
  simp only [CollatzResearch.WordTrace]
  refine ⟨21099117782247756965680585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28132157042997009287574113 21099117782247756965680585)
  ·
    refine ⟨15824338336685817724260439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21099117782247756965680585 15824338336685817724260439)
    ·
      refine ⟨23736507505028726586390659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15824338336685817724260439 23736507505028726586390659)
      ·
        refine ⟨35604761257543089879585989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23736507505028726586390659 35604761257543089879585989)
        ·
          refine ⟨6675892735789329352422373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35604761257543089879585989 6675892735789329352422373)
          ·
            refine ⟨1251729887960499253579195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6675892735789329352422373 1251729887960499253579195)
            ·
              refine ⟨1877594831940748880368793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251729887960499253579195 1877594831940748880368793)
              ·
                refine ⟨1408196123955561660276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877594831940748880368793 1408196123955561660276595)
                ·
                  refine ⟨2112294185933342490414893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408196123955561660276595 2112294185933342490414893)
                  ·
                    refine ⟨792110319725003433905585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2112294185933342490414893 792110319725003433905585)
                    ·
                      refine ⟨594082739793752575429189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792110319725003433905585 594082739793752575429189)
                      ·
                        rfl

theorem cell23_1156972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_1156972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1156972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1156972 prefixEnd_1156972 := by exact prefixLift 1156972
  have htrace : WordTrace (prefixWord ++ tailWord_1156972) baseStart_1156972 baseEnd_1156972 := by
    simpa [prefixWord, tailWord_1156972, baseEnd_1156972] using wordTrace_append hprefix tailTrace_1156972
  have hstable : (prefixWord ++ tailWord_1156972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156972).length < 2 ^ (prefixWord ++ tailWord_1156972).sum := by decide
  have hdescent : baseEnd_1156972 < baseStart_1156972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157018 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1157018 : Nat := 118140960795 + 1157018 * 2 ^ 59
def prefixEnd_1157018 : Nat := 4983230072969 + 3 ^ 40 * 1157018 * 2
def baseEnd_1157018 : Nat := 594106359903859395453977

theorem tailTrace_1157018 : CollatzResearch.WordTrace tailWord_1157018 prefixEnd_1157018 594106359903859395453977 := by
  unfold tailWord_1157018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549978330582215946883927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28133275548219242525023805 10549978330582215946883927)
  ·
    refine ⟨15824967495873323920325891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10549978330582215946883927 15824967495873323920325891)
    ·
      refine ⟨23737451243809985880488837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15824967495873323920325891 23737451243809985880488837)
      ·
        refine ⟨4450772108214372352591657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23737451243809985880488837 4450772108214372352591657)
        ·
          refine ⟨3338079081160779264443743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450772108214372352591657 3338079081160779264443743)
          ·
            refine ⟨5007118621741168896665615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338079081160779264443743 5007118621741168896665615)
            ·
              refine ⟨7510677932611753344998423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007118621741168896665615 7510677932611753344998423)
              ·
                refine ⟨11266016898917630017497635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510677932611753344998423 11266016898917630017497635)
                ·
                  refine ⟨16899025348376445026246453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266016898917630017497635 16899025348376445026246453)
                  ·
                    refine ⟨1584283626410291721210605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16899025348376445026246453 1584283626410291721210605)
                    ·
                      refine ⟨594106359903859395453977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584283626410291721210605 594106359903859395453977)
                      ·
                        rfl

theorem cell23_1157018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1157018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157018 prefixEnd_1157018 := by exact prefixLift 1157018
  have htrace : WordTrace (prefixWord ++ tailWord_1157018) baseStart_1157018 baseEnd_1157018 := by
    simpa [prefixWord, tailWord_1157018, baseEnd_1157018] using wordTrace_append hprefix tailTrace_1157018
  have hstable : (prefixWord ++ tailWord_1157018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157018).length < 2 ^ (prefixWord ++ tailWord_1157018).sum := by decide
  have hdescent : baseEnd_1157018 < baseStart_1157018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157071 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_1157071 : Nat := 118140960795 + 1157071 * 2 ^ 59
def prefixEnd_1157071 : Nat := 4983230072969 + 3 ^ 40 * 1157071 * 2
def baseEnd_1157071 : Nat := 594133574378547688091233

theorem tailTrace_1157071 : CollatzResearch.WordTrace tailWord_1157071 prefixEnd_1157071 594133574378547688091233 := by
  unfold tailWord_1157071
  simp only [CollatzResearch.WordTrace]
  refine ⟨42201846391136853839215067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28134564260757902559476711 42201846391136853839215067)
  ·
    refine ⟨63302769586705280758822601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42201846391136853839215067 63302769586705280758822601)
    ·
      refine ⟨47477077190028960569116951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63302769586705280758822601 47477077190028960569116951)
      ·
        refine ⟨71215615785043440853675427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47477077190028960569116951 71215615785043440853675427)
        ·
          refine ⟨106823423677565161280513141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71215615785043440853675427 106823423677565161280513141)
          ·
            refine ⟨10014695969771733870048107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106823423677565161280513141 10014695969771733870048107)
            ·
              refine ⟨15022043954657600805072161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10014695969771733870048107 15022043954657600805072161)
              ·
                refine ⟨11266532965993200603804121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15022043954657600805072161 11266532965993200603804121)
                ·
                  refine ⟨8449899724494900452853091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11266532965993200603804121 8449899724494900452853091)
                  ·
                    refine ⟨12674849586742350679279637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8449899724494900452853091 12674849586742350679279637)
                    ·
                      refine ⟨594133574378547688091233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12674849586742350679279637 594133574378547688091233)
                      ·
                        rfl

theorem cell23_1157071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_1157071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157071 prefixEnd_1157071 := by exact prefixLift 1157071
  have htrace : WordTrace (prefixWord ++ tailWord_1157071) baseStart_1157071 baseEnd_1157071 := by
    simpa [prefixWord, tailWord_1157071, baseEnd_1157071] using wordTrace_append hprefix tailTrace_1157071
  have hstable : (prefixWord ++ tailWord_1157071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157071).length < 2 ^ (prefixWord ++ tailWord_1157071).sum := by decide
  have hdescent : baseEnd_1157071 < baseStart_1157071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157128 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1157128 : Nat := 118140960795 + 1157128 * 2 ^ 59
def prefixEnd_1157128 : Nat := 4983230072969 + 3 ^ 40 * 1157128 * 2
def baseEnd_1157128 : Nat := 198054280925284655026157

theorem tailTrace_1157128 : CollatzResearch.WordTrace tailWord_1157128 prefixEnd_1157128 198054280925284655026157 := by
  unfold tailWord_1157128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21101962675965176287020019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28135950234620235049360025 21101962675965176287020019)
  ·
    refine ⟨31652944013947764430530029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21101962675965176287020019 31652944013947764430530029)
    ·
      refine ⟨11869854005230411661448761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31652944013947764430530029 11869854005230411661448761)
      ·
        refine ⟨8902390503922808746086571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11869854005230411661448761 8902390503922808746086571)
        ·
          refine ⟨13353585755884213119129857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8902390503922808746086571 13353585755884213119129857)
          ·
            refine ⟨10015189316913159839347393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13353585755884213119129857 10015189316913159839347393)
            ·
              refine ⟨7511391987684869879510545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10015189316913159839347393 7511391987684869879510545)
              ·
                refine ⟨5633543990763652409632909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7511391987684869879510545 5633543990763652409632909)
                ·
                  refine ⟨2112578996536369653612341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5633543990763652409632909 2112578996536369653612341)
                  ·
                    refine ⟨198054280925284655026157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2112578996536369653612341 198054280925284655026157)
                    ·
                      rfl

theorem cell23_1157128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1157128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157128 prefixEnd_1157128 := by exact prefixLift 1157128
  have htrace : WordTrace (prefixWord ++ tailWord_1157128) baseStart_1157128 baseEnd_1157128 := by
    simpa [prefixWord, tailWord_1157128, baseEnd_1157128] using wordTrace_append hprefix tailTrace_1157128
  have hstable : (prefixWord ++ tailWord_1157128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157128).length < 2 ^ (prefixWord ++ tailWord_1157128).sum := by decide
  have hdescent : baseEnd_1157128 < baseStart_1157128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157175 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 2, 4]
def baseStart_1157175 : Nat := 118140960795 + 1157175 * 2 ^ 59
def prefixEnd_1157175 : Nat := 4983230072969 + 3 ^ 40 * 1157175 * 2
def baseEnd_1157175 : Nat := 198062325455538427063585

theorem tailTrace_1157175 : CollatzResearch.WordTrace tailWord_1157175 prefixEnd_1157175 198062325455538427063585 := by
  unfold tailWord_1157175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42205639582760079601000979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28137093055173386400667319 42205639582760079601000979)
  ·
    refine ⟨63308459374140119401501469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42205639582760079601000979 63308459374140119401501469)
    ·
      refine ⟨23740672265302544775563051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63308459374140119401501469 23740672265302544775563051)
      ·
        refine ⟨35611008397953817163344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23740672265302544775563051 35611008397953817163344577)
        ·
          refine ⟨26708256298465362872508433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35611008397953817163344577 26708256298465362872508433)
          ·
            refine ⟨20031192223849022154381325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26708256298465362872508433 20031192223849022154381325)
            ·
              refine ⟨7511697083943383307892997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20031192223849022154381325 7511697083943383307892997)
              ·
                refine ⟨1408443203239384370229937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7511697083943383307892997 1408443203239384370229937)
                ·
                  refine ⟨1056332402429538277672453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408443203239384370229937 1056332402429538277672453)
                  ·
                    refine ⟨198062325455538427063585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056332402429538277672453 198062325455538427063585)
                    ·
                      rfl

theorem cell23_1157175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_1157175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157175 prefixEnd_1157175 := by exact prefixLift 1157175
  have htrace : WordTrace (prefixWord ++ tailWord_1157175) baseStart_1157175 baseEnd_1157175 := by
    simpa [prefixWord, tailWord_1157175, baseEnd_1157175] using wordTrace_append hprefix tailTrace_1157175
  have hstable : (prefixWord ++ tailWord_1157175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157175).length < 2 ^ (prefixWord ++ tailWord_1157175).sum := by decide
  have hdescent : baseEnd_1157175 < baseStart_1157175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157178 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1157178 : Nat := 118140960795 + 1157178 * 2 ^ 59
def prefixEnd_1157178 : Nat := 4983230072969 + 3 ^ 40 * 1157178 * 2
def baseEnd_1157178 : Nat := 594188516808578769453241

theorem tailTrace_1157178 : CollatzResearch.WordTrace tailWord_1157178 prefixEnd_1157178 594188516808578769453241 := by
  unfold tailWord_1157178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551437250437302778340047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28137166001166140742240125 10551437250437302778340047)
  ·
    refine ⟨15827155875655954167510071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551437250437302778340047 15827155875655954167510071)
    ·
      refine ⟨23740733813483931251265107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15827155875655954167510071 23740733813483931251265107)
      ·
        refine ⟨35611100720225896876897661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23740733813483931251265107 35611100720225896876897661)
        ·
          refine ⟨13354162770084711328836623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35611100720225896876897661 13354162770084711328836623)
          ·
            refine ⟨20031244155127066993254935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13354162770084711328836623 20031244155127066993254935)
            ·
              refine ⟨30046866232690600489882403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20031244155127066993254935 30046866232690600489882403)
              ·
                refine ⟨45070299349035900734823605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30046866232690600489882403 45070299349035900734823605)
                ·
                  refine ⟨4225340563972115693889713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45070299349035900734823605 4225340563972115693889713)
                  ·
                    refine ⟨3169005422979086770417285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225340563972115693889713 3169005422979086770417285)
                    ·
                      refine ⟨594188516808578769453241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3169005422979086770417285 594188516808578769453241)
                      ·
                        rfl

theorem cell23_1157178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1157178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157178 prefixEnd_1157178 := by exact prefixLift 1157178
  have htrace : WordTrace (prefixWord ++ tailWord_1157178) baseStart_1157178 baseEnd_1157178 := by
    simpa [prefixWord, tailWord_1157178, baseEnd_1157178] using wordTrace_append hprefix tailTrace_1157178
  have hstable : (prefixWord ++ tailWord_1157178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157178).length < 2 ^ (prefixWord ++ tailWord_1157178).sum := by decide
  have hdescent : baseEnd_1157178 < baseStart_1157178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157205 : List Nat := [1, 3, 2, 2, 1, 4, 3, 7]
def baseStart_1157205 : Nat := 118140960795 + 1157205 * 2 ^ 59
def prefixEnd_1157205 : Nat := 4983230072969 + 3 ^ 40 * 1157205 * 2
def baseEnd_1157205 : Nat := 22007495584675931993171

theorem tailTrace_1157205 : CollatzResearch.WordTrace tailWord_1157205 prefixEnd_1157205 22007495584675931993171 := by
  unfold tailWord_1157205
  simp only [CollatzResearch.WordTrace]
  refine ⟨42206733772651394724593069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28137822515100929816395379 42206733772651394724593069)
  ·
    refine ⟨15827525164744273021722401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42206733772651394724593069 15827525164744273021722401)
    ·
      refine ⟨11870643873558204766291801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15827525164744273021722401 11870643873558204766291801)
      ·
        refine ⟨8902982905168653574718851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11870643873558204766291801 8902982905168653574718851)
        ·
          refine ⟨13354474357752980362078277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8902982905168653574718851 13354474357752980362078277)
          ·
            refine ⟨2503963942078683817889677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13354474357752980362078277 2503963942078683817889677)
            ·
              refine ⟨938986478279506431708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2503963942078683817889677 938986478279506431708629)
              ·
                refine ⟨22007495584675931993171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 938986478279506431708629 22007495584675931993171)
                ·
                  rfl

theorem cell23_1157205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 7].length) (baseStart_1157205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157205 prefixEnd_1157205 := by exact prefixLift 1157205
  have htrace : WordTrace (prefixWord ++ tailWord_1157205) baseStart_1157205 baseEnd_1157205 := by
    simpa [prefixWord, tailWord_1157205, baseEnd_1157205] using wordTrace_append hprefix tailTrace_1157205
  have hstable : (prefixWord ++ tailWord_1157205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157205).length < 2 ^ (prefixWord ++ tailWord_1157205).sum := by decide
  have hdescent : baseEnd_1157205 < baseStart_1157205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157216 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 1, 2, 2]
def baseStart_1157216 : Nat := 118140960795 + 1157216 * 2 ^ 59
def prefixEnd_1157216 : Nat := 4983230072969 + 3 ^ 40 * 1157216 * 2
def baseEnd_1157216 : Nat := 594208029073449620778067

theorem tailTrace_1157216 : CollatzResearch.WordTrace tailWord_1157216 prefixEnd_1157216 594208029073449620778067 := by
  unfold tailWord_1157216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21103567487805771801621751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28138089983741029068829001 21103567487805771801621751)
  ·
    refine ⟨31655351231708657702432627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21103567487805771801621751 31655351231708657702432627)
    ·
      refine ⟨47483026847562986553648941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31655351231708657702432627 47483026847562986553648941)
      ·
        refine ⟨17806135067836119957618353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47483026847562986553648941 17806135067836119957618353)
        ·
          refine ⟨13354601300877089968213765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17806135067836119957618353 13354601300877089968213765)
          ·
            refine ⟨2503987743914454369040081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13354601300877089968213765 2503987743914454369040081)
            ·
              refine ⟨1877990807935840776780061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503987743914454369040081 1877990807935840776780061)
              ·
                refine ⟨704246552975940291292523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877990807935840776780061 704246552975940291292523)
                ·
                  refine ⟨1056369829463910436938785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704246552975940291292523 1056369829463910436938785)
                  ·
                    refine ⟨792277372097932827704089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056369829463910436938785 792277372097932827704089)
                    ·
                      refine ⟨594208029073449620778067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792277372097932827704089 594208029073449620778067)
                      ·
                        rfl

theorem cell23_1157216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_1157216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157216 prefixEnd_1157216 := by exact prefixLift 1157216
  have htrace : WordTrace (prefixWord ++ tailWord_1157216) baseStart_1157216 baseEnd_1157216 := by
    simpa [prefixWord, tailWord_1157216, baseEnd_1157216] using wordTrace_append hprefix tailTrace_1157216
  have hstable : (prefixWord ++ tailWord_1157216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157216).length < 2 ^ (prefixWord ++ tailWord_1157216).sum := by decide
  have hdescent : baseEnd_1157216 < baseStart_1157216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157226 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1157226 : Nat := 118140960795 + 1157226 * 2 ^ 59
def prefixEnd_1157226 : Nat := 4983230072969 + 3 ^ 40 * 1157226 * 2
def baseEnd_1157226 : Nat := 198071054626664860551007

theorem tailTrace_1157226 : CollatzResearch.WordTrace tailWord_1157226 prefixEnd_1157226 198071054626664860551007 := by
  unfold tailWord_1157226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10551874926393828827776883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28138333137050210207405021 10551874926393828827776883)
  ·
    refine ⟨15827812389590743241665325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10551874926393828827776883 15827812389590743241665325)
    ·
      refine ⟨5935429646096528715624497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15827812389590743241665325 5935429646096528715624497)
      ·
        refine ⟨4451572234572396536718373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5935429646096528715624497 4451572234572396536718373)
        ·
          refine ⟨834669793982324350634695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4451572234572396536718373 834669793982324350634695)
          ·
            refine ⟨1252004690973486525952043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834669793982324350634695 1252004690973486525952043)
            ·
              refine ⟨1878007036460229788928065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252004690973486525952043 1878007036460229788928065)
              ·
                refine ⟨1408505277345172341696049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878007036460229788928065 1408505277345172341696049)
                ·
                  refine ⟨1056378958008879256272037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408505277345172341696049 1056378958008879256272037)
                  ·
                    refine ⟨198071054626664860551007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056378958008879256272037 198071054626664860551007)
                    ·
                      rfl

theorem cell23_1157226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1157226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157226 prefixEnd_1157226 := by exact prefixLift 1157226
  have htrace : WordTrace (prefixWord ++ tailWord_1157226) baseStart_1157226 baseEnd_1157226 := by
    simpa [prefixWord, tailWord_1157226, baseEnd_1157226] using wordTrace_append hprefix tailTrace_1157226
  have hstable : (prefixWord ++ tailWord_1157226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157226).length < 2 ^ (prefixWord ++ tailWord_1157226).sum := by decide
  have hdescent : baseEnd_1157226 < baseStart_1157226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157232 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_1157232 : Nat := 118140960795 + 1157232 * 2 ^ 59
def prefixEnd_1157232 : Nat := 4983230072969 + 3 ^ 40 * 1157232 * 2
def baseEnd_1157232 : Nat := 594216244763921558177993

theorem tailTrace_1157232 : CollatzResearch.WordTrace tailWord_1157232 prefixEnd_1157232 594216244763921558177993 := by
  unfold tailWord_1157232
  simp only [CollatzResearch.WordTrace]
  refine ⟨21103859271776789167912975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28138479029035718890550633 21103859271776789167912975)
  ·
    refine ⟨31655788907665183751869463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21103859271776789167912975 31655788907665183751869463)
    ·
      refine ⟨47483683361497775627804195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31655788907665183751869463 47483683361497775627804195)
      ·
        refine ⟨71225525042246663441706293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47483683361497775627804195 71225525042246663441706293)
        ·
          refine ⟨6677392972710624697659965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71225525042246663441706293 6677392972710624697659965)
          ·
            refine ⟨2504022364766484261622487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6677392972710624697659965 2504022364766484261622487)
            ·
              refine ⟨3756033547149726392433731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504022364766484261622487 3756033547149726392433731)
              ·
                refine ⟨5634050320724589588650597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756033547149726392433731 5634050320724589588650597)
                ·
                  refine ⟨1056384435135860547871987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5634050320724589588650597 1056384435135860547871987)
                  ·
                    refine ⟨1584576652703790821807981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056384435135860547871987 1584576652703790821807981)
                    ·
                      refine ⟨594216244763921558177993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584576652703790821807981 594216244763921558177993)
                      ·
                        rfl

theorem cell23_1157232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_1157232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157232 prefixEnd_1157232 := by exact prefixLift 1157232
  have htrace : WordTrace (prefixWord ++ tailWord_1157232) baseStart_1157232 baseEnd_1157232 := by
    simpa [prefixWord, tailWord_1157232, baseEnd_1157232] using wordTrace_append hprefix tailTrace_1157232
  have hstable : (prefixWord ++ tailWord_1157232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157232).length < 2 ^ (prefixWord ++ tailWord_1157232).sum := by decide
  have hdescent : baseEnd_1157232 < baseStart_1157232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157249 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1157249 : Nat := 118140960795 + 1157249 * 2 ^ 59
def prefixEnd_1157249 : Nat := 4983230072969 + 3 ^ 40 * 1157249 * 2
def baseEnd_1157249 : Nat := 594224973935047991665415

theorem tailTrace_1157249 : CollatzResearch.WordTrace tailWord_1157249 prefixEnd_1157249 594224973935047991665415 := by
  unfold tailWord_1157249
  simp only [CollatzResearch.WordTrace]
  refine ⟨42208338584491990239194801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28138892389661326826129867 42208338584491990239194801)
  ·
    refine ⟨31656253938368992679396101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42208338584491990239194801 31656253938368992679396101)
    ·
      refine ⟨5935547613444186127386769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31656253938368992679396101 5935547613444186127386769)
      ·
        refine ⟨4451660710083139595540077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5935547613444186127386769 4451660710083139595540077)
        ·
          refine ⟨1669372766281177348327529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4451660710083139595540077 1669372766281177348327529)
          ·
            refine ⟨1252029574710883011245647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669372766281177348327529 1252029574710883011245647)
            ·
              refine ⟨1878044362066324516868471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252029574710883011245647 1878044362066324516868471)
              ·
                refine ⟨2817066543099486775302707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878044362066324516868471 2817066543099486775302707)
                ·
                  refine ⟨4225599814649230162954061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817066543099486775302707 4225599814649230162954061)
                  ·
                    refine ⟨1584599930493461311107773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4225599814649230162954061 1584599930493461311107773)
                    ·
                      refine ⟨594224973935047991665415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584599930493461311107773 594224973935047991665415)
                      ·
                        rfl

theorem cell23_1157249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1157249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157249 prefixEnd_1157249 := by exact prefixLift 1157249
  have htrace : WordTrace (prefixWord ++ tailWord_1157249) baseStart_1157249 baseEnd_1157249 := by
    simpa [prefixWord, tailWord_1157249, baseEnd_1157249] using wordTrace_append hprefix tailTrace_1157249
  have hstable : (prefixWord ++ tailWord_1157249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157249).length < 2 ^ (prefixWord ++ tailWord_1157249).sum := by decide
  have hdescent : baseEnd_1157249 < baseStart_1157249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157300 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1157300 : Nat := 118140960795 + 1157300 * 2 ^ 59
def prefixEnd_1157300 : Nat := 4983230072969 + 3 ^ 40 * 1157300 * 2
def baseEnd_1157300 : Nat := 594251161448427292127681

theorem tailTrace_1157300 : CollatzResearch.WordTrace tailWord_1157300 prefixEnd_1157300 594251161448427292127681 := by
  unfold tailWord_1157300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105099353653612974650677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28140132471538150632867569 21105099353653612974650677)
  ·
    refine ⟨1978603064405026216373501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21105099353653612974650677 1978603064405026216373501)
    ·
      refine ⟨741976149151884831140063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1978603064405026216373501 741976149151884831140063)
      ·
        refine ⟨1112964223727827246710095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741976149151884831140063 1112964223727827246710095)
        ·
          refine ⟨1669446335591740870065143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112964223727827246710095 1669446335591740870065143)
          ·
            refine ⟨2504169503387611305097715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669446335591740870065143 2504169503387611305097715)
            ·
              refine ⟨3756254255081416957646573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504169503387611305097715 3756254255081416957646573)
              ·
                refine ⟨1408595345655531359117465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756254255081416957646573 1408595345655531359117465)
                ·
                  refine ⟨1056446509241648519338099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408595345655531359117465 1056446509241648519338099)
                  ·
                    refine ⟨1584669763862472779007149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056446509241648519338099 1584669763862472779007149)
                    ·
                      refine ⟨594251161448427292127681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584669763862472779007149 594251161448427292127681)
                      ·
                        rfl

theorem cell23_1157300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1157300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157300 prefixEnd_1157300 := by exact prefixLift 1157300
  have htrace : WordTrace (prefixWord ++ tailWord_1157300) baseStart_1157300 baseEnd_1157300 := by
    simpa [prefixWord, tailWord_1157300, baseEnd_1157300] using wordTrace_append hprefix tailTrace_1157300
  have hstable : (prefixWord ++ tailWord_1157300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157300).length < 2 ^ (prefixWord ++ tailWord_1157300).sum := by decide
  have hdescent : baseEnd_1157300 < baseStart_1157300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157305 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1157305 : Nat := 118140960795 + 1157305 * 2 ^ 59
def prefixEnd_1157305 : Nat := 4983230072969 + 3 ^ 40 * 1157305 * 2
def baseEnd_1157305 : Nat := 594253728851699772565157

theorem tailTrace_1157305 : CollatzResearch.WordTrace tailWord_1157305 prefixEnd_1157305 594253728851699772565157 := by
  unfold tailWord_1157305
  simp only [CollatzResearch.WordTrace]
  refine ⟨42210381072289111803233369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28140254048192741202155579 42210381072289111803233369)
  ·
    refine ⟨31657785804216833852425027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42210381072289111803233369 31657785804216833852425027)
    ·
      refine ⟨47486678706325250778637541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31657785804216833852425027 47486678706325250778637541)
      ·
        refine ⟨8903752257435984520994539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47486678706325250778637541 8903752257435984520994539)
        ·
          refine ⟨13355628386153976781491809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8903752257435984520994539 13355628386153976781491809)
          ·
            refine ⟨10016721289615482586118857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13355628386153976781491809 10016721289615482586118857)
            ·
              refine ⟨7512540967211611939589143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016721289615482586118857 7512540967211611939589143)
              ·
                refine ⟨11268811450817417909383715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512540967211611939589143 11268811450817417909383715)
                ·
                  refine ⟨16903217176226126864075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11268811450817417909383715 16903217176226126864075573)
                  ·
                    refine ⟨1584676610271199393507085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16903217176226126864075573 1584676610271199393507085)
                    ·
                      refine ⟨594253728851699772565157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584676610271199393507085 594253728851699772565157)
                      ·
                        rfl

theorem cell23_1157305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1157305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157305 prefixEnd_1157305 := by exact prefixLift 1157305
  have htrace : WordTrace (prefixWord ++ tailWord_1157305) baseStart_1157305 baseEnd_1157305 := by
    simpa [prefixWord, tailWord_1157305, baseEnd_1157305] using wordTrace_append hprefix tailTrace_1157305
  have hstable : (prefixWord ++ tailWord_1157305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157305).length < 2 ^ (prefixWord ++ tailWord_1157305).sum := by decide
  have hdescent : baseEnd_1157305 < baseStart_1157305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157306 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_1157306 : Nat := 118140960795 + 1157306 * 2 ^ 59
def prefixEnd_1157306 : Nat := 4983230072969 + 3 ^ 40 * 1157306 * 2
def baseEnd_1157306 : Nat := 594254242332354268652653

theorem tailTrace_1157306 : CollatzResearch.WordTrace tailWord_1157306 prefixEnd_1157306 594254242332354268652653 := by
  unfold tailWord_1157306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10552604386321372243504943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28140278363523659316013181 10552604386321372243504943)
  ·
    refine ⟨15828906579482058365257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10552604386321372243504943 15828906579482058365257415)
    ·
      refine ⟨23743359869223087547886123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15828906579482058365257415 23743359869223087547886123)
      ·
        refine ⟨35615039803834631321829185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23743359869223087547886123 35615039803834631321829185)
        ·
          refine ⟨26711279852875973491371889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35615039803834631321829185 26711279852875973491371889)
          ·
            refine ⟨20033459889656980118528917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26711279852875973491371889 20033459889656980118528917)
            ·
              refine ⟨939068432327670943056043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20033459889656980118528917 939068432327670943056043)
              ·
                refine ⟨1408602648491506414584065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939068432327670943056043 1408602648491506414584065)
                ·
                  refine ⟨1056451986368629810938049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408602648491506414584065 1056451986368629810938049)
                  ·
                    refine ⟨792338989776472358203537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056451986368629810938049 792338989776472358203537)
                    ·
                      refine ⟨594254242332354268652653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792338989776472358203537 594254242332354268652653)
                      ·
                        rfl

theorem cell23_1157306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_1157306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157306 prefixEnd_1157306 := by exact prefixLift 1157306
  have htrace : WordTrace (prefixWord ++ tailWord_1157306) baseStart_1157306 baseEnd_1157306 := by
    simpa [prefixWord, tailWord_1157306, baseEnd_1157306] using wordTrace_append hprefix tailTrace_1157306
  have hstable : (prefixWord ++ tailWord_1157306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157306).length < 2 ^ (prefixWord ++ tailWord_1157306).sum := by decide
  have hdescent : baseEnd_1157306 < baseStart_1157306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157340 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1157340 : Nat := 118140960795 + 1157340 * 2 ^ 59
def prefixEnd_1157340 : Nat := 4983230072969 + 3 ^ 40 * 1157340 * 2
def baseEnd_1157340 : Nat := 594271700674607135627497

theorem tailTrace_1157340 : CollatzResearch.WordTrace tailWord_1157340 prefixEnd_1157340 594271700674607135627497 := by
  unfold tailWord_1157340
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105828813581156390378737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28141105084774875187171649 21105828813581156390378737)
  ·
    refine ⟨15829371610185867292784053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21105828813581156390378737 15829371610185867292784053)
    ·
      refine ⟨1484003588454925058698505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15829371610185867292784053 1484003588454925058698505)
      ·
        refine ⟨1113002691341193794023879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484003588454925058698505 1113002691341193794023879)
        ·
          refine ⟨1669504037011790691035819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113002691341193794023879 1669504037011790691035819)
          ·
            refine ⟨2504256055517686036553729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669504037011790691035819 2504256055517686036553729)
            ·
              refine ⟨1878192041638264527415297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504256055517686036553729 1878192041638264527415297)
              ·
                refine ⟨1408644031228698395561473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878192041638264527415297 1408644031228698395561473)
                ·
                  refine ⟨1056483023421523796671105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408644031228698395561473 1056483023421523796671105)
                  ·
                    refine ⟨792362267566142847503329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056483023421523796671105 792362267566142847503329)
                    ·
                      refine ⟨594271700674607135627497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792362267566142847503329 594271700674607135627497)
                      ·
                        rfl

theorem cell23_1157340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1157340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157340 prefixEnd_1157340 := by exact prefixLift 1157340
  have htrace : WordTrace (prefixWord ++ tailWord_1157340) baseStart_1157340 baseEnd_1157340 := by
    simpa [prefixWord, tailWord_1157340, baseEnd_1157340] using wordTrace_append hprefix tailTrace_1157340
  have hstable : (prefixWord ++ tailWord_1157340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157340).length < 2 ^ (prefixWord ++ tailWord_1157340).sum := by decide
  have hdescent : baseEnd_1157340 < baseStart_1157340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157372 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1157372 : Nat := 118140960795 + 1157372 * 2 ^ 59
def prefixEnd_1157372 : Nat := 4983230072969 + 3 ^ 40 * 1157372 * 2
def baseEnd_1157372 : Nat := 198096044018517003475783

theorem tailTrace_1157372 : CollatzResearch.WordTrace tailWord_1157372 prefixEnd_1157372 198096044018517003475783 := by
  unfold tailWord_1157372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106412381523191122961185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28141883175364254830614913 21106412381523191122961185)
  ·
    refine ⟨15829809286142393342220889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21106412381523191122961185 15829809286142393342220889)
    ·
      refine ⟨11872356964606795006665667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15829809286142393342220889 11872356964606795006665667)
      ·
        refine ⟨17808535446910192509998501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11872356964606795006665667 17808535446910192509998501)
        ·
          refine ⟨3339100396295661095624719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17808535446910192509998501 3339100396295661095624719)
          ·
            refine ⟨5008650594443491643437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339100396295661095624719 5008650594443491643437079)
            ·
              refine ⟨7512975891665237465155619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008650594443491643437079 7512975891665237465155619)
              ·
                refine ⟨11269463837497856197733429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512975891665237465155619 11269463837497856197733429)
                ·
                  refine ⟨1056512234765424018537509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11269463837497856197733429 1056512234765424018537509)
                  ·
                    refine ⟨198096044018517003475783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056512234765424018537509 198096044018517003475783)
                    ·
                      rfl

theorem cell23_1157372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1157372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157372 prefixEnd_1157372 := by exact prefixLift 1157372
  have htrace : WordTrace (prefixWord ++ tailWord_1157372) baseStart_1157372 baseEnd_1157372 := by
    simpa [prefixWord, tailWord_1157372, baseEnd_1157372] using wordTrace_append hprefix tailTrace_1157372
  have hstable : (prefixWord ++ tailWord_1157372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157372).length < 2 ^ (prefixWord ++ tailWord_1157372).sum := by decide
  have hdescent : baseEnd_1157372 < baseStart_1157372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157395 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3]
def baseStart_1157395 : Nat := 118140960795 + 1157395 * 2 ^ 59
def prefixEnd_1157395 : Nat := 4983230072969 + 3 ^ 40 * 1157395 * 2
def baseEnd_1157395 : Nat := 594299942110604420439743

theorem tailTrace_1157395 : CollatzResearch.WordTrace tailWord_1157395 prefixEnd_1157395 594299942110604420439743 := by
  unfold tailWord_1157395
  simp only [CollatzResearch.WordTrace]
  refine ⟨42213663641963057174009639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28142442427975371449339759 42213663641963057174009639)
  ·
    refine ⟨63320495462944585761014459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42213663641963057174009639 63320495462944585761014459)
    ·
      refine ⟨94980743194416878641521689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63320495462944585761014459 94980743194416878641521689)
      ·
        refine ⟨71235557395812658981141267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94980743194416878641521689 71235557395812658981141267)
        ·
          refine ⟨106853336093718988471711901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71235557395812658981141267 106853336093718988471711901)
          ·
            refine ⟨40070001035144620676891963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106853336093718988471711901 40070001035144620676891963)
            ·
              refine ⟨60105001552716931015337945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40070001035144620676891963 60105001552716931015337945)
              ·
                refine ⟨45078751164537698261503459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60105001552716931015337945 45078751164537698261503459)
                ·
                  refine ⟨67618126746806547392255189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45078751164537698261503459 67618126746806547392255189)
                  ·
                    refine ⟨1584799845628278454505981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67618126746806547392255189 1584799845628278454505981)
                    ·
                      refine ⟨594299942110604420439743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584799845628278454505981 594299942110604420439743)
                      ·
                        rfl

theorem cell23_1157395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_1157395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157395 prefixEnd_1157395 := by exact prefixLift 1157395
  have htrace : WordTrace (prefixWord ++ tailWord_1157395) baseStart_1157395 baseEnd_1157395 := by
    simpa [prefixWord, tailWord_1157395, baseEnd_1157395] using wordTrace_append hprefix tailTrace_1157395
  have hstable : (prefixWord ++ tailWord_1157395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157395).length < 2 ^ (prefixWord ++ tailWord_1157395).sum := by decide
  have hdescent : baseEnd_1157395 < baseStart_1157395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157402 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_1157402 : Nat := 118140960795 + 1157402 * 2 ^ 59
def prefixEnd_1157402 : Nat := 4983230072969 + 3 ^ 40 * 1157402 * 2
def baseEnd_1157402 : Nat := 66033726275020654783579

theorem tailTrace_1157402 : CollatzResearch.WordTrace tailWord_1157402 prefixEnd_1157402 66033726275020654783579 := by
  unfold tailWord_1157402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553479738234424342378615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28142612635291798246342973 10553479738234424342378615)
  ·
    refine ⟨15830219607351636513567923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10553479738234424342378615 15830219607351636513567923)
    ·
      refine ⟨23745329411027454770351885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15830219607351636513567923 23745329411027454770351885)
      ·
        refine ⟨8904498529135295538881957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23745329411027454770351885 8904498529135295538881957)
        ·
          refine ⟨1669593474212867913540367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8904498529135295538881957 1669593474212867913540367)
          ·
            refine ⟨2504390211319301870310551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669593474212867913540367 2504390211319301870310551)
            ·
              refine ⟨3756585316978952805465827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504390211319301870310551 3756585316978952805465827)
              ·
                refine ⟨5634877975468429208198741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756585316978952805465827 5634877975468429208198741)
                ·
                  refine ⟨66033726275020654783579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5634877975468429208198741 66033726275020654783579)
                  ·
                    rfl

theorem cell23_1157402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_1157402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157402 prefixEnd_1157402 := by exact prefixLift 1157402
  have htrace : WordTrace (prefixWord ++ tailWord_1157402) baseStart_1157402 baseEnd_1157402 := by
    simpa [prefixWord, tailWord_1157402, baseEnd_1157402] using wordTrace_append hprefix tailTrace_1157402
  have hstable : (prefixWord ++ tailWord_1157402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157402).length < 2 ^ (prefixWord ++ tailWord_1157402).sum := by decide
  have hdescent : baseEnd_1157402 < baseStart_1157402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157406 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1157406 : Nat := 118140960795 + 1157406 * 2 ^ 59
def prefixEnd_1157406 : Nat := 4983230072969 + 3 ^ 40 * 1157406 * 2
def baseEnd_1157406 : Nat := 198101863465934625800731

theorem tailTrace_1157406 : CollatzResearch.WordTrace tailWord_1157406 prefixEnd_1157406 198101863465934625800731 := by
  unfold tailWord_1157406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276758105615400756582509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28142709896615470701773381 5276758105615400756582509)
  ·
    refine ⟨1978784289605775283718441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5276758105615400756582509 1978784289605775283718441)
    ·
      refine ⟨1484088217204331462788831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1978784289605775283718441 1484088217204331462788831)
      ·
        refine ⟨2226132325806497194183247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484088217204331462788831 2226132325806497194183247)
        ·
          refine ⟨3339198488709745791274871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226132325806497194183247 3339198488709745791274871)
          ·
            refine ⟨5008797733064618686912307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339198488709745791274871 5008797733064618686912307)
            ·
              refine ⟨7513196599596928030368461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008797733064618686912307 7513196599596928030368461)
              ·
                refine ⟨2817448724848848011388173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7513196599596928030368461 2817448724848848011388173)
                ·
                  refine ⟨1056543271818318004270565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2817448724848848011388173 1056543271818318004270565)
                  ·
                    refine ⟨198101863465934625800731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1056543271818318004270565 198101863465934625800731)
                    ·
                      rfl

theorem cell23_1157406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1157406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157406 prefixEnd_1157406 := by exact prefixLift 1157406
  have htrace : WordTrace (prefixWord ++ tailWord_1157406) baseStart_1157406 baseEnd_1157406 := by
    simpa [prefixWord, tailWord_1157406, baseEnd_1157406] using wordTrace_append hprefix tailTrace_1157406
  have hstable : (prefixWord ++ tailWord_1157406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157406).length < 2 ^ (prefixWord ++ tailWord_1157406).sum := by decide
  have hdescent : baseEnd_1157406 < baseStart_1157406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157429 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1157429 : Nat := 118140960795 + 1157429 * 2 ^ 59
def prefixEnd_1157429 : Nat := 4983230072969 + 3 ^ 40 * 1157429 * 2
def baseEnd_1157429 : Nat := 594317400452857287414587

theorem tailTrace_1157429 : CollatzResearch.WordTrace tailWord_1157429 prefixEnd_1157429 594317400452857287414587 := by
  unfold tailWord_1157429
  simp only [CollatzResearch.WordTrace]
  refine ⟨42214903723839880980747341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28143269149226587320498227 42214903723839880980747341)
  ·
    refine ⟨15830588896439955367780253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42214903723839880980747341 15830588896439955367780253)
    ·
      refine ⟨5936470836164983262917595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15830588896439955367780253 5936470836164983262917595)
      ·
        refine ⟨8904706254247474894376393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936470836164983262917595 8904706254247474894376393)
        ·
          refine ⟨6678529690685606170782295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8904706254247474894376393 6678529690685606170782295)
          ·
            refine ⟨10017794536028409256173443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678529690685606170782295 10017794536028409256173443)
            ·
              refine ⟨15026691804042613884260165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10017794536028409256173443 15026691804042613884260165)
              ·
                refine ⟨2817504713257990103298781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15026691804042613884260165 2817504713257990103298781)
                ·
                  refine ⟨1056564267471746288737043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2817504713257990103298781 1056564267471746288737043)
                  ·
                    refine ⟨1584846401207619433105565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056564267471746288737043 1584846401207619433105565)
                    ·
                      refine ⟨594317400452857287414587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584846401207619433105565 594317400452857287414587)
                      ·
                        rfl

theorem cell23_1157429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1157429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157429 prefixEnd_1157429 := by exact prefixLift 1157429
  have htrace : WordTrace (prefixWord ++ tailWord_1157429) baseStart_1157429 baseEnd_1157429 := by
    simpa [prefixWord, tailWord_1157429, baseEnd_1157429] using wordTrace_append hprefix tailTrace_1157429
  have hstable : (prefixWord ++ tailWord_1157429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157429).length < 2 ^ (prefixWord ++ tailWord_1157429).sum := by decide
  have hdescent : baseEnd_1157429 < baseStart_1157429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157432 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_1157432 : Nat := 118140960795 + 1157432 * 2 ^ 59
def prefixEnd_1157432 : Nat := 4983230072969 + 3 ^ 40 * 1157432 * 2
def baseEnd_1157432 : Nat := 198106313631606925225691

theorem tailTrace_1157432 : CollatzResearch.WordTrace tailWord_1157432 prefixEnd_1157432 198106313631606925225691 := by
  unfold tailWord_1157432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21107506571414506246553275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28143342095219341662071033 21107506571414506246553275)
  ·
    refine ⟨31661259857121759369829913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21107506571414506246553275 31661259857121759369829913)
    ·
      refine ⟨23745944892841319527372435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31661259857121759369829913 23745944892841319527372435)
      ·
        refine ⟨35618917339261979291058653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745944892841319527372435 35618917339261979291058653)
        ·
          refine ⟨13357094002223242234146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35618917339261979291058653 13357094002223242234146995)
          ·
            refine ⟨20035641003334863351220493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13357094002223242234146995 20035641003334863351220493)
            ·
              refine ⟨7513365376250573756707685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20035641003334863351220493 7513365376250573756707685)
              ·
                refine ⟨1408756008046982579382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7513365376250573756707685 1408756008046982579382691)
                ·
                  refine ⟨2113134012070473869074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408756008046982579382691 2113134012070473869074037)
                  ·
                    refine ⟨198106313631606925225691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2113134012070473869074037 198106313631606925225691)
                    ·
                      rfl

theorem cell23_1157432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_1157432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157432 prefixEnd_1157432 := by exact prefixLift 1157432
  have htrace : WordTrace (prefixWord ++ tailWord_1157432) baseStart_1157432 baseEnd_1157432 := by
    simpa [prefixWord, tailWord_1157432, baseEnd_1157432] using wordTrace_append hprefix tailTrace_1157432
  have hstable : (prefixWord ++ tailWord_1157432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157432).length < 2 ^ (prefixWord ++ tailWord_1157432).sum := by decide
  have hdescent : baseEnd_1157432 < baseStart_1157432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157439 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 2, 3, 2]
def baseStart_1157439 : Nat := 118140960795 + 1157439 * 2 ^ 59
def prefixEnd_1157439 : Nat := 4983230072969 + 3 ^ 40 * 1157439 * 2
def baseEnd_1157439 : Nat := 594322535259402248289541

theorem tailTrace_1157439 : CollatzResearch.WordTrace tailWord_1157439 prefixEnd_1157439 594322535259402248289541 := by
  unfold tailWord_1157439
  simp only [CollatzResearch.WordTrace]
  refine ⟨42215268453803652688611371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28143512302535768459074247 42215268453803652688611371)
  ·
    refine ⟨63322902680705479032917057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42215268453803652688611371 63322902680705479032917057)
    ·
      refine ⟨47492177010529109274687793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63322902680705479032917057 47492177010529109274687793)
      ·
        refine ⟨35619132757896831956015845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47492177010529109274687793 35619132757896831956015845)
        ·
          refine ⟨6678587392105655991752971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35619132757896831956015845 6678587392105655991752971)
          ·
            refine ⟨10017881088158483987629457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678587392105655991752971 10017881088158483987629457)
            ·
              refine ⟨7513410816118862990722093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10017881088158483987629457 7513410816118862990722093)
              ·
                refine ⟨2817529056044573621520785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7513410816118862990722093 2817529056044573621520785)
                ·
                  refine ⟨2113146792033430216140589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817529056044573621520785 2113146792033430216140589)
                  ·
                    refine ⟨792430047012536331052721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113146792033430216140589 792430047012536331052721)
                    ·
                      refine ⟨594322535259402248289541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792430047012536331052721 594322535259402248289541)
                      ·
                        rfl

theorem cell23_1157439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_1157439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157439 prefixEnd_1157439 := by exact prefixLift 1157439
  have htrace : WordTrace (prefixWord ++ tailWord_1157439) baseStart_1157439 baseEnd_1157439 := by
    simpa [prefixWord, tailWord_1157439, baseEnd_1157439] using wordTrace_append hprefix tailTrace_1157439
  have hstable : (prefixWord ++ tailWord_1157439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157439).length < 2 ^ (prefixWord ++ tailWord_1157439).sum := by decide
  have hdescent : baseEnd_1157439 < baseStart_1157439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157463 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_1157463 : Nat := 118140960795 + 1157463 * 2 ^ 59
def prefixEnd_1157463 : Nat := 4983230072969 + 3 ^ 40 * 1157463 * 2
def baseEnd_1157463 : Nat := 594334858795110154389431

theorem tailTrace_1157463 : CollatzResearch.WordTrace tailWord_1157463 prefixEnd_1157463 594334858795110154389431 := by
  unfold tailWord_1157463
  simp only [CollatzResearch.WordTrace]
  refine ⟨42216143805716704787485043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28144095870477803191656695 42216143805716704787485043)
  ·
    refine ⟨63324215708575057181227565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42216143805716704787485043 63324215708575057181227565)
    ·
      refine ⟨23746580890715646442960337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63324215708575057181227565 23746580890715646442960337)
      ·
        refine ⟨17809935668036734832220253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23746580890715646442960337 17809935668036734832220253)
        ·
          refine ⟨6678725875513775562082595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17809935668036734832220253 6678725875513775562082595)
          ·
            refine ⟨10018088813270663343123893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678725875513775562082595 10018088813270663343123893)
            ·
              refine ⟨939195826244124688417865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10018088813270663343123893 939195826244124688417865)
              ·
                refine ⟨704396869683093516313399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939195826244124688417865 704396869683093516313399)
                ·
                  refine ⟨1056595304524640274470099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704396869683093516313399 1056595304524640274470099)
                  ·
                    refine ⟨1584892956786960411705149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056595304524640274470099 1584892956786960411705149)
                    ·
                      refine ⟨594334858795110154389431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584892956786960411705149 594334858795110154389431)
                      ·
                        rfl

theorem cell23_1157463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_1157463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157463 prefixEnd_1157463 := by exact prefixLift 1157463
  have htrace : WordTrace (prefixWord ++ tailWord_1157463) baseStart_1157463 baseEnd_1157463 := by
    simpa [prefixWord, tailWord_1157463, baseEnd_1157463] using wordTrace_append hprefix tailTrace_1157463
  have hstable : (prefixWord ++ tailWord_1157463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157463).length < 2 ^ (prefixWord ++ tailWord_1157463).sum := by decide
  have hdescent : baseEnd_1157463 < baseStart_1157463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157470 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1157470 : Nat := 118140960795 + 1157470 * 2 ^ 59
def prefixEnd_1157470 : Nat := 4983230072969 + 3 ^ 40 * 1157470 * 2
def baseEnd_1157470 : Nat := 66037605906632403000211

theorem tailTrace_1157470 : CollatzResearch.WordTrace tailWord_1157470 prefixEnd_1157470 66037605906632403000211 := by
  unfold tailWord_1157470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277049889586418122873733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28144266077794229988659909 5277049889586418122873733)
  ·
    refine ⟨989446854297453398038825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5277049889586418122873733 989446854297453398038825)
    ·
      refine ⟨742085140723090048529119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 989446854297453398038825 742085140723090048529119)
      ·
        refine ⟨1113127711084635072793679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742085140723090048529119 1113127711084635072793679)
        ·
          refine ⟨1669691566626952609190519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113127711084635072793679 1669691566626952609190519)
          ·
            refine ⟨2504537349940428913785779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669691566626952609190519 2504537349940428913785779)
            ·
              refine ⟨3756806024910643370678669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504537349940428913785779 3756806024910643370678669)
              ·
                refine ⟨1408802259341491264004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3756806024910643370678669 1408802259341491264004501)
                ·
                  refine ⟨66037605906632403000211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1408802259341491264004501 66037605906632403000211)
                  ·
                    rfl

theorem cell23_1157470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1157470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157470 prefixEnd_1157470 := by exact prefixLift 1157470
  have htrace : WordTrace (prefixWord ++ tailWord_1157470) baseStart_1157470 baseEnd_1157470 := by
    simpa [prefixWord, tailWord_1157470, baseEnd_1157470] using wordTrace_append hprefix tailTrace_1157470
  have hstable : (prefixWord ++ tailWord_1157470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157470).length < 2 ^ (prefixWord ++ tailWord_1157470).sum := by decide
  have hdescent : baseEnd_1157470 < baseStart_1157470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157514 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1157514 : Nat := 118140960795 + 1157514 * 2 ^ 59
def prefixEnd_1157514 : Nat := 4983230072969 + 3 ^ 40 * 1157514 * 2
def baseEnd_1157514 : Nat := 594361046308489454851697

theorem tailTrace_1157514 : CollatzResearch.WordTrace tailWord_1157514 prefixEnd_1157514 594361046308489454851697 := by
  unfold tailWord_1157514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554500982132985124397899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28145335952354626998394397 10554500982132985124397899)
  ·
    refine ⟨15831751473199477686596849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554500982132985124397899 15831751473199477686596849)
    ·
      refine ⟨11873813604899608264947637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15831751473199477686596849 11873813604899608264947637)
      ·
        refine ⟨1113170025459338274838841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11873813604899608264947637 1113170025459338274838841)
        ·
          refine ⟨834877519094503706129131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113170025459338274838841 834877519094503706129131)
          ·
            refine ⟨1252316278641755559193697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834877519094503706129131 1252316278641755559193697)
            ·
              refine ⟨939237208981316669395273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252316278641755559193697 939237208981316669395273)
              ·
                refine ⟨704427906735987502046455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939237208981316669395273 704427906735987502046455)
                ·
                  refine ⟨1056641860103981253069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704427906735987502046455 1056641860103981253069683)
                  ·
                    refine ⟨1584962790155971879604525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056641860103981253069683 1584962790155971879604525)
                    ·
                      refine ⟨594361046308489454851697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584962790155971879604525 594361046308489454851697)
                      ·
                        rfl

theorem cell23_1157514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1157514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157514 prefixEnd_1157514 := by exact prefixLift 1157514
  have htrace : WordTrace (prefixWord ++ tailWord_1157514) baseStart_1157514 baseEnd_1157514 := by
    simpa [prefixWord, tailWord_1157514, baseEnd_1157514] using wordTrace_append hprefix tailTrace_1157514
  have hstable : (prefixWord ++ tailWord_1157514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157514).length < 2 ^ (prefixWord ++ tailWord_1157514).sum := by decide
  have hdescent : baseEnd_1157514 < baseStart_1157514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157529 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 5, 3, 2]
def baseStart_1157529 : Nat := 118140960795 + 1157529 * 2 ^ 59
def prefixEnd_1157529 : Nat := 4983230072969 + 3 ^ 40 * 1157529 * 2
def baseEnd_1157529 : Nat := 594368748518306896164127

theorem tailTrace_1157529 : CollatzResearch.WordTrace tailWord_1157529 prefixEnd_1157529 594368748518306896164127 := by
  unfold tailWord_1157529
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218551023477598059387641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28145700682318398706258427 42218551023477598059387641)
  ·
    refine ⟨31663913267608198544540731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42218551023477598059387641 31663913267608198544540731)
    ·
      refine ⟨47495869901412297816811097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31663913267608198544540731 47495869901412297816811097)
      ·
        refine ⟨35621902426059223362608323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47495869901412297816811097 35621902426059223362608323)
        ·
          refine ⟨53432853639088835043912485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35621902426059223362608323 53432853639088835043912485)
          ·
            refine ⟨10018660057329156570733591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53432853639088835043912485 10018660057329156570733591)
            ·
              refine ⟨15027990085993734856100387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10018660057329156570733591 15027990085993734856100387)
              ·
                refine ⟨22541985128990602284150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15027990085993734856100387 22541985128990602284150581)
                ·
                  refine ⟨2113311105842868964139117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22541985128990602284150581 2113311105842868964139117)
                  ·
                    refine ⟨792491664691075861552169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2113311105842868964139117 792491664691075861552169)
                    ·
                      refine ⟨594368748518306896164127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792491664691075861552169 594368748518306896164127)
                      ·
                        rfl

theorem cell23_1157529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_1157529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157529 prefixEnd_1157529 := by exact prefixLift 1157529
  have htrace : WordTrace (prefixWord ++ tailWord_1157529) baseStart_1157529 baseEnd_1157529 := by
    simpa [prefixWord, tailWord_1157529, baseEnd_1157529] using wordTrace_append hprefix tailTrace_1157529
  have hstable : (prefixWord ++ tailWord_1157529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157529).length < 2 ^ (prefixWord ++ tailWord_1157529).sum := by decide
  have hdescent : baseEnd_1157529 < baseStart_1157529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157536 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1157536 : Nat := 118140960795 + 1157536 * 2 ^ 59
def prefixEnd_1157536 : Nat := 4983230072969 + 3 ^ 40 * 1157536 * 2
def baseEnd_1157536 : Nat := 594372342882888368776595

theorem tailTrace_1157536 : CollatzResearch.WordTrace tailWord_1157536 prefixEnd_1157536 594372342882888368776595 := by
  unfold tailWord_1157536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21109403167226119127446231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28145870889634825503261641 21109403167226119127446231)
  ·
    refine ⟨31664104750839178691169347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21109403167226119127446231 31664104750839178691169347)
    ·
      refine ⟨47496157126258768036754021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31664104750839178691169347 47496157126258768036754021)
      ·
        refine ⟨8905529461173519006891379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47496157126258768036754021 8905529461173519006891379)
        ·
          refine ⟨13358294191760278510337069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8905529461173519006891379 13358294191760278510337069)
          ·
            refine ⟨5009360321910104441376401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13358294191760278510337069 5009360321910104441376401)
            ·
              refine ⟨3757020241432578331032301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009360321910104441376401 3757020241432578331032301)
              ·
                refine ⟨1408882590537216874137113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3757020241432578331032301 1408882590537216874137113)
                ·
                  refine ⟨1056661942902912655602835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408882590537216874137113 1056661942902912655602835)
                  ·
                    refine ⟨1584992914354368983404253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056661942902912655602835 1584992914354368983404253)
                    ·
                      refine ⟨594372342882888368776595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1584992914354368983404253 594372342882888368776595)
                      ·
                        rfl

theorem cell23_1157536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1157536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157536 prefixEnd_1157536 := by exact prefixLift 1157536
  have htrace : WordTrace (prefixWord ++ tailWord_1157536) baseStart_1157536 baseEnd_1157536 := by
    simpa [prefixWord, tailWord_1157536, baseEnd_1157536] using wordTrace_append hprefix tailTrace_1157536
  have hstable : (prefixWord ++ tailWord_1157536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157536).length < 2 ^ (prefixWord ++ tailWord_1157536).sum := by decide
  have hdescent : baseEnd_1157536 < baseStart_1157536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157562 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1157562 : Nat := 118140960795 + 1157562 * 2 ^ 59
def prefixEnd_1157562 : Nat := 4983230072969 + 3 ^ 40 * 1157562 * 2
def baseEnd_1157562 : Nat := 594385693379905267051475

theorem tailTrace_1157562 : CollatzResearch.WordTrace tailWord_1157562 prefixEnd_1157562 594385693379905267051475 := by
  unfold tailWord_1157562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554938658089511173834735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28146503088238696463559293 10554938658089511173834735)
  ·
    refine ⟨15832407987134266760752103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554938658089511173834735 15832407987134266760752103)
    ·
      refine ⟨23748611980701400141128155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15832407987134266760752103 23748611980701400141128155)
      ·
        refine ⟨35622917971052100211692233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23748611980701400141128155 35622917971052100211692233)
        ·
          refine ⟨26717188478289075158769175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35622917971052100211692233 26717188478289075158769175)
          ·
            refine ⟨40075782717433612738153763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26717188478289075158769175 40075782717433612738153763)
            ·
              refine ⟨60113674076150419107230645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40075782717433612738153763 60113674076150419107230645)
              ·
                refine ⟨5635656944639101791302873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60113674076150419107230645 5635656944639101791302873)
                ·
                  refine ⟨4226742708479326343477155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635656944639101791302873 4226742708479326343477155)
                  ·
                    refine ⟨6340114062718989515215733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226742708479326343477155 6340114062718989515215733)
                    ·
                      refine ⟨594385693379905267051475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6340114062718989515215733 594385693379905267051475)
                      ·
                        rfl

theorem cell23_1157562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1157562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157562 prefixEnd_1157562 := by exact prefixLift 1157562
  have htrace : WordTrace (prefixWord ++ tailWord_1157562) baseStart_1157562 baseEnd_1157562 := by
    simpa [prefixWord, tailWord_1157562, baseEnd_1157562] using wordTrace_append hprefix tailTrace_1157562
  have hstable : (prefixWord ++ tailWord_1157562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157562).length < 2 ^ (prefixWord ++ tailWord_1157562).sum := by decide
  have hdescent : baseEnd_1157562 < baseStart_1157562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157589 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1157589 : Nat := 118140960795 + 1157589 * 2 ^ 59
def prefixEnd_1157589 : Nat := 4983230072969 + 3 ^ 40 * 1157589 * 2
def baseEnd_1157589 : Nat := 594399557357576661413851

theorem tailTrace_1157589 : CollatzResearch.WordTrace tailWord_1157589 prefixEnd_1157589 594399557357576661413851 := by
  unfold tailWord_1157589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42220739403260228306571821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28147159602173485537714547 42220739403260228306571821)
  ·
    refine ⟨15832777276222585614964433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42220739403260228306571821 15832777276222585614964433)
    ·
      refine ⟨11874582957166939211223325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15832777276222585614964433 11874582957166939211223325)
      ·
        refine ⟨4452968608937602204208747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11874582957166939211223325 4452968608937602204208747)
        ·
          refine ⟨6679452913406403306313121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452968608937602204208747 6679452913406403306313121)
          ·
            refine ⟨5009589685054802479734841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679452913406403306313121 5009589685054802479734841)
            ·
              refine ⟨3757192263791101859801131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009589685054802479734841 3757192263791101859801131)
              ·
                refine ⟨5635788395686652789701697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757192263791101859801131 5635788395686652789701697)
                ·
                  refine ⟨4226841296764989592276273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635788395686652789701697 4226841296764989592276273)
                  ·
                    refine ⟨3170130972573742194207205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226841296764989592276273 3170130972573742194207205)
                    ·
                      refine ⟨594399557357576661413851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3170130972573742194207205 594399557357576661413851)
                      ·
                        rfl

theorem cell23_1157589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1157589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157589 prefixEnd_1157589 := by exact prefixLift 1157589
  have htrace : WordTrace (prefixWord ++ tailWord_1157589) baseStart_1157589 baseEnd_1157589 := by
    simpa [prefixWord, tailWord_1157589, baseEnd_1157589] using wordTrace_append hprefix tailTrace_1157589
  have hstable : (prefixWord ++ tailWord_1157589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157589).length < 2 ^ (prefixWord ++ tailWord_1157589).sum := by decide
  have hdescent : baseEnd_1157589 < baseStart_1157589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157612 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_1157612 : Nat := 118140960795 + 1157612 * 2 ^ 59
def prefixEnd_1157612 : Nat := 4983230072969 + 3 ^ 40 * 1157612 * 2
def baseEnd_1157612 : Nat := 198137122470876690475415

theorem tailTrace_1157612 : CollatzResearch.WordTrace tailWord_1157612 prefixEnd_1157612 198137122470876690475415 := by
  unfold tailWord_1157612
  simp only [CollatzResearch.WordTrace]
  refine ⟨21110789141088451617329545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28147718854784602156439393 21110789141088451617329545)
  ·
    refine ⟨15833091855816338712997159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21110789141088451617329545 15833091855816338712997159)
    ·
      refine ⟨23749637783724508069495739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15833091855816338712997159 23749637783724508069495739)
      ·
        refine ⟨35624456675586762104243609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23749637783724508069495739 35624456675586762104243609)
        ·
          refine ⟨26718342506690071578182707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35624456675586762104243609 26718342506690071578182707)
          ·
            refine ⟨40077513760035107367274061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26718342506690071578182707 40077513760035107367274061)
            ·
              refine ⟨15029067660013165262727773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40077513760035107367274061 15029067660013165262727773)
              ·
                refine ⟨5635900372504936973522915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15029067660013165262727773 5635900372504936973522915)
                ·
                  refine ⟨8453850558757405460284373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635900372504936973522915 8453850558757405460284373)
                  ·
                    refine ⟨198137122470876690475415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8453850558757405460284373 198137122470876690475415)
                    ·
                      rfl

theorem cell23_1157612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_1157612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157612 prefixEnd_1157612 := by exact prefixLift 1157612
  have htrace : WordTrace (prefixWord ++ tailWord_1157612) baseStart_1157612 baseEnd_1157612 := by
    simpa [prefixWord, tailWord_1157612, baseEnd_1157612] using wordTrace_append hprefix tailTrace_1157612
  have hstable : (prefixWord ++ tailWord_1157612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157612).length < 2 ^ (prefixWord ++ tailWord_1157612).sum := by decide
  have hdescent : baseEnd_1157612 < baseStart_1157612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157629 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1157629 : Nat := 118140960795 + 1157629 * 2 ^ 59
def prefixEnd_1157629 : Nat := 4983230072969 + 3 ^ 40 * 1157629 * 2
def baseEnd_1157629 : Nat := 198140032194585501637889

theorem tailTrace_1157629 : CollatzResearch.WordTrace tailWord_1157629 prefixEnd_1157629 198140032194585501637889 := by
  unfold tailWord_1157629
  simp only [CollatzResearch.WordTrace]
  refine ⟨42222198323115315138027941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28148132215410210092018627 42222198323115315138027941)
  ·
    refine ⟨7916662185584121588380239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42222198323115315138027941 7916662185584121588380239)
    ·
      refine ⟨11874993278376182382570359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916662185584121588380239 11874993278376182382570359)
      ·
        refine ⟨17812489917564273573855539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874993278376182382570359 17812489917564273573855539)
        ·
          refine ⟨26718734876346410360783309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17812489917564273573855539 26718734876346410360783309)
          ·
            refine ⟨10019525578629903885293741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26718734876346410360783309 10019525578629903885293741)
            ·
              refine ⟨3757322091986213956985153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10019525578629903885293741 3757322091986213956985153)
              ·
                refine ⟨2817991568989660467738865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757322091986213956985153 2817991568989660467738865)
                ·
                  refine ⟨2113493676742245350804149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817991568989660467738865 2113493676742245350804149)
                  ·
                    refine ⟨198140032194585501637889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2113493676742245350804149 198140032194585501637889)
                    ·
                      rfl

theorem cell23_1157629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1157629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157629 prefixEnd_1157629 := by exact prefixLift 1157629
  have htrace : WordTrace (prefixWord ++ tailWord_1157629) baseStart_1157629 baseEnd_1157629 := by
    simpa [prefixWord, tailWord_1157629, baseEnd_1157629] using wordTrace_append hprefix tailTrace_1157629
  have hstable : (prefixWord ++ tailWord_1157629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157629).length < 2 ^ (prefixWord ++ tailWord_1157629).sum := by decide
  have hdescent : baseEnd_1157629 < baseStart_1157629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157632 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1157632 : Nat := 118140960795 + 1157632 * 2 ^ 59
def prefixEnd_1157632 : Nat := 4983230072969 + 3 ^ 40 * 1157632 * 2
def baseEnd_1157632 : Nat := 594421637025719993176153

theorem tailTrace_1157632 : CollatzResearch.WordTrace tailWord_1157632 prefixEnd_1157632 594421637025719993176153 := by
  unfold tailWord_1157632
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111153871052223325193575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28148205161402964433591433 21111153871052223325193575)
  ·
    refine ⟨31666730806578334987790363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21111153871052223325193575 31666730806578334987790363)
    ·
      refine ⟨47500096209867502481685545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31666730806578334987790363 47500096209867502481685545)
      ·
        refine ⟨35625072157400626861264159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47500096209867502481685545 35625072157400626861264159)
        ·
          refine ⟨53437608236100940291896239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35625072157400626861264159 53437608236100940291896239)
          ·
            refine ⟨80156412354151410437844359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53437608236100940291896239 80156412354151410437844359)
            ·
              refine ⟨120234618531227115656766539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80156412354151410437844359 120234618531227115656766539)
              ·
                refine ⟨180351927796840673485149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120234618531227115656766539 180351927796840673485149809)
                ·
                  refine ⟨135263945847630505113862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180351927796840673485149809 135263945847630505113862357)
                  ·
                    refine ⟨3170248730803839963606149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135263945847630505113862357 3170248730803839963606149)
                    ·
                      refine ⟨594421637025719993176153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3170248730803839963606149 594421637025719993176153)
                      ·
                        rfl

theorem cell23_1157632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1157632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157632 prefixEnd_1157632 := by exact prefixLift 1157632
  have htrace : WordTrace (prefixWord ++ tailWord_1157632) baseStart_1157632 baseEnd_1157632 := by
    simpa [prefixWord, tailWord_1157632, baseEnd_1157632] using wordTrace_append hprefix tailTrace_1157632
  have hstable : (prefixWord ++ tailWord_1157632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157632).length < 2 ^ (prefixWord ++ tailWord_1157632).sum := by decide
  have hdescent : baseEnd_1157632 < baseStart_1157632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157633 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 5]
def baseStart_1157633 : Nat := 118140960795 + 1157633 * 2 ^ 59
def prefixEnd_1157633 : Nat := 4983230072969 + 3 ^ 40 * 1157633 * 2
def baseEnd_1157633 : Nat := 66046905611819387695961

theorem tailTrace_1157633 : CollatzResearch.WordTrace tailWord_1157633 prefixEnd_1157633 66046905611819387695961 := by
  unfold tailWord_1157633
  simp only [CollatzResearch.WordTrace]
  refine ⟨42222344215100823821173553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28148229476733882547449035 42222344215100823821173553)
  ·
    refine ⟨31666758161325617865880165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42222344215100823821173553 31666758161325617865880165)
    ·
      refine ⟨5937517155248553349852531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31666758161325617865880165 5937517155248553349852531)
      ·
        refine ⟨8906275732872830024778797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937517155248553349852531 8906275732872830024778797)
        ·
          refine ⟨3339853399827311259292049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8906275732872830024778797 3339853399827311259292049)
          ·
            refine ⟨2504890049870483444469037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3339853399827311259292049 2504890049870483444469037)
            ·
              refine ⟨939333768701431291675889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2504890049870483444469037 939333768701431291675889)
              ·
                refine ⟨704500326526073468756917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939333768701431291675889 704500326526073468756917)
                ·
                  refine ⟨66046905611819387695961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 704500326526073468756917 66046905611819387695961)
                  ·
                    rfl

theorem cell23_1157633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 5].length) (baseStart_1157633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157633 prefixEnd_1157633 := by exact prefixLift 1157633
  have htrace : WordTrace (prefixWord ++ tailWord_1157633) baseStart_1157633 baseEnd_1157633 := by
    simpa [prefixWord, tailWord_1157633, baseEnd_1157633] using wordTrace_append hprefix tailTrace_1157633
  have hstable : (prefixWord ++ tailWord_1157633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157633).length < 2 ^ (prefixWord ++ tailWord_1157633).sum := by decide
  have hdescent : baseEnd_1157633 < baseStart_1157633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157666 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_1157666 : Nat := 118140960795 + 1157666 * 2 ^ 59
def prefixEnd_1157666 : Nat := 4983230072969 + 3 ^ 40 * 1157666 * 2
def baseEnd_1157666 : Nat := 594439095367972860150997

theorem tailTrace_1157666 : CollatzResearch.WordTrace tailWord_1157666 prefixEnd_1157666 594439095367972860150997 := by
  unfold tailWord_1157666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555886955995317614281213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28149031882654180304749901 10555886955995317614281213)
  ·
    refine ⟨3958457608498244105355455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10555886955995317614281213 3958457608498244105355455)
    ·
      refine ⟨5937686412747366158033183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3958457608498244105355455 5937686412747366158033183)
      ·
        refine ⟨8906529619121049237049775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937686412747366158033183 8906529619121049237049775)
        ·
          refine ⟨13359794428681573855574663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8906529619121049237049775 13359794428681573855574663)
          ·
            refine ⟨20039691643022360783361995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359794428681573855574663 20039691643022360783361995)
            ·
              refine ⟨30059537464533541175042993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20039691643022360783361995 30059537464533541175042993)
              ·
                refine ⟨22544653098400155881282245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30059537464533541175042993 22544653098400155881282245)
                ·
                  refine ⟨4227122455950029227740421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22544653098400155881282245 4227122455950029227740421)
                  ·
                    refine ⟨792585460490630480201329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227122455950029227740421 792585460490630480201329)
                    ·
                      refine ⟨594439095367972860150997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792585460490630480201329 594439095367972860150997)
                      ·
                        rfl

theorem cell23_1157666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_1157666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157666 prefixEnd_1157666 := by exact prefixLift 1157666
  have htrace : WordTrace (prefixWord ++ tailWord_1157666) baseStart_1157666 baseEnd_1157666 := by
    simpa [prefixWord, tailWord_1157666, baseEnd_1157666] using wordTrace_append hprefix tailTrace_1157666
  have hstable : (prefixWord ++ tailWord_1157666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157666).length < 2 ^ (prefixWord ++ tailWord_1157666).sum := by decide
  have hdescent : baseEnd_1157666 < baseStart_1157666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157669 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_1157669 : Nat := 118140960795 + 1157669 * 2 ^ 59
def prefixEnd_1157669 : Nat := 4983230072969 + 3 ^ 40 * 1157669 * 2
def baseEnd_1157669 : Nat := 594440635809936348413483

theorem tailTrace_1157669 : CollatzResearch.WordTrace tailWord_1157669 prefixEnd_1157669 594440635809936348413483 := by
  unfold tailWord_1157669
  simp only [CollatzResearch.WordTrace]
  refine ⟨42223657242970401969484061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28149104828646934646322707 42223657242970401969484061)
  ·
    refine ⟨15833871466113900738556523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42223657242970401969484061 15833871466113900738556523)
    ·
      refine ⟨23750807199170851107834785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15833871466113900738556523 23750807199170851107834785)
      ·
        refine ⟨17813105399378138330876089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23750807199170851107834785 17813105399378138330876089)
        ·
          refine ⟨13359829049533603748157067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17813105399378138330876089 13359829049533603748157067)
          ·
            refine ⟨20039743574300405622235601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359829049533603748157067 20039743574300405622235601)
            ·
              refine ⟨15029807680725304216676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20039743574300405622235601 15029807680725304216676701)
              ·
                refine ⟨5636177880271989081253763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15029807680725304216676701 5636177880271989081253763)
                ·
                  refine ⟨8454266820407983621880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5636177880271989081253763 8454266820407983621880645)
                  ·
                    refine ⟨1585175028826496929102621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8454266820407983621880645 1585175028826496929102621)
                    ·
                      refine ⟨594440635809936348413483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1585175028826496929102621 594440635809936348413483)
                      ·
                        rfl

theorem cell23_1157669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_1157669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157669 prefixEnd_1157669 := by exact prefixLift 1157669
  have htrace : WordTrace (prefixWord ++ tailWord_1157669) baseStart_1157669 baseEnd_1157669 := by
    simpa [prefixWord, tailWord_1157669, baseEnd_1157669] using wordTrace_append hprefix tailTrace_1157669
  have hstable : (prefixWord ++ tailWord_1157669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157669).length < 2 ^ (prefixWord ++ tailWord_1157669).sum := by decide
  have hdescent : baseEnd_1157669 < baseStart_1157669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157684 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1157684 : Nat := 118140960795 + 1157684 * 2 ^ 59
def prefixEnd_1157684 : Nat := 4983230072969 + 3 ^ 40 * 1157684 * 2
def baseEnd_1157684 : Nat := 66049815335528198858435

theorem tailTrace_1157684 : CollatzResearch.WordTrace tailWord_1157684 prefixEnd_1157684 66049815335528198858435 := by
  unfold tailWord_1157684
  simp only [CollatzResearch.WordTrace]
  refine ⟨21112102168958029765640053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28149469558610706354186737 21112102168958029765640053)
  ·
    refine ⟨1979259578339815290528755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21112102168958029765640053 1979259578339815290528755)
    ·
      refine ⟨2968889367509722935793133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1979259578339815290528755 2968889367509722935793133)
      ·
        refine ⟨1113333512816146100922425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2968889367509722935793133 1113333512816146100922425)
        ·
          refine ⟨835000134612109575691819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113333512816146100922425 835000134612109575691819)
          ·
            refine ⟨1252500201918164363537729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835000134612109575691819 1252500201918164363537729)
            ·
              refine ⟨939375151438623272653297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252500201918164363537729 939375151438623272653297)
              ·
                refine ⟨704531363578967454489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939375151438623272653297 704531363578967454489973)
                ·
                  refine ⟨66049815335528198858435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 704531363578967454489973 66049815335528198858435)
                  ·
                    rfl

theorem cell23_1157684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1157684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157684 prefixEnd_1157684 := by exact prefixLift 1157684
  have htrace : WordTrace (prefixWord ++ tailWord_1157684) baseStart_1157684 baseEnd_1157684 := by
    simpa [prefixWord, tailWord_1157684, baseEnd_1157684] using wordTrace_append hprefix tailTrace_1157684
  have hstable : (prefixWord ++ tailWord_1157684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157684).length < 2 ^ (prefixWord ++ tailWord_1157684).sum := by decide
  have hdescent : baseEnd_1157684 < baseStart_1157684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157719 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 3, 5]
def baseStart_1157719 : Nat := 118140960795 + 1157719 * 2 ^ 59
def prefixEnd_1157719 : Nat := 4983230072969 + 3 ^ 40 * 1157719 * 2
def baseEnd_1157719 : Nat := 198155436614220384262751

theorem tailTrace_1157719 : CollatzResearch.WordTrace tailWord_1157719 prefixEnd_1157719 198155436614220384262751 := by
  unfold tailWord_1157719
  simp only [CollatzResearch.WordTrace]
  refine ⟨42225480892789260508804211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28150320595192840339202807 42225480892789260508804211)
  ·
    refine ⟨63338221339183890763206317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42225480892789260508804211 63338221339183890763206317)
    ·
      refine ⟨23751833002193959036202369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63338221339183890763206317 23751833002193959036202369)
      ·
        refine ⟨17813874751645469277151777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23751833002193959036202369 17813874751645469277151777)
        ·
          refine ⟨13360406063734101957863833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17813874751645469277151777 13360406063734101957863833)
          ·
            refine ⟨10020304547800576468397875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13360406063734101957863833 10020304547800576468397875)
            ·
              refine ⟨15030456821700864702596813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020304547800576468397875 15030456821700864702596813)
              ·
                refine ⟨5636421308137824263473805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15030456821700864702596813 5636421308137824263473805)
                ·
                  refine ⟨2113657990551684098802677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5636421308137824263473805 2113657990551684098802677)
                  ·
                    refine ⟨198155436614220384262751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2113657990551684098802677 198155436614220384262751)
                    ·
                      rfl

theorem cell23_1157719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_1157719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157719 prefixEnd_1157719 := by exact prefixLift 1157719
  have htrace : WordTrace (prefixWord ++ tailWord_1157719) baseStart_1157719 baseEnd_1157719 := by
    simpa [prefixWord, tailWord_1157719, baseEnd_1157719] using wordTrace_append hprefix tailTrace_1157719
  have hstable : (prefixWord ++ tailWord_1157719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157719).length < 2 ^ (prefixWord ++ tailWord_1157719).sum := by decide
  have hdescent : baseEnd_1157719 < baseStart_1157719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157739 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4]
def baseStart_1157739 : Nat := 118140960795 + 1157739 * 2 ^ 59
def prefixEnd_1157739 : Nat := 4983230072969 + 3 ^ 40 * 1157739 * 2
def baseEnd_1157739 : Nat := 594476579455751074538161

theorem tailTrace_1157739 : CollatzResearch.WordTrace tailWord_1157739 prefixEnd_1157739 594476579455751074538161 := by
  unfold tailWord_1157739
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226210352716803924532271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28150806901811202616354847 42226210352716803924532271)
  ·
    refine ⟨63339315529075205886798407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42226210352716803924532271 63339315529075205886798407)
    ·
      refine ⟨95008973293612808830197611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63339315529075205886798407 95008973293612808830197611)
      ·
        refine ⟨142513459940419213245296417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95008973293612808830197611 142513459940419213245296417)
        ·
          refine ⟨106885094955314409933972313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142513459940419213245296417 106885094955314409933972313)
          ·
            refine ⟨80163821216485807450479235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106885094955314409933972313 80163821216485807450479235)
            ·
              refine ⟨120245731824728711175718853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80163821216485807450479235 120245731824728711175718853)
              ·
                refine ⟨22546074717136633345447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120245731824728711175718853 22546074717136633345447285)
                ·
                  refine ⟨2113694504731559376135683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22546074717136633345447285 2113694504731559376135683)
                  ·
                    refine ⟨3170541757097339064203525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2113694504731559376135683 3170541757097339064203525)
                    ·
                      refine ⟨594476579455751074538161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3170541757097339064203525 594476579455751074538161)
                      ·
                        rfl

theorem cell23_1157739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_1157739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157739 prefixEnd_1157739 := by exact prefixLift 1157739
  have htrace : WordTrace (prefixWord ++ tailWord_1157739) baseStart_1157739 baseEnd_1157739 := by
    simpa [prefixWord, tailWord_1157739, baseEnd_1157739] using wordTrace_append hprefix tailTrace_1157739
  have hstable : (prefixWord ++ tailWord_1157739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157739).length < 2 ^ (prefixWord ++ tailWord_1157739).sum := by decide
  have hdescent : baseEnd_1157739 < baseStart_1157739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157759 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_1157759 : Nat := 118140960795 + 1157759 * 2 ^ 59
def prefixEnd_1157759 : Nat := 4983230072969 + 3 ^ 40 * 1157759 * 2
def baseEnd_1157759 : Nat := 594486849068840996288069

theorem tailTrace_1157759 : CollatzResearch.WordTrace tailWord_1157759 prefixEnd_1157759 594486849068840996288069 := by
  unfold tailWord_1157759
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226939812644347340260331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28151293208429564893506887 42226939812644347340260331)
  ·
    refine ⟨63340409718966521010390497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42226939812644347340260331 63340409718966521010390497)
    ·
      refine ⟨47505307289224890757792873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63340409718966521010390497 47505307289224890757792873)
      ·
        refine ⟨35628980466918668068344655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47505307289224890757792873 35628980466918668068344655)
        ·
          refine ⟨53443470700378002102516983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35628980466918668068344655 53443470700378002102516983)
          ·
            refine ⟨80165206050567003153775475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53443470700378002102516983 80165206050567003153775475)
            ·
              refine ⟨120247809075850504730663213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80165206050567003153775475 120247809075850504730663213)
              ·
                refine ⟨45092928403443939273998705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120247809075850504730663213 45092928403443939273998705)
                ·
                  refine ⟨33819696302582954455499029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45092928403443939273998705 33819696302582954455499029)
                  ·
                    refine ⟨1585298264183575990101517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33819696302582954455499029 1585298264183575990101517)
                    ·
                      refine ⟨594486849068840996288069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1585298264183575990101517 594486849068840996288069)
                      ·
                        rfl

theorem cell23_1157759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_1157759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157759 prefixEnd_1157759 := by exact prefixLift 1157759
  have htrace : WordTrace (prefixWord ++ tailWord_1157759) baseStart_1157759 baseEnd_1157759 := by
    simpa [prefixWord, tailWord_1157759, baseEnd_1157759] using wordTrace_append hprefix tailTrace_1157759
  have hstable : (prefixWord ++ tailWord_1157759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157759).length < 2 ^ (prefixWord ++ tailWord_1157759).sum := by decide
  have hdescent : baseEnd_1157759 < baseStart_1157759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157793 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1157793 : Nat := 118140960795 + 1157793 * 2 ^ 59
def prefixEnd_1157793 : Nat := 4983230072969 + 3 ^ 40 * 1157793 * 2
def baseEnd_1157793 : Nat := 594504307411093863262913

theorem tailTrace_1157793 : CollatzResearch.WordTrace tailWord_1157793 prefixEnd_1157793 594504307411093863262913 := by
  unfold tailWord_1157793
  simp only [CollatzResearch.WordTrace]
  refine ⟨42228179894521171146998033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28152119929680780764665355 42228179894521171146998033)
  ·
    refine ⟨31671134920890878360248525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42228179894521171146998033 31671134920890878360248525)
    ·
      refine ⟨11876675595334079385093197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31671134920890878360248525 11876675595334079385093197)
      ·
        refine ⟨4453753348250279769409949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11876675595334079385093197 4453753348250279769409949)
        ·
          refine ⟨1670157505593854913528731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4453753348250279769409949 1670157505593854913528731)
          ·
            refine ⟨2505236258390782370293097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670157505593854913528731 2505236258390782370293097)
            ·
              refine ⟨1878927193793086777719823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505236258390782370293097 1878927193793086777719823)
              ·
                refine ⟨2818390790689630166579735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878927193793086777719823 2818390790689630166579735)
                ·
                  refine ⟨4227586186034445249869603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818390790689630166579735 4227586186034445249869603)
                  ·
                    refine ⟨6341379279051667874804405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227586186034445249869603 6341379279051667874804405)
                    ·
                      refine ⟨594504307411093863262913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6341379279051667874804405 594504307411093863262913)
                      ·
                        rfl

theorem cell23_1157793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1157793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157793 prefixEnd_1157793 := by exact prefixLift 1157793
  have htrace : WordTrace (prefixWord ++ tailWord_1157793) baseStart_1157793 baseEnd_1157793 := by
    simpa [prefixWord, tailWord_1157793, baseEnd_1157793] using wordTrace_append hprefix tailTrace_1157793
  have hstable : (prefixWord ++ tailWord_1157793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157793).length < 2 ^ (prefixWord ++ tailWord_1157793).sum := by decide
  have hdescent : baseEnd_1157793 < baseStart_1157793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157816 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_1157816 : Nat := 118140960795 + 1157816 * 2 ^ 59
def prefixEnd_1157816 : Nat := 4983230072969 + 3 ^ 40 * 1157816 * 2
def baseEnd_1157816 : Nat := 594516117466147273275307

theorem tailTrace_1157816 : CollatzResearch.WordTrace tailWord_1157816 prefixEnd_1157816 594516117466147273275307 := by
  unfold tailWord_1157816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21114509386718923037542651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28152679182291897383390201 21114509386718923037542651)
  ·
    refine ⟨31671764080078384556313977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21114509386718923037542651 31671764080078384556313977)
    ·
      refine ⟨23753823060058788417235483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31671764080078384556313977 23753823060058788417235483)
      ·
        refine ⟨35630734590088182625853225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23753823060058788417235483 35630734590088182625853225)
        ·
          refine ⟨26723050942566136969389919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35630734590088182625853225 26723050942566136969389919)
          ·
            refine ⟨40084576413849205454084879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26723050942566136969389919 40084576413849205454084879)
            ·
              refine ⟨60126864620773808181127319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40084576413849205454084879 60126864620773808181127319)
              ·
                refine ⟨90190296931160712271690979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60126864620773808181127319 90190296931160712271690979)
                ·
                  refine ⟨135285445396741068407536469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90190296931160712271690979 135285445396741068407536469)
                  ·
                    refine ⟨792688156621529697700409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135285445396741068407536469 792688156621529697700409)
                    ·
                      refine ⟨594516117466147273275307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792688156621529697700409 594516117466147273275307)
                      ·
                        rfl

theorem cell23_1157816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_1157816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157816 prefixEnd_1157816 := by exact prefixLift 1157816
  have htrace : WordTrace (prefixWord ++ tailWord_1157816) baseStart_1157816 baseEnd_1157816 := by
    simpa [prefixWord, tailWord_1157816, baseEnd_1157816] using wordTrace_append hprefix tailTrace_1157816
  have hstable : (prefixWord ++ tailWord_1157816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157816).length < 2 ^ (prefixWord ++ tailWord_1157816).sum := by decide
  have hdescent : baseEnd_1157816 < baseStart_1157816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157839 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 6, 6]
def baseStart_1157839 : Nat := 118140960795 + 1157839 * 2 ^ 59
def prefixEnd_1157839 : Nat := 4983230072969 + 3 ^ 40 * 1157839 * 2
def baseEnd_1157839 : Nat := 198175975840400227762567

theorem tailTrace_1157839 : CollatzResearch.WordTrace tailWord_1157839 prefixEnd_1157839 198175975840400227762567 := by
  unfold tailWord_1157839
  simp only [CollatzResearch.WordTrace]
  refine ⟨42229857652354521003172571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28153238434903014002115047 42229857652354521003172571)
  ·
    refine ⟨63344786478531781504758857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42229857652354521003172571 63344786478531781504758857)
    ·
      refine ⟨47508589858898836128569143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63344786478531781504758857 47508589858898836128569143)
      ·
        refine ⟨71262884788348254192853715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47508589858898836128569143 71262884788348254192853715)
        ·
          refine ⟨106894327182522381289280573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71262884788348254192853715 106894327182522381289280573)
          ·
            refine ⟨40085372693445892983480215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106894327182522381289280573 40085372693445892983480215)
            ·
              refine ⟨60128059040168839475220323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40085372693445892983480215 60128059040168839475220323)
              ·
                refine ⟨90192088560253259212830485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60128059040168839475220323 90192088560253259212830485)
                ·
                  refine ⟨4227754151261871525601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90192088560253259212830485 4227754151261871525601429)
                  ·
                    refine ⟨198175975840400227762567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4227754151261871525601429 198175975840400227762567)
                    ·
                      rfl

theorem cell23_1157839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_1157839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157839 prefixEnd_1157839 := by exact prefixLift 1157839
  have htrace : WordTrace (prefixWord ++ tailWord_1157839) baseStart_1157839 baseEnd_1157839 := by
    simpa [prefixWord, tailWord_1157839, baseEnd_1157839] using wordTrace_append hprefix tailTrace_1157839
  have hstable : (prefixWord ++ tailWord_1157839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157839).length < 2 ^ (prefixWord ++ tailWord_1157839).sum := by decide
  have hdescent : baseEnd_1157839 < baseStart_1157839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157880 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_1157880 : Nat := 118140960795 + 1157880 * 2 ^ 59
def prefixEnd_1157880 : Nat := 4983230072969 + 3 ^ 40 * 1157880 * 2
def baseEnd_1157880 : Nat := 594548980228035022875013

theorem tailTrace_1157880 : CollatzResearch.WordTrace tailWord_1157880 prefixEnd_1157880 594548980228035022875013 := by
  unfold tailWord_1157880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21115676522602992502707547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28154235363470656670276729 21115676522602992502707547)
  ·
    refine ⟨31673514783904488754061321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21115676522602992502707547 31673514783904488754061321)
    ·
      refine ⟨23755136087928366565545991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31673514783904488754061321 23755136087928366565545991)
      ·
        refine ⟨35632704131892549848318987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23755136087928366565545991 35632704131892549848318987)
        ·
          refine ⟨53449056197838824772478481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35632704131892549848318987 53449056197838824772478481)
          ·
            refine ⟨40086792148379118579358861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53449056197838824772478481 40086792148379118579358861)
            ·
              refine ⟨15032547055642169467259573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40086792148379118579358861 15032547055642169467259573)
              ·
                refine ⟨1409301286466453387555585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15032547055642169467259573 1409301286466453387555585)
                ·
                  refine ⟨1056975964849840040666689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409301286466453387555585 1056975964849840040666689)
                  ·
                    refine ⟨792731973637380030500017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056975964849840040666689 792731973637380030500017)
                    ·
                      refine ⟨594548980228035022875013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792731973637380030500017 594548980228035022875013)
                      ·
                        rfl

theorem cell23_1157880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_1157880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157880 prefixEnd_1157880 := by exact prefixLift 1157880
  have htrace : WordTrace (prefixWord ++ tailWord_1157880) baseStart_1157880 baseEnd_1157880 := by
    simpa [prefixWord, tailWord_1157880, baseEnd_1157880] using wordTrace_append hprefix tailTrace_1157880
  have hstable : (prefixWord ++ tailWord_1157880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157880).length < 2 ^ (prefixWord ++ tailWord_1157880).sum := by decide
  have hdescent : baseEnd_1157880 < baseStart_1157880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157903 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 5]
def baseStart_1157903 : Nat := 118140960795 + 1157903 * 2 ^ 59
def prefixEnd_1157903 : Nat := 4983230072969 + 3 ^ 40 * 1157903 * 2
def baseEnd_1157903 : Nat := 66062310031454270320823

theorem tailTrace_1157903 : CollatzResearch.WordTrace tailWord_1157903 prefixEnd_1157903 66062310031454270320823 := by
  unfold tailWord_1157903
  simp only [CollatzResearch.WordTrace]
  refine ⟨42232191924122659933502363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28154794616081773289001575 42232191924122659933502363)
  ·
    refine ⟨63348287886183989900253545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42232191924122659933502363 63348287886183989900253545)
    ·
      refine ⟨47511215914637992425190159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63348287886183989900253545 47511215914637992425190159)
      ·
        refine ⟨71266823871956988637785239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47511215914637992425190159 71266823871956988637785239)
        ·
          refine ⟨106900235807935482956677859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71266823871956988637785239 106900235807935482956677859)
          ·
            refine ⟨160350353711903224435016789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106900235807935482956677859 160350353711903224435016789)
            ·
              refine ⟨1879105707561365911347853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 160350353711903224435016789 1879105707561365911347853)
              ·
                refine ⟨704664640335512216755445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879105707561365911347853 704664640335512216755445)
                ·
                  refine ⟨66062310031454270320823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 704664640335512216755445 66062310031454270320823)
                  ·
                    rfl

theorem cell23_1157903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 5].length) (baseStart_1157903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157903 prefixEnd_1157903 := by exact prefixLift 1157903
  have htrace : WordTrace (prefixWord ++ tailWord_1157903) baseStart_1157903 baseEnd_1157903 := by
    simpa [prefixWord, tailWord_1157903, baseEnd_1157903] using wordTrace_append hprefix tailTrace_1157903
  have hstable : (prefixWord ++ tailWord_1157903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157903).length < 2 ^ (prefixWord ++ tailWord_1157903).sum := by decide
  have hdescent : baseEnd_1157903 < baseStart_1157903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157966 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1157966 : Nat := 118140960795 + 1157966 * 2 ^ 59
def prefixEnd_1157966 : Nat := 4983230072969 + 3 ^ 40 * 1157966 * 2
def baseEnd_1157966 : Nat := 594593139564321686399617

theorem tailTrace_1157966 : CollatzResearch.WordTrace tailWord_1157966 prefixEnd_1157966 594593139564321686399617 := by
  unfold tailWord_1157966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279311215361802711630719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28156326481929614462030501 5279311215361802711630719)
  ·
    refine ⟨7918966823042704067446079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279311215361802711630719 7918966823042704067446079)
    ·
      refine ⟨11878450234564056101169119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918966823042704067446079 11878450234564056101169119)
      ·
        refine ⟨17817675351846084151753679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11878450234564056101169119 17817675351846084151753679)
        ·
          refine ⟨26726513027769126227630519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17817675351846084151753679 26726513027769126227630519)
          ·
            refine ⟨40089769541653689341445779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26726513027769126227630519 40089769541653689341445779)
            ·
              refine ⟨60134654312480534012168669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40089769541653689341445779 60134654312480534012168669)
              ·
                refine ⟨22550495367180200254563251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60134654312480534012168669 22550495367180200254563251)
                ·
                  refine ⟨33825743050770300381844877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22550495367180200254563251 33825743050770300381844877)
                  ·
                    refine ⟨12684653644038862643191829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33825743050770300381844877 12684653644038862643191829)
                    ·
                      refine ⟨594593139564321686399617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12684653644038862643191829 594593139564321686399617)
                      ·
                        rfl

theorem cell23_1157966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1157966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1157966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1157966 prefixEnd_1157966 := by exact prefixLift 1157966
  have htrace : WordTrace (prefixWord ++ tailWord_1157966) baseStart_1157966 baseEnd_1157966 := by
    simpa [prefixWord, tailWord_1157966, baseEnd_1157966] using wordTrace_append hprefix tailTrace_1157966
  have hstable : (prefixWord ++ tailWord_1157966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157966).length < 2 ^ (prefixWord ++ tailWord_1157966).sum := by decide
  have hdescent : baseEnd_1157966 < baseStart_1157966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158016 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1158016 : Nat := 118140960795 + 1158016 * 2 ^ 59
def prefixEnd_1158016 : Nat := 4983230072969 + 3 ^ 40 * 1158016 * 2
def baseEnd_1158016 : Nat := 594618813597046490774387

theorem tailTrace_1158016 : CollatzResearch.WordTrace tailWord_1158016 prefixEnd_1158016 594618813597046490774387 := by
  unfold tailWord_1158016
  simp only [CollatzResearch.WordTrace]
  refine ⟨21118156686356640116182951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28157542248475520154910601 21118156686356640116182951)
  ·
    refine ⟨31677235029534960174274427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21118156686356640116182951 31677235029534960174274427)
    ·
      refine ⟨47515852544302440261411641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31677235029534960174274427 47515852544302440261411641)
      ·
        refine ⟨35636889408226830196058731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47515852544302440261411641 35636889408226830196058731)
        ·
          refine ⟨53455334112340245294088097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35636889408226830196058731 53455334112340245294088097)
          ·
            refine ⟨40091500584255183970566073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53455334112340245294088097 40091500584255183970566073)
            ·
              refine ⟨30068625438191387977924555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40091500584255183970566073 30068625438191387977924555)
              ·
                refine ⟨45102938157287081966886833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30068625438191387977924555 45102938157287081966886833)
                ·
                  refine ⟨33827203617965311475165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45102938157287081966886833 33827203617965311475165125)
                  ·
                    refine ⟨6342600678368495901593461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33827203617965311475165125 6342600678368495901593461)
                    ·
                      refine ⟨594618813597046490774387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6342600678368495901593461 594618813597046490774387)
                      ·
                        rfl

theorem cell23_1158016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1158016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158016 prefixEnd_1158016 := by exact prefixLift 1158016
  have htrace : WordTrace (prefixWord ++ tailWord_1158016) baseStart_1158016 baseEnd_1158016 := by
    simpa [prefixWord, tailWord_1158016, baseEnd_1158016] using wordTrace_append hprefix tailTrace_1158016
  have hstable : (prefixWord ++ tailWord_1158016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158016).length < 2 ^ (prefixWord ++ tailWord_1158016).sum := by decide
  have hdescent : baseEnd_1158016 < baseStart_1158016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158053 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1158053 : Nat := 118140960795 + 1158053 * 2 ^ 59
def prefixEnd_1158053 : Nat := 4983230072969 + 3 ^ 40 * 1158053 * 2
def baseEnd_1158053 : Nat := 198212604127087615337239

theorem tailTrace_1158053 : CollatzResearch.WordTrace tailWord_1158053 prefixEnd_1158053 198212604127087615337239 := by
  unfold tailWord_1158053
  simp only [CollatzResearch.WordTrace]
  refine ⟨42237662873579235551462813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28158441915719490367641875 42237662873579235551462813)
  ·
    refine ⟨15839123577592213331798555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42237662873579235551462813 15839123577592213331798555)
    ·
      refine ⟨23758685366388319997697833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15839123577592213331798555 23758685366388319997697833)
      ·
        refine ⟨17819014024791239998273375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23758685366388319997697833 17819014024791239998273375)
        ·
          refine ⟨26728521037186859997410063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17819014024791239998273375 26728521037186859997410063)
          ·
            refine ⟨40092781555780289996115095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26728521037186859997410063 40092781555780289996115095)
            ·
              refine ⟨60139172333670434994172643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40092781555780289996115095 60139172333670434994172643)
              ·
                refine ⟨90208758500505652491258965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60139172333670434994172643 90208758500505652491258965)
                ·
                  refine ⟨1057133888677800615131941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 90208758500505652491258965 1057133888677800615131941)
                  ·
                    refine ⟨198212604127087615337239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1057133888677800615131941 198212604127087615337239)
                    ·
                      rfl

theorem cell23_1158053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1158053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158053 prefixEnd_1158053 := by exact prefixLift 1158053
  have htrace : WordTrace (prefixWord ++ tailWord_1158053) baseStart_1158053 baseEnd_1158053 := by
    simpa [prefixWord, tailWord_1158053, baseEnd_1158053] using wordTrace_append hprefix tailTrace_1158053
  have hstable : (prefixWord ++ tailWord_1158053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158053).length < 2 ^ (prefixWord ++ tailWord_1158053).sum := by decide
  have hdescent : baseEnd_1158053 < baseStart_1158053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158077 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1158077 : Nat := 118140960795 + 1158077 * 2 ^ 59
def prefixEnd_1158077 : Nat := 4983230072969 + 3 ^ 40 * 1158077 * 2
def baseEnd_1158077 : Nat := 594650135916970752111607

theorem tailTrace_1158077 : CollatzResearch.WordTrace tailWord_1158077 prefixEnd_1158077 594650135916970752111607 := by
  unfold tailWord_1158077
  simp only [CollatzResearch.WordTrace]
  refine ⟨42238538225492287650336485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28159025483661525100224323 42238538225492287650336485)
  ·
    refine ⟨7919725917279803934438091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42238538225492287650336485 7919725917279803934438091)
    ·
      refine ⟨11879588875919705901657137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7919725917279803934438091 11879588875919705901657137)
      ·
        refine ⟨8909691656939779426242853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11879588875919705901657137 8909691656939779426242853)
        ·
          refine ⟨1670567185676208642420535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8909691656939779426242853 1670567185676208642420535)
          ·
            refine ⟨2505850778514312963630803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670567185676208642420535 2505850778514312963630803)
            ·
              refine ⟨3758776167771469445446205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505850778514312963630803 3758776167771469445446205)
              ·
                refine ⟨1409541062914301042042327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3758776167771469445446205 1409541062914301042042327)
                ·
                  refine ⟨2114311594371451563063491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409541062914301042042327 2114311594371451563063491)
                  ·
                    refine ⟨3171467391557177344595237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114311594371451563063491 3171467391557177344595237)
                    ·
                      refine ⟨594650135916970752111607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3171467391557177344595237 594650135916970752111607)
                      ·
                        rfl

theorem cell23_1158077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1158077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158077 prefixEnd_1158077 := by exact prefixLift 1158077
  have htrace : WordTrace (prefixWord ++ tailWord_1158077) baseStart_1158077 baseEnd_1158077 := by
    simpa [prefixWord, tailWord_1158077, baseEnd_1158077] using wordTrace_append hprefix tailTrace_1158077
  have hstable : (prefixWord ++ tailWord_1158077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158077).length < 2 ^ (prefixWord ++ tailWord_1158077).sum := by decide
  have hdescent : baseEnd_1158077 < baseStart_1158077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158094 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_1158094 : Nat := 118140960795 + 1158094 * 2 ^ 59
def prefixEnd_1158094 : Nat := 4983230072969 + 3 ^ 40 * 1158094 * 2
def baseEnd_1158094 : Nat := 594658865088097185599029

theorem tailTrace_1158094 : CollatzResearch.WordTrace tailWord_1158094 prefixEnd_1158094 594658865088097185599029 := by
  unfold tailWord_1158094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279894783303837444213167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28159438844287133035803557 5279894783303837444213167)
  ·
    refine ⟨7919842174955756166319751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279894783303837444213167 7919842174955756166319751)
    ·
      refine ⟨11879763262433634249479627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7919842174955756166319751 11879763262433634249479627)
      ·
        refine ⟨17819644893650451374219441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879763262433634249479627 17819644893650451374219441)
        ·
          refine ⟨13364733670237838530664581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17819644893650451374219441 13364733670237838530664581)
          ·
            refine ⟨2505887563169594724499609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13364733670237838530664581 2505887563169594724499609)
            ·
              refine ⟨1879415672377196043374707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505887563169594724499609 1879415672377196043374707)
              ·
                refine ⟨2819123508565794065062061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879415672377196043374707 2819123508565794065062061)
                ·
                  refine ⟨1057171315712172774398273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2819123508565794065062061 1057171315712172774398273)
                  ·
                    refine ⟨792878486784129580798705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057171315712172774398273 792878486784129580798705)
                    ·
                      refine ⟨594658865088097185599029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792878486784129580798705 594658865088097185599029)
                      ·
                        rfl

theorem cell23_1158094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_1158094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158094 prefixEnd_1158094 := by exact prefixLift 1158094
  have htrace : WordTrace (prefixWord ++ tailWord_1158094) baseStart_1158094 baseEnd_1158094 := by
    simpa [prefixWord, tailWord_1158094, baseEnd_1158094] using wordTrace_append hprefix tailTrace_1158094
  have hstable : (prefixWord ++ tailWord_1158094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158094).length < 2 ^ (prefixWord ++ tailWord_1158094).sum := by decide
  have hdescent : baseEnd_1158094 < baseStart_1158094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158114 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1158114 : Nat := 118140960795 + 1158114 * 2 ^ 59
def prefixEnd_1158114 : Nat := 4983230072969 + 3 ^ 40 * 1158114 * 2
def baseEnd_1158114 : Nat := 594669134701187107348937

theorem tailTrace_1158114 : CollatzResearch.WordTrace tailWord_1158114 prefixEnd_1158114 594669134701187107348937 := by
  unfold tailWord_1158114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10559971931589560742358349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28159925150905495312955597 10559971931589560742358349)
  ·
    refine ⟨3959989474346085278384381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10559971931589560742358349 3959989474346085278384381)
    ·
      refine ⟨1484996052879781979394143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3959989474346085278384381 1484996052879781979394143)
      ·
        refine ⟨2227494079319672969091215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484996052879781979394143 2227494079319672969091215)
        ·
          refine ⟨3341241118979509453636823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227494079319672969091215 3341241118979509453636823)
          ·
            refine ⟨5011861678469264180455235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341241118979509453636823 5011861678469264180455235)
            ·
              refine ⟨7517792517703896270682853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011861678469264180455235 7517792517703896270682853)
              ·
                refine ⟨1409586097069480550753035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7517792517703896270682853 1409586097069480550753035)
                ·
                  refine ⟨2114379145604220826129553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409586097069480550753035 2114379145604220826129553)
                  ·
                    refine ⟨1585784359203165619597165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114379145604220826129553 1585784359203165619597165)
                    ·
                      refine ⟨594669134701187107348937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1585784359203165619597165 594669134701187107348937)
                      ·
                        rfl

theorem cell23_1158114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1158114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158114 prefixEnd_1158114 := by exact prefixLift 1158114
  have htrace : WordTrace (prefixWord ++ tailWord_1158114) baseStart_1158114 baseEnd_1158114 := by
    simpa [prefixWord, tailWord_1158114, baseEnd_1158114] using wordTrace_append hprefix tailTrace_1158114
  have hstable : (prefixWord ++ tailWord_1158114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158114).length < 2 ^ (prefixWord ++ tailWord_1158114).sum := by decide
  have hdescent : baseEnd_1158114 < baseStart_1158114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158137 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 1, 3, 2]
def baseStart_1158137 : Nat := 118140960795 + 1158137 * 2 ^ 59
def prefixEnd_1158137 : Nat := 4983230072969 + 3 ^ 40 * 1158137 * 2
def baseEnd_1158137 : Nat := 594680944756240517361331

theorem tailTrace_1158137 : CollatzResearch.WordTrace tailWord_1158137 prefixEnd_1158137 594680944756240517361331 := by
  unfold tailWord_1158137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42240726605274917897520665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28160484403516611931680443 42240726605274917897520665)
  ·
    refine ⟨31680544953956188423140499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42240726605274917897520665 31680544953956188423140499)
    ·
      refine ⟨47520817430934282634710749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31680544953956188423140499 47520817430934282634710749)
      ·
        refine ⟨17820306536600355988016531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47520817430934282634710749 17820306536600355988016531)
        ·
          refine ⟨26730459804900533982024797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17820306536600355988016531 26730459804900533982024797)
          ·
            refine ⟨10023922426837700243259299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26730459804900533982024797 10023922426837700243259299)
            ·
              refine ⟨15035883640256550364888949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10023922426837700243259299 15035883640256550364888949)
              ·
                refine ⟨1409614091274051596708339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15035883640256550364888949 1409614091274051596708339)
                ·
                  refine ⟨2114421136911077395062509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409614091274051596708339 2114421136911077395062509)
                  ·
                    refine ⟨792907926341654023148441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2114421136911077395062509 792907926341654023148441)
                    ·
                      refine ⟨594680944756240517361331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792907926341654023148441 594680944756240517361331)
                      ·
                        rfl

theorem cell23_1158137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_1158137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158137 prefixEnd_1158137 := by exact prefixLift 1158137
  have htrace : WordTrace (prefixWord ++ tailWord_1158137) baseStart_1158137 baseEnd_1158137 := by
    simpa [prefixWord, tailWord_1158137, baseEnd_1158137] using wordTrace_append hprefix tailTrace_1158137
  have hstable : (prefixWord ++ tailWord_1158137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158137).length < 2 ^ (prefixWord ++ tailWord_1158137).sum := by decide
  have hdescent : baseEnd_1158137 < baseStart_1158137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158163 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_1158163 : Nat := 118140960795 + 1158163 * 2 ^ 59
def prefixEnd_1158163 : Nat := 4983230072969 + 3 ^ 40 * 1158163 * 2
def baseEnd_1158163 : Nat := 594694295253257415636211

theorem tailTrace_1158163 : CollatzResearch.WordTrace tailWord_1158163 prefixEnd_1158163 594694295253257415636211 := by
  unfold tailWord_1158163
  simp only [CollatzResearch.WordTrace]
  refine ⟨42241674903180724337967143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28161116602120482891978095 42241674903180724337967143)
  ·
    refine ⟨63362512354771086506950715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42241674903180724337967143 63362512354771086506950715)
    ·
      refine ⟨95043768532156629760426073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63362512354771086506950715 95043768532156629760426073)
      ·
        refine ⟨71282826399117472320319555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95043768532156629760426073 71282826399117472320319555)
        ·
          refine ⟨106924239598676208480479333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71282826399117472320319555 106924239598676208480479333)
          ·
            refine ⟨20048294924751789090089875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106924239598676208480479333 20048294924751789090089875)
            ·
              refine ⟨30072442387127683635134813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20048294924751789090089875 30072442387127683635134813)
              ·
                refine ⟨11277165895172881363175555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30072442387127683635134813 11277165895172881363175555)
                ·
                  refine ⟨16915748842759322044763333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11277165895172881363175555 16915748842759322044763333)
                  ·
                    refine ⟨3171702908017372883393125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16915748842759322044763333 3171702908017372883393125)
                    ·
                      refine ⟨594694295253257415636211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3171702908017372883393125 594694295253257415636211)
                      ·
                        rfl

theorem cell23_1158163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_1158163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158163 prefixEnd_1158163 := by exact prefixLift 1158163
  have htrace : WordTrace (prefixWord ++ tailWord_1158163) baseStart_1158163 baseEnd_1158163 := by
    simpa [prefixWord, tailWord_1158163, baseEnd_1158163] using wordTrace_append hprefix tailTrace_1158163
  have hstable : (prefixWord ++ tailWord_1158163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158163).length < 2 ^ (prefixWord ++ tailWord_1158163).sum := by decide
  have hdescent : baseEnd_1158163 < baseStart_1158163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158201 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1158201 : Nat := 118140960795 + 1158201 * 2 ^ 59
def prefixEnd_1158201 : Nat := 4983230072969 + 3 ^ 40 * 1158201 * 2
def baseEnd_1158201 : Nat := 594713807518128266961037

theorem tailTrace_1158201 : CollatzResearch.WordTrace tailWord_1158201 prefixEnd_1158201 594713807518128266961037 := by
  unfold tailWord_1158201
  simp only [CollatzResearch.WordTrace]
  refine ⟨42243060877043056827850457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28162040584695371218566971 42243060877043056827850457)
  ·
    refine ⟨31682295657782292620887843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42243060877043056827850457 31682295657782292620887843)
    ·
      refine ⟨47523443486673438931331765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31682295657782292620887843 47523443486673438931331765)
      ·
        refine ⟨4455322826875634899812353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47523443486673438931331765 4455322826875634899812353)
        ·
          refine ⟨3341492120156726174859265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455322826875634899812353 3341492120156726174859265)
          ·
            refine ⟨2506119090117544631144449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3341492120156726174859265 2506119090117544631144449)
            ·
              refine ⟨1879589317588158473358337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506119090117544631144449 1879589317588158473358337)
              ·
                refine ⟨1409691988191118855018753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879589317588158473358337 1409691988191118855018753)
                ·
                  refine ⟨1057268991143339141264065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409691988191118855018753 1057268991143339141264065)
                  ·
                    refine ⟨792951743357504355948049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057268991143339141264065 792951743357504355948049)
                    ·
                      refine ⟨594713807518128266961037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 792951743357504355948049 594713807518128266961037)
                      ·
                        rfl

theorem cell23_1158201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1158201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158201 prefixEnd_1158201 := by exact prefixLift 1158201
  have htrace : WordTrace (prefixWord ++ tailWord_1158201) baseStart_1158201 baseEnd_1158201 := by
    simpa [prefixWord, tailWord_1158201, baseEnd_1158201] using wordTrace_append hprefix tailTrace_1158201
  have hstable : (prefixWord ++ tailWord_1158201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158201).length < 2 ^ (prefixWord ++ tailWord_1158201).sum := by decide
  have hdescent : baseEnd_1158201 < baseStart_1158201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158214 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1158214 : Nat := 118140960795 + 1158214 * 2 ^ 59
def prefixEnd_1158214 : Nat := 4983230072969 + 3 ^ 40 * 1158214 * 2
def baseEnd_1158214 : Nat := 594720482766636716098477

theorem tailTrace_1158214 : CollatzResearch.WordTrace tailWord_1158214 prefixEnd_1158214 594720482766636716098477 := by
  unfold tailWord_1158214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320110469562373751502303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28162356683997306698715797 1320110469562373751502303)
  ·
    refine ⟨1980165704343560627253455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320110469562373751502303 1980165704343560627253455)
    ·
      refine ⟨2970248556515340940880183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980165704343560627253455 2970248556515340940880183)
      ·
        refine ⟨4455372834773011411320275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970248556515340940880183 4455372834773011411320275)
        ·
          refine ⟨6683059252159517116980413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455372834773011411320275 6683059252159517116980413)
          ·
            refine ⟨2506147219559818918867655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6683059252159517116980413 2506147219559818918867655)
            ·
              refine ⟨3759220829339728378301483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506147219559818918867655 3759220829339728378301483)
              ·
                refine ⟨5638831244009592567452225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759220829339728378301483 5638831244009592567452225)
                ·
                  refine ⟨4229123433007194425589169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638831244009592567452225 4229123433007194425589169)
                  ·
                    refine ⟨3171842574755395819191877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4229123433007194425589169 3171842574755395819191877)
                    ·
                      refine ⟨594720482766636716098477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3171842574755395819191877 594720482766636716098477)
                      ·
                        rfl

theorem cell23_1158214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1158214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158214 prefixEnd_1158214 := by exact prefixLift 1158214
  have htrace : WordTrace (prefixWord ++ tailWord_1158214) baseStart_1158214 baseEnd_1158214 := by
    simpa [prefixWord, tailWord_1158214, baseEnd_1158214] using wordTrace_append hprefix tailTrace_1158214
  have hstable : (prefixWord ++ tailWord_1158214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158214).length < 2 ^ (prefixWord ++ tailWord_1158214).sum := by decide
  have hdescent : baseEnd_1158214 < baseStart_1158214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158233 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_1158233 : Nat := 118140960795 + 1158233 * 2 ^ 59
def prefixEnd_1158233 : Nat := 4983230072969 + 3 ^ 40 * 1158233 * 2
def baseEnd_1158233 : Nat := 198243412966357380586963

theorem tailTrace_1158233 : CollatzResearch.WordTrace tailWord_1158233 prefixEnd_1158233 198243412966357380586963 := by
  unfold tailWord_1158233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42244228012927126293015353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28162818675284750862010235 42244228012927126293015353)
  ·
    refine ⟨31683171009695344719761515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42244228012927126293015353 31683171009695344719761515)
    ·
      refine ⟨47524756514543017079642273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31683171009695344719761515 47524756514543017079642273)
      ·
        refine ⟨35643567385907262809731705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47524756514543017079642273 35643567385907262809731705)
        ·
          refine ⟨26732675539430447107298779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35643567385907262809731705 26732675539430447107298779)
          ·
            refine ⟨40099013309145670660948169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26732675539430447107298779 40099013309145670660948169)
            ·
              refine ⟨30074259981859252995711127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40099013309145670660948169 30074259981859252995711127)
              ·
                refine ⟨45111389972788879493566691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30074259981859252995711127 45111389972788879493566691)
                ·
                  refine ⟨67667084959183319240350037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45111389972788879493566691 67667084959183319240350037)
                  ·
                    refine ⟨198243412966357380586963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 67667084959183319240350037 198243412966357380586963)
                    ·
                      rfl

theorem cell23_1158233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_1158233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158233 prefixEnd_1158233 := by exact prefixLift 1158233
  have htrace : WordTrace (prefixWord ++ tailWord_1158233) baseStart_1158233 baseEnd_1158233 := by
    simpa [prefixWord, tailWord_1158233, baseEnd_1158233] using wordTrace_append hprefix tailTrace_1158233
  have hstable : (prefixWord ++ tailWord_1158233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158233).length < 2 ^ (prefixWord ++ tailWord_1158233).sum := by decide
  have hdescent : baseEnd_1158233 < baseStart_1158233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158240 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1158240 : Nat := 118140960795 + 1158240 * 2 ^ 59
def prefixEnd_1158240 : Nat := 4983230072969 + 3 ^ 40 * 1158240 * 2
def baseEnd_1158240 : Nat := 594733833263653614373357

theorem tailTrace_1158240 : CollatzResearch.WordTrace tailWord_1158240 prefixEnd_1158240 594733833263653614373357 := by
  unfold tailWord_1158240
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122241661950883244260087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28162988882601177659013449 21122241661950883244260087)
  ·
    refine ⟨31683362492926324866390131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21122241661950883244260087 31683362492926324866390131)
    ·
      refine ⟨47525043739389487299585197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31683362492926324866390131 47525043739389487299585197)
      ·
        refine ⟨17821891402271057737344449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47525043739389487299585197 17821891402271057737344449)
        ·
          refine ⟨13366418551703293303008337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17821891402271057737344449 13366418551703293303008337)
          ·
            refine ⟨10024813913777469977256253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13366418551703293303008337 10024813913777469977256253)
            ·
              refine ⟨3759305217666551241471095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10024813913777469977256253 3759305217666551241471095)
              ·
                refine ⟨5638957826499826862206643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759305217666551241471095 5638957826499826862206643)
                ·
                  refine ⟨8458436739749740293309965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638957826499826862206643 8458436739749740293309965)
                  ·
                    refine ⟨3171913777406152609991237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8458436739749740293309965 3171913777406152609991237)
                    ·
                      refine ⟨594733833263653614373357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3171913777406152609991237 594733833263653614373357)
                      ·
                        rfl

theorem cell23_1158240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1158240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158240 prefixEnd_1158240 := by exact prefixLift 1158240
  have htrace : WordTrace (prefixWord ++ tailWord_1158240) baseStart_1158240 baseEnd_1158240 := by
    simpa [prefixWord, tailWord_1158240, baseEnd_1158240] using wordTrace_append hprefix tailTrace_1158240
  have hstable : (prefixWord ++ tailWord_1158240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158240).length < 2 ^ (prefixWord ++ tailWord_1158240).sum := by decide
  have hdescent : baseEnd_1158240 < baseStart_1158240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158307 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1158307 : Nat := 118140960795 + 1158307 * 2 ^ 59
def prefixEnd_1158307 : Nat := 4983230072969 + 3 ^ 40 * 1158307 * 2
def baseEnd_1158307 : Nat := 594768236467504852235549

theorem tailTrace_1158307 : CollatzResearch.WordTrace tailWord_1158307 prefixEnd_1158307 594768236467504852235549 := by
  unfold tailWord_1158307
  simp only [CollatzResearch.WordTrace]
  refine ⟨42246927014659036931209175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28164618009772691287472783 42246927014659036931209175)
  ·
    refine ⟨63370390521988555396813763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42246927014659036931209175 63370390521988555396813763)
    ·
      refine ⟨95055585782982833095220645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63370390521988555396813763 95055585782982833095220645)
      ·
        refine ⟨17822922334309281205353871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95055585782982833095220645 17822922334309281205353871)
        ·
          refine ⟨26734383501463921808030807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822922334309281205353871 26734383501463921808030807)
          ·
            refine ⟨40101575252195882712046211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26734383501463921808030807 40101575252195882712046211)
            ·
              refine ⟨60152362878293824068069317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40101575252195882712046211 60152362878293824068069317)
              ·
                refine ⟨11278568039680092012762997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60152362878293824068069317 11278568039680092012762997)
                ·
                  refine ⟨1057365753720008626196531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11278568039680092012762997 1057365753720008626196531)
                  ·
                    refine ⟨1586048630580012939294797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1057365753720008626196531 1586048630580012939294797)
                    ·
                      refine ⟨594768236467504852235549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586048630580012939294797 594768236467504852235549)
                      ·
                        rfl

theorem cell23_1158307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1158307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158307 prefixEnd_1158307 := by exact prefixLift 1158307
  have htrace : WordTrace (prefixWord ++ tailWord_1158307) baseStart_1158307 baseEnd_1158307 := by
    simpa [prefixWord, tailWord_1158307, baseEnd_1158307] using wordTrace_append hprefix tailTrace_1158307
  have hstable : (prefixWord ++ tailWord_1158307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158307).length < 2 ^ (prefixWord ++ tailWord_1158307).sum := by decide
  have hdescent : baseEnd_1158307 < baseStart_1158307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158330 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1158330 : Nat := 118140960795 + 1158330 * 2 ^ 59
def prefixEnd_1158330 : Nat := 4983230072969 + 3 ^ 40 * 1158330 * 2
def baseEnd_1158330 : Nat := 594780046522558262247943

theorem tailTrace_1158330 : CollatzResearch.WordTrace tailWord_1158330 prefixEnd_1158330 594780046522558262247943 := by
  unfold tailWord_1158330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561941473393927964824111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28165177262383807906197629 10561941473393927964824111)
  ·
    refine ⟨15842912210090891947236167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10561941473393927964824111 15842912210090891947236167)
    ·
      refine ⟨23764368315136337920854251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15842912210090891947236167 23764368315136337920854251)
      ·
        refine ⟨35646552472704506881281377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23764368315136337920854251 35646552472704506881281377)
        ·
          refine ⟨26734914354528380160961033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35646552472704506881281377 26734914354528380160961033)
          ·
            refine ⟨20051185765896285120720775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734914354528380160961033 20051185765896285120720775)
            ·
              refine ⟨30076778648844427681081163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20051185765896285120720775 30076778648844427681081163)
              ·
                refine ⟨45115167973266641521621745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30076778648844427681081163 45115167973266641521621745)
                ·
                  refine ⟨33836375979949981141216309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45115167973266641521621745 33836375979949981141216309)
                  ·
                    refine ⟨3172160248120310731989029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33836375979949981141216309 3172160248120310731989029)
                    ·
                      refine ⟨594780046522558262247943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3172160248120310731989029 594780046522558262247943)
                      ·
                        rfl

theorem cell23_1158330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1158330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158330 prefixEnd_1158330 := by exact prefixLift 1158330
  have htrace : WordTrace (prefixWord ++ tailWord_1158330) baseStart_1158330 baseEnd_1158330 := by
    simpa [prefixWord, tailWord_1158330, baseEnd_1158330] using wordTrace_append hprefix tailTrace_1158330
  have hstable : (prefixWord ++ tailWord_1158330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158330).length < 2 ^ (prefixWord ++ tailWord_1158330).sum := by decide
  have hdescent : baseEnd_1158330 < baseStart_1158330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158347 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 4]
def baseStart_1158347 : Nat := 118140960795 + 1158347 * 2 ^ 59
def prefixEnd_1158347 : Nat := 4983230072969 + 3 ^ 40 * 1158347 * 2
def baseEnd_1158347 : Nat := 594788775693684695735365

theorem tailTrace_1158347 : CollatzResearch.WordTrace tailWord_1158347 prefixEnd_1158347 594788775693684695735365 := by
  unfold tailWord_1158347
  simp only [CollatzResearch.WordTrace]
  refine ⟨42248385934514123762665295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28165590623009415841776863 42248385934514123762665295)
  ·
    refine ⟨63372578901771185643997943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42248385934514123762665295 63372578901771185643997943)
    ·
      refine ⟨95058868352656778465996915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63372578901771185643997943 95058868352656778465996915)
      ·
        refine ⟨142588302528985167698995373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95058868352656778465996915 142588302528985167698995373)
        ·
          refine ⟨53470613448369437887123265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142588302528985167698995373 53470613448369437887123265)
          ·
            refine ⟨40102960086277078415342449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53470613448369437887123265 40102960086277078415342449)
            ·
              refine ⟨30077220064707808811506837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40102960086277078415342449 30077220064707808811506837)
              ·
                refine ⟨1409869690533178538039383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30077220064707808811506837 1409869690533178538039383)
                ·
                  refine ⟨2114804535799767807059075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409869690533178538039383 2114804535799767807059075)
                  ·
                    refine ⟨3172206803699651710588613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2114804535799767807059075 3172206803699651710588613)
                    ·
                      refine ⟨594788775693684695735365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3172206803699651710588613 594788775693684695735365)
                      ·
                        rfl

theorem cell23_1158347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 4].length) (baseStart_1158347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158347 prefixEnd_1158347 := by exact prefixLift 1158347
  have htrace : WordTrace (prefixWord ++ tailWord_1158347) baseStart_1158347 baseEnd_1158347 := by
    simpa [prefixWord, tailWord_1158347, baseEnd_1158347] using wordTrace_append hprefix tailTrace_1158347
  have hstable : (prefixWord ++ tailWord_1158347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158347).length < 2 ^ (prefixWord ++ tailWord_1158347).sum := by decide
  have hdescent : baseEnd_1158347 < baseStart_1158347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158357 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1158357 : Nat := 118140960795 + 1158357 * 2 ^ 59
def prefixEnd_1158357 : Nat := 4983230072969 + 3 ^ 40 * 1158357 * 2
def baseEnd_1158357 : Nat := 198264636833409885536773

theorem tailTrace_1158357 : CollatzResearch.WordTrace tailWord_1158357 prefixEnd_1158357 198264636833409885536773 := by
  unfold tailWord_1158357
  simp only [CollatzResearch.WordTrace]
  refine ⟨42248750664477895470529325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28165833776318596980352883 42248750664477895470529325)
  ·
    refine ⟨15843281499179210801448497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42248750664477895470529325 15843281499179210801448497)
    ·
      refine ⟨11882461124384408101086373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15843281499179210801448497 11882461124384408101086373)
      ·
        refine ⟨2227961460822076518953695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11882461124384408101086373 2227961460822076518953695)
        ·
          refine ⟨3341942191233114778430543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227961460822076518953695 3341942191233114778430543)
          ·
            refine ⟨5012913286849672167645815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341942191233114778430543 5012913286849672167645815)
            ·
              refine ⟨7519369930274508251468723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012913286849672167645815 7519369930274508251468723)
              ·
                refine ⟨11279054895411762377203085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7519369930274508251468723 11279054895411762377203085)
                ·
                  refine ⟨4229645585779410891451157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11279054895411762377203085 4229645585779410891451157)
                  ·
                    refine ⟨198264636833409885536773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4229645585779410891451157 198264636833409885536773)
                    ·
                      rfl

theorem cell23_1158357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1158357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158357 prefixEnd_1158357 := by exact prefixLift 1158357
  have htrace : WordTrace (prefixWord ++ tailWord_1158357) baseStart_1158357 baseEnd_1158357 := by
    simpa [prefixWord, tailWord_1158357, baseEnd_1158357] using wordTrace_append hprefix tailTrace_1158357
  have hstable : (prefixWord ++ tailWord_1158357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158357).length < 2 ^ (prefixWord ++ tailWord_1158357).sum := by decide
  have hdescent : baseEnd_1158357 < baseStart_1158357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158367 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1158367 : Nat := 118140960795 + 1158367 * 2 ^ 59
def prefixEnd_1158367 : Nat := 4983230072969 + 3 ^ 40 * 1158367 * 2
def baseEnd_1158367 : Nat := 594799045306774617485273

theorem tailTrace_1158367 : CollatzResearch.WordTrace tailWord_1158367 prefixEnd_1158367 594799045306774617485273 := by
  unfold tailWord_1158367
  simp only [CollatzResearch.WordTrace]
  refine ⟨42249115394441667178393355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28166076929627778118928903 42249115394441667178393355)
  ·
    refine ⟨63373673091662500767590033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42249115394441667178393355 63373673091662500767590033)
    ·
      refine ⟨47530254818746875575692525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63373673091662500767590033 47530254818746875575692525)
      ·
        refine ⟨17823845557030078340884697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47530254818746875575692525 17823845557030078340884697)
        ·
          refine ⟨13367884167772558755663523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17823845557030078340884697 13367884167772558755663523)
          ·
            refine ⟨20051826251658838133495285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13367884167772558755663523 20051826251658838133495285)
            ·
              refine ⟨1879858711093016075015183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20051826251658838133495285 1879858711093016075015183)
              ·
                refine ⟨2819788066639524112522775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879858711093016075015183 2819788066639524112522775)
                ·
                  refine ⟨4229682099959286168784163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819788066639524112522775 4229682099959286168784163)
                  ·
                    refine ⟨6344523149938929253176245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229682099959286168784163 6344523149938929253176245)
                    ·
                      refine ⟨594799045306774617485273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6344523149938929253176245 594799045306774617485273)
                      ·
                        rfl

theorem cell23_1158367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1158367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158367 prefixEnd_1158367 := by exact prefixLift 1158367
  have htrace : WordTrace (prefixWord ++ tailWord_1158367) baseStart_1158367 baseEnd_1158367 := by
    simpa [prefixWord, tailWord_1158367, baseEnd_1158367] using wordTrace_append hprefix tailTrace_1158367
  have hstable : (prefixWord ++ tailWord_1158367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158367).length < 2 ^ (prefixWord ++ tailWord_1158367).sum := by decide
  have hdescent : baseEnd_1158367 < baseStart_1158367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158387 : List Nat := [1, 1, 1, 2, 2, 7, 1, 8]
def baseStart_1158387 : Nat := 118140960795 + 1158387 * 2 ^ 59
def prefixEnd_1158387 : Nat := 4983230072969 + 3 ^ 40 * 1158387 * 2
def baseEnd_1158387 : Nat := 22029974626661649601303

theorem tailTrace_1158387 : CollatzResearch.WordTrace tailWord_1158387 prefixEnd_1158387 22029974626661649601303 := by
  unfold tailWord_1158387
  simp only [CollatzResearch.WordTrace]
  refine ⟨42249844854369210594121415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28166563236246140396080943 42249844854369210594121415)
  ·
    refine ⟨63374767281553815891182123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42249844854369210594121415 63374767281553815891182123)
    ·
      refine ⟨95062150922330723836773185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63374767281553815891182123 95062150922330723836773185)
      ·
        refine ⟨71296613191748042877579889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95062150922330723836773185 71296613191748042877579889)
        ·
          refine ⟨53472459893811032158184917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71296613191748042877579889 53472459893811032158184917)
          ·
            refine ⟨1253260778761196066207459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53472459893811032158184917 1253260778761196066207459)
            ·
              refine ⟨1879891168141794099311189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253260778761196066207459 1879891168141794099311189)
              ·
                refine ⟨22029974626661649601303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1879891168141794099311189 22029974626661649601303)
                ·
                  rfl

theorem cell23_1158387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 8].length) (baseStart_1158387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158387 prefixEnd_1158387 := by exact prefixLift 1158387
  have htrace : WordTrace (prefixWord ++ tailWord_1158387) baseStart_1158387 baseEnd_1158387 := by
    simpa [prefixWord, tailWord_1158387, baseEnd_1158387] using wordTrace_append hprefix tailTrace_1158387
  have hstable : (prefixWord ++ tailWord_1158387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158387).length < 2 ^ (prefixWord ++ tailWord_1158387).sum := by decide
  have hdescent : baseEnd_1158387 < baseStart_1158387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158398 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_1158398 : Nat := 118140960795 + 1158398 * 2 ^ 59
def prefixEnd_1158398 : Nat := 4983230072969 + 3 ^ 40 * 1158398 * 2
def baseEnd_1158398 : Nat := 594814963207063996197631

theorem tailTrace_1158398 : CollatzResearch.WordTrace tailWord_1158398 prefixEnd_1158398 594814963207063996197631 := by
  unfold tailWord_1158398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281280757166169934096481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28166830704886239648514565 5281280757166169934096481)
  ·
    refine ⟨3960960567874627450572361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5281280757166169934096481 3960960567874627450572361)
    ·
      refine ⟨2970720425905970587929271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960960567874627450572361 2970720425905970587929271)
      ·
        refine ⟨4456080638858955881893907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970720425905970587929271 4456080638858955881893907)
        ·
          refine ⟨6684120958288433822840861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456080638858955881893907 6684120958288433822840861)
          ·
            refine ⟨2506545359358162683565323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6684120958288433822840861 2506545359358162683565323)
            ·
              refine ⟨3759818039037244025347985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506545359358162683565323 3759818039037244025347985)
              ·
                refine ⟨2819863529277933019010989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759818039037244025347985 2819863529277933019010989)
                ·
                  refine ⟨1057448823479224882129121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2819863529277933019010989 1057448823479224882129121)
                  ·
                    refine ⟨793086617609418661596841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057448823479224882129121 793086617609418661596841)
                    ·
                      refine ⟨594814963207063996197631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793086617609418661596841 594814963207063996197631)
                      ·
                        rfl

theorem cell23_1158398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_1158398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158398 prefixEnd_1158398 := by exact prefixLift 1158398
  have htrace : WordTrace (prefixWord ++ tailWord_1158398) baseStart_1158398 baseEnd_1158398 := by
    simpa [prefixWord, tailWord_1158398, baseEnd_1158398] using wordTrace_append hprefix tailTrace_1158398
  have hstable : (prefixWord ++ tailWord_1158398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158398).length < 2 ^ (prefixWord ++ tailWord_1158398).sum := by decide
  have hdescent : baseEnd_1158398 < baseStart_1158398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158400 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_1158400 : Nat := 118140960795 + 1158400 * 2 ^ 59
def prefixEnd_1158400 : Nat := 4983230072969 + 3 ^ 40 * 1158400 * 2
def baseEnd_1158400 : Nat := 198271996722790996124207

theorem tailTrace_1158400 : CollatzResearch.WordTrace tailWord_1158400 prefixEnd_1158400 198271996722790996124207 := by
  unfold tailWord_1158400
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125159501661056907172327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28166879335548075876229769 21125159501661056907172327)
  ·
    refine ⟨31687739252491585360758491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21125159501661056907172327 31687739252491585360758491)
    ·
      refine ⟨47531608878737378041137737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31687739252491585360758491 47531608878737378041137737)
      ·
        refine ⟨35648706659053033530853303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47531608878737378041137737 35648706659053033530853303)
        ·
          refine ⟨53473059988579550296279955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35648706659053033530853303 53473059988579550296279955)
          ·
            refine ⟨80209589982869325444419933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53473059988579550296279955 80209589982869325444419933)
            ·
              refine ⟨30078596243575997041657475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80209589982869325444419933 30078596243575997041657475)
              ·
                refine ⟨45117894365363995562486213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30078596243575997041657475 45117894365363995562486213)
                ·
                  refine ⟨8459605193505749167966165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45117894365363995562486213 8459605193505749167966165)
                  ·
                    refine ⟨198271996722790996124207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8459605193505749167966165 198271996722790996124207)
                    ·
                      rfl

theorem cell23_1158400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_1158400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158400 prefixEnd_1158400 := by exact prefixLift 1158400
  have htrace : WordTrace (prefixWord ++ tailWord_1158400) baseStart_1158400 baseEnd_1158400 := by
    simpa [prefixWord, tailWord_1158400, baseEnd_1158400] using wordTrace_append hprefix tailTrace_1158400
  have hstable : (prefixWord ++ tailWord_1158400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158400).length < 2 ^ (prefixWord ++ tailWord_1158400).sum := by decide
  have hdescent : baseEnd_1158400 < baseStart_1158400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158404 : List Nat := [2, 3, 2, 2, 2, 2, 3, 7]
def baseStart_1158404 : Nat := 118140960795 + 1158404 * 2 ^ 59
def prefixEnd_1158404 : Nat := 4983230072969 + 3 ^ 40 * 1158404 * 2
def baseEnd_1158404 : Nat := 22030297929295961952689

theorem tailTrace_1158404 : CollatzResearch.WordTrace tailWord_1158404 prefixEnd_1158404 22030297929295961952689 := by
  unfold tailWord_1158404
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125232447653811248745133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28166976596871748331660177 21125232447653811248745133)
  ·
    refine ⟨7921962167870179218279425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21125232447653811248745133 7921962167870179218279425)
    ·
      refine ⟨5941471625902634413709569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7921962167870179218279425 5941471625902634413709569)
      ·
        refine ⟨4456103719426975810282177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5941471625902634413709569 4456103719426975810282177)
        ·
          refine ⟨3342077789570231857711633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4456103719426975810282177 3342077789570231857711633)
          ·
            refine ⟨2506558342177673893283725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342077789570231857711633 2506558342177673893283725)
            ·
              refine ⟨939959378316627709981397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506558342177673893283725 939959378316627709981397)
              ·
                refine ⟨22030297929295961952689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 939959378316627709981397 22030297929295961952689)
                ·
                  rfl

theorem cell23_1158404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 7].length) (baseStart_1158404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158404 prefixEnd_1158404 := by exact prefixLift 1158404
  have htrace : WordTrace (prefixWord ++ tailWord_1158404) baseStart_1158404 baseEnd_1158404 := by
    simpa [prefixWord, tailWord_1158404, baseEnd_1158404] using wordTrace_append hprefix tailTrace_1158404
  have hstable : (prefixWord ++ tailWord_1158404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158404).length < 2 ^ (prefixWord ++ tailWord_1158404).sum := by decide
  have hdescent : baseEnd_1158404 < baseStart_1158404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158414 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1158414 : Nat := 118140960795 + 1158414 * 2 ^ 59
def prefixEnd_1158414 : Nat := 4983230072969 + 3 ^ 40 * 1158414 * 2
def baseEnd_1158414 : Nat := 594823178897535933597557

theorem tailTrace_1158414 : CollatzResearch.WordTrace tailWord_1158414 prefixEnd_1158414 594823178897535933597557 := by
  unfold tailWord_1158414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281353703158924275669287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28167219750180929470236197 5281353703158924275669287)
  ·
    refine ⟨7922030554738386413503931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281353703158924275669287 7922030554738386413503931)
    ·
      refine ⟨11883045832107579620255897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922030554738386413503931 11883045832107579620255897)
      ·
        refine ⟨8912284374080684715191923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11883045832107579620255897 8912284374080684715191923)
        ·
          refine ⟨13368426561121027072787885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912284374080684715191923 13368426561121027072787885)
          ·
            refine ⟨5013159960420385152295457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13368426561121027072787885 5013159960420385152295457)
            ·
              refine ⟨3759869970315288864221593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013159960420385152295457 3759869970315288864221593)
              ·
                refine ⟨2819902477736466648166195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759869970315288864221593 2819902477736466648166195)
                ·
                  refine ⟨4229853716604699972249293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819902477736466648166195 4229853716604699972249293)
                  ·
                    refine ⟨1586195143726762489593485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4229853716604699972249293 1586195143726762489593485)
                    ·
                      refine ⟨594823178897535933597557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586195143726762489593485 594823178897535933597557)
                      ·
                        rfl

theorem cell23_1158414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1158414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158414 prefixEnd_1158414 := by exact prefixLift 1158414
  have htrace : WordTrace (prefixWord ++ tailWord_1158414) baseStart_1158414 baseEnd_1158414 := by
    simpa [prefixWord, tailWord_1158414, baseEnd_1158414] using wordTrace_append hprefix tailTrace_1158414
  have hstable : (prefixWord ++ tailWord_1158414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158414).length < 2 ^ (prefixWord ++ tailWord_1158414).sum := by decide
  have hdescent : baseEnd_1158414 < baseStart_1158414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158431 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1158431 : Nat := 118140960795 + 1158431 * 2 ^ 59
def prefixEnd_1158431 : Nat := 4983230072969 + 3 ^ 40 * 1158431 * 2
def baseEnd_1158431 : Nat := 594831908068662367084979

theorem tailTrace_1158431 : CollatzResearch.WordTrace tailWord_1158431 prefixEnd_1158431 594831908068662367084979 := by
  unfold tailWord_1158431
  simp only [CollatzResearch.WordTrace]
  refine ⟨42251449666209806108723147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28167633110806537405815431 42251449666209806108723147)
  ·
    refine ⟨63377174499314709163084721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42251449666209806108723147 63377174499314709163084721)
    ·
      refine ⟨47532880874486031872313541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63377174499314709163084721 47532880874486031872313541)
      ·
        refine ⟨8912415163966130976058789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47532880874486031872313541 8912415163966130976058789)
        ·
          refine ⟨1671077843243649558011023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8912415163966130976058789 1671077843243649558011023)
          ·
            refine ⟨2506616764865474337016535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671077843243649558011023 2506616764865474337016535)
            ·
              refine ⟨3759925147298211505524803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506616764865474337016535 3759925147298211505524803)
              ·
                refine ⟨5639887720947317258287205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759925147298211505524803 5639887720947317258287205)
                ·
                  refine ⟨1057478947677621985928851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5639887720947317258287205 1057478947677621985928851)
                  ·
                    refine ⟨1586218421516432978893277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1057478947677621985928851 1586218421516432978893277)
                    ·
                      refine ⟨594831908068662367084979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586218421516432978893277 594831908068662367084979)
                      ·
                        rfl

theorem cell23_1158431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1158431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158431 prefixEnd_1158431 := by exact prefixLift 1158431
  have htrace : WordTrace (prefixWord ++ tailWord_1158431) baseStart_1158431 baseEnd_1158431 := by
    simpa [prefixWord, tailWord_1158431, baseEnd_1158431] using wordTrace_append hprefix tailTrace_1158431
  have hstable : (prefixWord ++ tailWord_1158431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158431).length < 2 ^ (prefixWord ++ tailWord_1158431).sum := by decide
  have hdescent : baseEnd_1158431 < baseStart_1158431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158471 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_1158471 : Nat := 118140960795 + 1158471 * 2 ^ 59
def prefixEnd_1158471 : Nat := 4983230072969 + 3 ^ 40 * 1158471 * 2
def baseEnd_1158471 : Nat := 594852447294842210584795

theorem tailTrace_1158471 : CollatzResearch.WordTrace tailWord_1158471 prefixEnd_1158471 594852447294842210584795 := by
  unfold tailWord_1158471
  simp only [CollatzResearch.WordTrace]
  refine ⟨42252908586064892940179267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28168605724043261960119511 42252908586064892940179267)
  ·
    refine ⟨63379362879097339410268901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42252908586064892940179267 63379362879097339410268901)
    ·
      refine ⟨11883630539830751139425419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63379362879097339410268901 11883630539830751139425419)
      ·
        refine ⟨17825445809746126709138129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883630539830751139425419 17825445809746126709138129)
        ·
          refine ⟨13369084357309595031853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17825445809746126709138129 13369084357309595031853597)
          ·
            refine ⟨5013406633991098136945099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13369084357309595031853597 5013406633991098136945099)
            ·
              refine ⟨7520109950986647205417649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013406633991098136945099 7520109950986647205417649)
              ·
                refine ⟨5640082463239985404063237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7520109950986647205417649 5640082463239985404063237)
                ·
                  refine ⟨1057515461857497263261857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5640082463239985404063237 1057515461857497263261857)
                  ·
                    refine ⟨793136596393122947446393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057515461857497263261857 793136596393122947446393)
                    ·
                      refine ⟨594852447294842210584795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793136596393122947446393 594852447294842210584795)
                      ·
                        rfl

theorem cell23_1158471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_1158471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158471 prefixEnd_1158471 := by exact prefixLift 1158471
  have htrace : WordTrace (prefixWord ++ tailWord_1158471) baseStart_1158471 baseEnd_1158471 := by
    simpa [prefixWord, tailWord_1158471, baseEnd_1158471] using wordTrace_append hprefix tailTrace_1158471
  have hstable : (prefixWord ++ tailWord_1158471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158471).length < 2 ^ (prefixWord ++ tailWord_1158471).sum := by decide
  have hdescent : baseEnd_1158471 < baseStart_1158471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158524 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1158524 : Nat := 118140960795 + 1158524 * 2 ^ 59
def prefixEnd_1158524 : Nat := 4983230072969 + 3 ^ 40 * 1158524 * 2
def baseEnd_1158524 : Nat := 198293220589843501074017

theorem tailTrace_1158524 : CollatzResearch.WordTrace tailWord_1158524 prefixEnd_1158524 198293220589843501074017 := by
  unfold tailWord_1158524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21127420827436441495929313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28169894436581921994572417 21127420827436441495929313)
  ·
    refine ⟨15845565620577331121946985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21127420827436441495929313 15845565620577331121946985)
    ·
      refine ⟨11884174215432998341460239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15845565620577331121946985 11884174215432998341460239)
      ·
        refine ⟨17826261323149497512190359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884174215432998341460239 17826261323149497512190359)
        ·
          refine ⟨26739391984724246268285539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17826261323149497512190359 26739391984724246268285539)
          ·
            refine ⟨40109087977086369402428309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26739391984724246268285539 40109087977086369402428309)
            ·
              refine ⟨1880113498925923565738827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40109087977086369402428309 1880113498925923565738827)
              ·
                refine ⟨2820170248388885348608241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880113498925923565738827 2820170248388885348608241)
                ·
                  refine ⟨2115127686291664011456181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820170248388885348608241 2115127686291664011456181)
                  ·
                    refine ⟨198293220589843501074017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2115127686291664011456181 198293220589843501074017)
                    ·
                      rfl

theorem cell23_1158524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1158524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158524 prefixEnd_1158524 := by exact prefixLift 1158524
  have htrace : WordTrace (prefixWord ++ tailWord_1158524) baseStart_1158524 baseEnd_1158524 := by
    simpa [prefixWord, tailWord_1158524, baseEnd_1158524] using wordTrace_append hprefix tailTrace_1158524
  have hstable : (prefixWord ++ tailWord_1158524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158524).length < 2 ^ (prefixWord ++ tailWord_1158524).sum := by decide
  have hdescent : baseEnd_1158524 < baseStart_1158524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158564 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1158564 : Nat := 118140960795 + 1158564 * 2 ^ 59
def prefixEnd_1158564 : Nat := 4983230072969 + 3 ^ 40 * 1158564 * 2
def baseEnd_1158564 : Nat := 594900200995710346721867

theorem tailTrace_1158564 : CollatzResearch.WordTrace tailWord_1158564 prefixEnd_1158564 594900200995710346721867 := by
  unfold tailWord_1158564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21128150287363984911657373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28170867049818646548876497 21128150287363984911657373)
  ·
    refine ⟨7923056357761494341871515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21128150287363984911657373 7923056357761494341871515)
    ·
      refine ⟨11884584536642241512807273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923056357761494341871515 11884584536642241512807273)
      ·
        refine ⟨8913438402481681134605455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11884584536642241512807273 8913438402481681134605455)
        ·
          refine ⟨13370157603722521701908183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913438402481681134605455 13370157603722521701908183)
          ·
            refine ⟨20055236405583782552862275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370157603722521701908183 20055236405583782552862275)
            ·
              refine ⟨30082854608375673829293413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20055236405583782552862275 30082854608375673829293413)
              ·
                refine ⟨5640535239070438842992515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30082854608375673829293413 5640535239070438842992515)
                ·
                  refine ⟨8460802858605658264488773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640535239070438842992515 8460802858605658264488773)
                  ·
                    refine ⟨1586400535988560924591645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8460802858605658264488773 1586400535988560924591645)
                    ·
                      refine ⟨594900200995710346721867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586400535988560924591645 594900200995710346721867)
                      ·
                        rfl

theorem cell23_1158564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1158564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158564 prefixEnd_1158564 := by exact prefixLift 1158564
  have htrace : WordTrace (prefixWord ++ tailWord_1158564) baseStart_1158564 baseEnd_1158564 := by
    simpa [prefixWord, tailWord_1158564, baseEnd_1158564] using wordTrace_append hprefix tailTrace_1158564
  have hstable : (prefixWord ++ tailWord_1158564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158564).length < 2 ^ (prefixWord ++ tailWord_1158564).sum := by decide
  have hdescent : baseEnd_1158564 < baseStart_1158564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158581 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1158581 : Nat := 118140960795 + 1158581 * 2 ^ 59
def prefixEnd_1158581 : Nat := 4983230072969 + 3 ^ 40 * 1158581 * 2
def baseEnd_1158581 : Nat := 594908930166836780209289

theorem tailTrace_1158581 : CollatzResearch.WordTrace tailWord_1158581 prefixEnd_1158581 594908930166836780209289 := by
  unfold tailWord_1158581
  simp only [CollatzResearch.WordTrace]
  refine ⟨42256920615666381726683597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28171280410444254484455731 42256920615666381726683597)
  ·
    refine ⟨15846345230874893147506349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42256920615666381726683597 15846345230874893147506349)
    ·
      refine ⟨5942379461578084930314881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15846345230874893147506349 5942379461578084930314881)
      ·
        refine ⟨4456784596183563697736161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5942379461578084930314881 4456784596183563697736161)
        ·
          refine ⟨3342588447137672773302121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4456784596183563697736161 3342588447137672773302121)
          ·
            refine ⟨2506941335353254579976591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342588447137672773302121 2506941335353254579976591)
            ·
              refine ⟨3760412003029881869964887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506941335353254579976591 3760412003029881869964887)
              ·
                refine ⟨5640618004544822804947331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760412003029881869964887 5640618004544822804947331)
                ·
                  refine ⟨8460927006817234207420997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640618004544822804947331 8460927006817234207420997)
                  ·
                    refine ⟨1586423813778231413891437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8460927006817234207420997 1586423813778231413891437)
                    ·
                      refine ⟨594908930166836780209289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586423813778231413891437 594908930166836780209289)
                      ·
                        rfl

theorem cell23_1158581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1158581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158581 prefixEnd_1158581 := by exact prefixLift 1158581
  have htrace : WordTrace (prefixWord ++ tailWord_1158581) baseStart_1158581 baseEnd_1158581 := by
    simpa [prefixWord, tailWord_1158581, baseEnd_1158581] using wordTrace_append hprefix tailTrace_1158581
  have hstable : (prefixWord ++ tailWord_1158581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158581).length < 2 ^ (prefixWord ++ tailWord_1158581).sum := by decide
  have hdescent : baseEnd_1158581 < baseStart_1158581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158604 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1158604 : Nat := 118140960795 + 1158604 * 2 ^ 59
def prefixEnd_1158604 : Nat := 4983230072969 + 3 ^ 40 * 1158604 * 2
def baseEnd_1158604 : Nat := 594920740221890190221683

theorem tailTrace_1158604 : CollatzResearch.WordTrace tailWord_1158604 prefixEnd_1158604 594920740221890190221683 := by
  unfold tailWord_1158604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21128879747291528327385433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28171839663055371103180577 21128879747291528327385433)
  ·
    refine ⟨15846659810468646245539075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21128879747291528327385433 15846659810468646245539075)
    ·
      refine ⟨23769989715702969368308613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15846659810468646245539075 23769989715702969368308613)
      ·
        refine ⟨4456873071694306756557865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23769989715702969368308613 4456873071694306756557865)
        ·
          refine ⟨3342654803770730067418399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4456873071694306756557865 3342654803770730067418399)
          ·
            refine ⟨5013982205656095101127599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342654803770730067418399 5013982205656095101127599)
            ·
              refine ⟨7520973308484142651691399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013982205656095101127599 7520973308484142651691399)
              ·
                refine ⟨11281459962726213977537099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7520973308484142651691399 11281459962726213977537099)
                ·
                  refine ⟨16922189944089320966305649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11281459962726213977537099 16922189944089320966305649)
                  ·
                    refine ⟨12691642458066990724729237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16922189944089320966305649 12691642458066990724729237)
                    ·
                      refine ⟨594920740221890190221683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12691642458066990724729237 594920740221890190221683)
                      ·
                        rfl

theorem cell23_1158604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1158604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158604 prefixEnd_1158604 := by exact prefixLift 1158604
  have htrace : WordTrace (prefixWord ++ tailWord_1158604) baseStart_1158604 baseEnd_1158604 := by
    simpa [prefixWord, tailWord_1158604, baseEnd_1158604] using wordTrace_append hprefix tailTrace_1158604
  have hstable : (prefixWord ++ tailWord_1158604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158604).length < 2 ^ (prefixWord ++ tailWord_1158604).sum := by decide
  have hdescent : baseEnd_1158604 < baseStart_1158604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158631 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1158631 : Nat := 118140960795 + 1158631 * 2 ^ 59
def prefixEnd_1158631 : Nat := 4983230072969 + 3 ^ 40 * 1158631 * 2
def baseEnd_1158631 : Nat := 198311534733187194861353

theorem tailTrace_1158631 : CollatzResearch.WordTrace tailWord_1158631 prefixEnd_1158631 198311534733187194861353 := by
  unfold tailWord_1158631
  simp only [CollatzResearch.WordTrace]
  refine ⟨42258744265485240266003747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28172496176990160177335831 42258744265485240266003747)
  ·
    refine ⟨63388116398227860399005621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42258744265485240266003747 63388116398227860399005621)
    ·
      refine ⟨5942635912333861912406777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63388116398227860399005621 5942635912333861912406777)
      ·
        refine ⟨4456976934250396434305083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5942635912333861912406777 4456976934250396434305083)
        ·
          refine ⟨6685465401375594651457625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456976934250396434305083 6685465401375594651457625)
          ·
            refine ⟨5014099051031695988593219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685465401375594651457625 5014099051031695988593219)
            ·
              refine ⟨7521148576547543982889829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014099051031695988593219 7521148576547543982889829)
              ·
                refine ⟨1410215358102664496791843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7521148576547543982889829 1410215358102664496791843)
                ·
                  refine ⟨2115323037153996745187765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410215358102664496791843 2115323037153996745187765)
                  ·
                    refine ⟨198311534733187194861353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2115323037153996745187765 198311534733187194861353)
                    ·
                      rfl

theorem cell23_1158631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1158631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158631 prefixEnd_1158631 := by exact prefixLift 1158631
  have htrace : WordTrace (prefixWord ++ tailWord_1158631) baseStart_1158631 baseEnd_1158631 := by
    simpa [prefixWord, tailWord_1158631, baseEnd_1158631] using wordTrace_append hprefix tailTrace_1158631
  have hstable : (prefixWord ++ tailWord_1158631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158631).length < 2 ^ (prefixWord ++ tailWord_1158631).sum := by decide
  have hdescent : baseEnd_1158631 < baseStart_1158631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158638 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_1158638 : Nat := 118140960795 + 1158638 * 2 ^ 59
def prefixEnd_1158638 : Nat := 4983230072969 + 3 ^ 40 * 1158638 * 2
def baseEnd_1158638 : Nat := 594938198564143057196527

theorem tailTrace_1158638 : CollatzResearch.WordTrace tailWord_1158638 prefixEnd_1158638 594938198564143057196527 := by
  unfold tailWord_1158638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282374947057485057688571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28172666384306586974339045 5282374947057485057688571)
  ·
    refine ⟨7923562420586227586532857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282374947057485057688571 7923562420586227586532857)
    ·
      refine ⟨5942671815439670689899643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7923562420586227586532857 5942671815439670689899643)
      ·
        refine ⟨8914007723159506034849465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5942671815439670689899643 8914007723159506034849465)
        ·
          refine ⟨6685505792369629526137099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8914007723159506034849465 6685505792369629526137099)
          ·
            refine ⟨10028258688554444289205649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685505792369629526137099 10028258688554444289205649)
            ·
              refine ⟨7521194016415833216904237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10028258688554444289205649 7521194016415833216904237)
              ·
                refine ⟨2820447756155937456339089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7521194016415833216904237 2820447756155937456339089)
                ·
                  refine ⟨2115335817116953092254317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2820447756155937456339089 2115335817116953092254317)
                  ·
                    refine ⟨793250931418857409595369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115335817116953092254317 793250931418857409595369)
                    ·
                      refine ⟨594938198564143057196527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793250931418857409595369 594938198564143057196527)
                      ·
                        rfl

theorem cell23_1158638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_1158638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158638 prefixEnd_1158638 := by exact prefixLift 1158638
  have htrace : WordTrace (prefixWord ++ tailWord_1158638) baseStart_1158638 baseEnd_1158638 := by
    simpa [prefixWord, tailWord_1158638, baseEnd_1158638] using wordTrace_append hprefix tailTrace_1158638
  have hstable : (prefixWord ++ tailWord_1158638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158638).length < 2 ^ (prefixWord ++ tailWord_1158638).sum := by decide
  have hdescent : baseEnd_1158638 < baseStart_1158638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158661 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_1158661 : Nat := 118140960795 + 1158661 * 2 ^ 59
def prefixEnd_1158661 : Nat := 4983230072969 + 3 ^ 40 * 1158661 * 2
def baseEnd_1158661 : Nat := 198316669539732155736307

theorem tailTrace_1158661 : CollatzResearch.WordTrace tailWord_1158661 prefixEnd_1158661 198316669539732155736307 := by
  unfold tailWord_1158661
  simp only [CollatzResearch.WordTrace]
  refine ⟨42259838455376555389595837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28173225636917703593063891 42259838455376555389595837)
  ·
    refine ⟨15847439420766208271098439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42259838455376555389595837 15847439420766208271098439)
    ·
      refine ⟨23771159131149312406647659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15847439420766208271098439 23771159131149312406647659)
      ·
        refine ⟨35656738696723968609971489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23771159131149312406647659 35656738696723968609971489)
        ·
          refine ⟨26742554022542976457478617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35656738696723968609971489 26742554022542976457478617)
          ·
            refine ⟨20056915516907232343108963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26742554022542976457478617 20056915516907232343108963)
            ·
              refine ⟨30085373275360848514663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20056915516907232343108963 30085373275360848514663445)
              ·
                refine ⟨1410251872282539774124849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30085373275360848514663445 1410251872282539774124849)
                ·
                  refine ⟨1057688904211904830593637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410251872282539774124849 1057688904211904830593637)
                  ·
                    refine ⟨198316669539732155736307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1057688904211904830593637 198316669539732155736307)
                    ·
                      rfl

theorem cell23_1158661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_1158661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158661 prefixEnd_1158661 := by exact prefixLift 1158661
  have htrace : WordTrace (prefixWord ++ tailWord_1158661) baseStart_1158661 baseEnd_1158661 := by
    simpa [prefixWord, tailWord_1158661, baseEnd_1158661] using wordTrace_append hprefix tailTrace_1158661
  have hstable : (prefixWord ++ tailWord_1158661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158661).length < 2 ^ (prefixWord ++ tailWord_1158661).sum := by decide
  have hdescent : baseEnd_1158661 < baseStart_1158661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158664 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1158664 : Nat := 118140960795 + 1158664 * 2 ^ 59
def prefixEnd_1158664 : Nat := 4983230072969 + 3 ^ 40 * 1158664 * 2
def baseEnd_1158664 : Nat := 594951549061159955471407

theorem tailTrace_1158664 : CollatzResearch.WordTrace tailWord_1158664 prefixEnd_1158664 594951549061159955471407 := by
  unfold tailWord_1158664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129973937182843450977523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28173298582910457934636697 21129973937182843450977523)
  ·
    refine ⟨31694960905774265176466285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21129973937182843450977523 31694960905774265176466285)
    ·
      refine ⟨11885610339665349441174857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31694960905774265176466285 11885610339665349441174857)
      ·
        refine ⟨8914207754749012080881143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11885610339665349441174857 8914207754749012080881143)
        ·
          refine ⟨13371311632123518121321715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8914207754749012080881143 13371311632123518121321715)
          ·
            refine ⟨20056967448185277181982573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13371311632123518121321715 20056967448185277181982573)
            ·
              refine ⟨7521362793069478943243465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20056967448185277181982573 7521362793069478943243465)
              ·
                refine ⟨5641022094802109207432599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7521362793069478943243465 5641022094802109207432599)
                ·
                  refine ⟨8461533142203163811148899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641022094802109207432599 8461533142203163811148899)
                  ·
                    refine ⟨12692299713304745716723349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8461533142203163811148899 12692299713304745716723349)
                    ·
                      refine ⟨594951549061159955471407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12692299713304745716723349 594951549061159955471407)
                      ·
                        rfl

theorem cell23_1158664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1158664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158664 prefixEnd_1158664 := by exact prefixLift 1158664
  have htrace : WordTrace (prefixWord ++ tailWord_1158664) baseStart_1158664 baseEnd_1158664 := by
    simpa [prefixWord, tailWord_1158664, baseEnd_1158664] using wordTrace_append hprefix tailTrace_1158664
  have hstable : (prefixWord ++ tailWord_1158664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158664).length < 2 ^ (prefixWord ++ tailWord_1158664).sum := by decide
  have hdescent : baseEnd_1158664 < baseStart_1158664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158669 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1158669 : Nat := 118140960795 + 1158669 * 2 ^ 59
def prefixEnd_1158669 : Nat := 4983230072969 + 3 ^ 40 * 1158669 * 2
def baseEnd_1158669 : Nat := 66106012940492492878765

theorem tailTrace_1158669 : CollatzResearch.WordTrace tailWord_1158669 prefixEnd_1158669 66106012940492492878765 := by
  unfold tailWord_1158669
  simp only [CollatzResearch.WordTrace]
  refine ⟨42260130239347572755887061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28173420159565048503924707 42260130239347572755887061)
  ·
    refine ⟨990471802484708736466103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42260130239347572755887061 990471802484708736466103)
    ·
      refine ⟨1485707703727063104699155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990471802484708736466103 1485707703727063104699155)
      ·
        refine ⟨2228561555590594657048733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485707703727063104699155 2228561555590594657048733)
        ·
          refine ⟨835710583346472996393275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2228561555590594657048733 835710583346472996393275)
          ·
            refine ⟨1253565875019709494589913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835710583346472996393275 1253565875019709494589913)
            ·
              refine ⟨940174406264782120942435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253565875019709494589913 940174406264782120942435)
              ·
                refine ⟨1410261609397173181413653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940174406264782120942435 1410261609397173181413653)
                ·
                  refine ⟨66106012940492492878765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1410261609397173181413653 66106012940492492878765)
                  ·
                    rfl

theorem cell23_1158669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1158669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158669 prefixEnd_1158669 := by exact prefixLift 1158669
  have htrace : WordTrace (prefixWord ++ tailWord_1158669) baseStart_1158669 baseEnd_1158669 := by
    simpa [prefixWord, tailWord_1158669, baseEnd_1158669] using wordTrace_append hprefix tailTrace_1158669
  have hstable : (prefixWord ++ tailWord_1158669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158669).length < 2 ^ (prefixWord ++ tailWord_1158669).sum := by decide
  have hdescent : baseEnd_1158669 < baseStart_1158669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158688 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1158688 : Nat := 118140960795 + 1158688 * 2 ^ 59
def prefixEnd_1158688 : Nat := 4983230072969 + 3 ^ 40 * 1158688 * 2
def baseEnd_1158688 : Nat := 594963872596867861571297

theorem tailTrace_1158688 : CollatzResearch.WordTrace tailWord_1158688 prefixEnd_1158688 594963872596867861571297 := by
  unfold tailWord_1158688
  simp only [CollatzResearch.WordTrace]
  refine ⟨21130411613139369500414359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28173882150852492667219145 21130411613139369500414359)
  ·
    refine ⟨31695617419709054250621539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21130411613139369500414359 31695617419709054250621539)
    ·
      refine ⟨47543426129563581375932309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31695617419709054250621539 47543426129563581375932309)
      ·
        refine ⟨2228598099823292876996827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47543426129563581375932309 2228598099823292876996827)
        ·
          refine ⟨3342897149734939315495241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228598099823292876996827 3342897149734939315495241)
          ·
            refine ⟨2507172862301204486621431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342897149734939315495241 2507172862301204486621431)
            ·
              refine ⟨3760759293451806729932147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507172862301204486621431 3760759293451806729932147)
              ·
                refine ⟨5641138940177710094898221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760759293451806729932147 5641138940177710094898221)
                ·
                  refine ⟨2115427102566641285586833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5641138940177710094898221 2115427102566641285586833)
                  ·
                    refine ⟨1586570326924980964190125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2115427102566641285586833 1586570326924980964190125)
                    ·
                      refine ⟨594963872596867861571297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586570326924980964190125 594963872596867861571297)
                      ·
                        rfl

theorem cell23_1158688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1158688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158688 prefixEnd_1158688 := by exact prefixLift 1158688
  have htrace : WordTrace (prefixWord ++ tailWord_1158688) baseStart_1158688 baseEnd_1158688 := by
    simpa [prefixWord, tailWord_1158688, baseEnd_1158688] using wordTrace_append hprefix tailTrace_1158688
  have hstable : (prefixWord ++ tailWord_1158688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158688).length < 2 ^ (prefixWord ++ tailWord_1158688).sum := by decide
  have hdescent : baseEnd_1158688 < baseStart_1158688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158719 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 1, 2, 2]
def baseStart_1158719 : Nat := 118140960795 + 1158719 * 2 ^ 59
def prefixEnd_1158719 : Nat := 4983230072969 + 3 ^ 40 * 1158719 * 2
def baseEnd_1158719 : Nat := 594979790497157240283655

theorem tailTrace_1158719 : CollatzResearch.WordTrace tailWord_1158719 prefixEnd_1158719 594979790497157240283655 := by
  unfold tailWord_1158719
  simp only [CollatzResearch.WordTrace]
  refine ⟨42261953889166431295207211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28174635926110954196804807 42261953889166431295207211)
  ·
    refine ⟨63392930833749646942810817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42261953889166431295207211 63392930833749646942810817)
    ·
      refine ⟨47544698125312235207108113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63392930833749646942810817 47544698125312235207108113)
      ·
        refine ⟨35658523593984176405331085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47544698125312235207108113 35658523593984176405331085)
        ·
          refine ⟨13371946347744066151999157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35658523593984176405331085 13371946347744066151999157)
          ·
            refine ⟨1253619970101006201749921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13371946347744066151999157 1253619970101006201749921)
            ·
              refine ⟨940214977575754651312441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253619970101006201749921 940214977575754651312441)
              ·
                refine ⟨705161233181815988484331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940214977575754651312441 705161233181815988484331)
                ·
                  refine ⟨1057741849772723982726497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705161233181815988484331 1057741849772723982726497)
                  ·
                    refine ⟨793306387329542987044873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057741849772723982726497 793306387329542987044873)
                    ·
                      refine ⟨594979790497157240283655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793306387329542987044873 594979790497157240283655)
                      ·
                        rfl

theorem cell23_1158719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_1158719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158719 prefixEnd_1158719 := by exact prefixLift 1158719
  have htrace : WordTrace (prefixWord ++ tailWord_1158719) baseStart_1158719 baseEnd_1158719 := by
    simpa [prefixWord, tailWord_1158719, baseEnd_1158719] using wordTrace_append hprefix tailTrace_1158719
  have hstable : (prefixWord ++ tailWord_1158719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158719).length < 2 ^ (prefixWord ++ tailWord_1158719).sum := by decide
  have hdescent : baseEnd_1158719 < baseStart_1158719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158742 : List Nat := [5, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1158742 : Nat := 118140960795 + 1158742 * 2 ^ 59
def prefixEnd_1158742 : Nat := 4983230072969 + 3 ^ 40 * 1158742 * 2
def baseEnd_1158742 : Nat := 22036725946378172233187

theorem tailTrace_1158742 : CollatzResearch.WordTrace tailWord_1158742 prefixEnd_1158742 22036725946378172233187 := by
  unfold tailWord_1158742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641424548005194138955905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28175195178722070815529653 2641424548005194138955905)
  ·
    refine ⟨1981068411003895604216929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2641424548005194138955905 1981068411003895604216929)
    ·
      refine ⟨1485801308252921703162697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981068411003895604216929 1485801308252921703162697)
      ·
        refine ⟨1114350981189691277372023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485801308252921703162697 1114350981189691277372023)
        ·
          refine ⟨1671526471784536916058035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114350981189691277372023 1671526471784536916058035)
          ·
            refine ⟨2507289707676805374087053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671526471784536916058035 2507289707676805374087053)
            ·
              refine ⟨940233640378802015282645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2507289707676805374087053 940233640378802015282645)
              ·
                refine ⟨22036725946378172233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 940233640378802015282645 22036725946378172233187)
                ·
                  rfl

theorem cell23_1158742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1158742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158742 prefixEnd_1158742 := by exact prefixLift 1158742
  have htrace : WordTrace (prefixWord ++ tailWord_1158742) baseStart_1158742 baseEnd_1158742 := by
    simpa [prefixWord, tailWord_1158742, baseEnd_1158742] using wordTrace_append hprefix tailTrace_1158742
  have hstable : (prefixWord ++ tailWord_1158742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158742).length < 2 ^ (prefixWord ++ tailWord_1158742).sum := by decide
  have hdescent : baseEnd_1158742 < baseStart_1158742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158762 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1158762 : Nat := 118140960795 + 1158762 * 2 ^ 59
def prefixEnd_1158762 : Nat := 4983230072969 + 3 ^ 40 * 1158762 * 2
def baseEnd_1158762 : Nat := 595001870165300572045957

theorem tailTrace_1158762 : CollatzResearch.WordTrace tailWord_1158762 prefixEnd_1158762 595001870165300572045957 := by
  unfold tailWord_1158762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10565880557002662409755635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28175681485340433092681693 10565880557002662409755635)
  ·
    refine ⟨15848820835503993614633453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10565880557002662409755635 15848820835503993614633453)
    ·
      refine ⟨5943307813313997605487545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15848820835503993614633453 5943307813313997605487545)
      ·
        refine ⟨4457480859985498204115659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5943307813313997605487545 4457480859985498204115659)
        ·
          refine ⟨6686221289978247306173489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457480859985498204115659 6686221289978247306173489)
          ·
            refine ⟨5014665967483685479630117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6686221289978247306173489 5014665967483685479630117)
            ·
              refine ⟨940249868903191027430647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5014665967483685479630117 940249868903191027430647)
              ·
                refine ⟨1410374803354786541145971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940249868903191027430647 1410374803354786541145971)
                ·
                  refine ⟨2115562205032179811718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410374803354786541145971 2115562205032179811718957)
                  ·
                    refine ⟨793335826887067429394609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115562205032179811718957 793335826887067429394609)
                    ·
                      refine ⟨595001870165300572045957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793335826887067429394609 595001870165300572045957)
                      ·
                        rfl

theorem cell23_1158762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1158762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158762 prefixEnd_1158762 := by exact prefixLift 1158762
  have htrace : WordTrace (prefixWord ++ tailWord_1158762) baseStart_1158762 baseEnd_1158762 := by
    simpa [prefixWord, tailWord_1158762, baseEnd_1158762] using wordTrace_append hprefix tailTrace_1158762
  have hstable : (prefixWord ++ tailWord_1158762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158762).length < 2 ^ (prefixWord ++ tailWord_1158762).sum := by decide
  have hdescent : baseEnd_1158762 < baseStart_1158762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158764 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 11]
def baseStart_1158764 : Nat := 118140960795 + 1158764 * 2 ^ 59
def prefixEnd_1158764 : Nat := 4983230072969 + 3 ^ 40 * 1158764 * 2
def baseEnd_1158764 : Nat := 66111433014067729357883

theorem tailTrace_1158764 : CollatzResearch.WordTrace tailWord_1158764 prefixEnd_1158764 66111433014067729357883 := by
  unfold tailWord_1158764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21131797587001701990297673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28175730116002269320396897 21131797587001701990297673)
  ·
    refine ⟨15848848190251276492723255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21131797587001701990297673 15848848190251276492723255)
    ·
      refine ⟨23773272285376914739084883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15848848190251276492723255 23773272285376914739084883)
      ·
        refine ⟨35659908428065372108627325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23773272285376914739084883 35659908428065372108627325)
        ·
          refine ⟨13372465660524514540735247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35659908428065372108627325 13372465660524514540735247)
          ·
            refine ⟨20058698490786771811102871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13372465660524514540735247 20058698490786771811102871)
            ·
              refine ⟨30088047736180157716654307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20058698490786771811102871 30088047736180157716654307)
              ·
                refine ⟨45132071604270236574981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30088047736180157716654307 45132071604270236574981461)
                ·
                  refine ⟨66111433014067729357883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 45132071604270236574981461 66111433014067729357883)
                  ·
                    rfl

theorem cell23_1158764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_1158764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158764 prefixEnd_1158764 := by exact prefixLift 1158764
  have htrace : WordTrace (prefixWord ++ tailWord_1158764) baseStart_1158764 baseEnd_1158764 := by
    simpa [prefixWord, tailWord_1158764, baseEnd_1158764] using wordTrace_append hprefix tailTrace_1158764
  have hstable : (prefixWord ++ tailWord_1158764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158764).length < 2 ^ (prefixWord ++ tailWord_1158764).sum := by decide
  have hdescent : baseEnd_1158764 < baseStart_1158764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158781 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 7]
def baseStart_1158781 : Nat := 118140960795 + 1158781 * 2 ^ 59
def prefixEnd_1158781 : Nat := 4983230072969 + 3 ^ 40 * 1158781 * 2
def baseEnd_1158781 : Nat := 66112402921970666412041

theorem tailTrace_1158781 : CollatzResearch.WordTrace tailWord_1158781 prefixEnd_1158781 66112402921970666412041 := by
  unfold tailWord_1158781
  simp only [CollatzResearch.WordTrace]
  refine ⟨42264215214941815883964197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28176143476627877255976131 42264215214941815883964197)
  ·
    refine ⟨7924540352801590478243287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42264215214941815883964197 7924540352801590478243287)
    ·
      refine ⟨11886810529202385717364931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924540352801590478243287 11886810529202385717364931)
      ·
        refine ⟨17830215793803578576047397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11886810529202385717364931 17830215793803578576047397)
        ·
          refine ⟨3343165461338170983008887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17830215793803578576047397 3343165461338170983008887)
          ·
            refine ⟨5014748192007256474513331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343165461338170983008887 5014748192007256474513331)
            ·
              refine ⟨7522122288010884711769997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014748192007256474513331 7522122288010884711769997)
              ·
                refine ⟨2820795858004081766913749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7522122288010884711769997 2820795858004081766913749)
                ·
                  refine ⟨66112402921970666412041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2820795858004081766913749 66112402921970666412041)
                  ·
                    rfl

theorem cell23_1158781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_1158781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158781 prefixEnd_1158781 := by exact prefixLift 1158781
  have htrace : WordTrace (prefixWord ++ tailWord_1158781) baseStart_1158781 baseEnd_1158781 := by
    simpa [prefixWord, tailWord_1158781, baseEnd_1158781] using wordTrace_append hprefix tailTrace_1158781
  have hstable : (prefixWord ++ tailWord_1158781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158781).length < 2 ^ (prefixWord ++ tailWord_1158781).sum := by decide
  have hdescent : baseEnd_1158781 < baseStart_1158781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158848 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2]
def baseStart_1158848 : Nat := 118140960795 + 1158848 * 2 ^ 59
def prefixEnd_1158848 : Nat := 4983230072969 + 3 ^ 40 * 1158848 * 2
def baseEnd_1158848 : Nat := 595046029501587235570561

theorem tailTrace_1158848 : CollatzResearch.WordTrace tailWord_1158848 prefixEnd_1158848 595046029501587235570561 := by
  unfold tailWord_1158848
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133329452849543163326599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28177772603799390884435465 21133329452849543163326599)
  ·
    refine ⟨31699994179274314744989899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21133329452849543163326599 31699994179274314744989899)
    ·
      refine ⟨47549991268911472117484849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31699994179274314744989899 47549991268911472117484849)
      ·
        refine ⟨35662493451683604088113637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47549991268911472117484849 35662493451683604088113637)
        ·
          refine ⟨6686717522190675766521307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35662493451683604088113637 6686717522190675766521307)
          ·
            refine ⟨10030076283286013649781961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686717522190675766521307 10030076283286013649781961)
            ·
              refine ⟨7522557212464510237336471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10030076283286013649781961 7522557212464510237336471)
              ·
                refine ⟨11283835818696765356004707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522557212464510237336471 11283835818696765356004707)
                ·
                  refine ⟨16925753728045148034007061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11283835818696765356004707 16925753728045148034007061)
                  ·
                    refine ⟨793394706002116314094081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16925753728045148034007061 793394706002116314094081)
                    ·
                      refine ⟨595046029501587235570561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793394706002116314094081 595046029501587235570561)
                      ·
                        rfl

theorem cell23_1158848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_1158848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158848 prefixEnd_1158848 := by exact prefixLift 1158848
  have htrace : WordTrace (prefixWord ++ tailWord_1158848) baseStart_1158848 baseEnd_1158848 := by
    simpa [prefixWord, tailWord_1158848, baseEnd_1158848] using wordTrace_append hprefix tailTrace_1158848
  have hstable : (prefixWord ++ tailWord_1158848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158848).length < 2 ^ (prefixWord ++ tailWord_1158848).sum := by decide
  have hdescent : baseEnd_1158848 < baseStart_1158848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158888 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 6]
def baseStart_1158888 : Nat := 118140960795 + 1158888 * 2 ^ 59
def prefixEnd_1158888 : Nat := 4983230072969 + 3 ^ 40 * 1158888 * 2
def baseEnd_1158888 : Nat := 66118507636418564341153

theorem tailTrace_1158888 : CollatzResearch.WordTrace tailWord_1158888 prefixEnd_1158888 66118507636418564341153 := by
  unfold tailWord_1158888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134058912777086579054659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28178745217036115438739545 21134058912777086579054659)
  ·
    refine ⟨31701088369165629868581989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21134058912777086579054659 31701088369165629868581989)
    ·
      refine ⟨5943954069218555600359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31701088369165629868581989 5943954069218555600359123)
      ·
        refine ⟨8915931103827833400538685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943954069218555600359123 8915931103827833400538685)
        ·
          refine ⟨3343474163935437525202007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8915931103827833400538685 3343474163935437525202007)
          ·
            refine ⟨5015211245903156287803011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343474163935437525202007 5015211245903156287803011)
            ·
              refine ⟨7522816868854734431704517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015211245903156287803011 7522816868854734431704517)
              ·
                refine ⟨1410528162910262705944597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7522816868854734431704517 1410528162910262705944597)
                ·
                  refine ⟨66118507636418564341153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1410528162910262705944597 66118507636418564341153)
                  ·
                    rfl

theorem cell23_1158888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_1158888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158888 prefixEnd_1158888 := by exact prefixLift 1158888
  have htrace : WordTrace (prefixWord ++ tailWord_1158888) baseStart_1158888 baseEnd_1158888 := by
    simpa [prefixWord, tailWord_1158888, baseEnd_1158888] using wordTrace_append hprefix tailTrace_1158888
  have hstable : (prefixWord ++ tailWord_1158888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158888).length < 2 ^ (prefixWord ++ tailWord_1158888).sum := by decide
  have hdescent : baseEnd_1158888 < baseStart_1158888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158892 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_1158892 : Nat := 118140960795 + 1158892 * 2 ^ 59
def prefixEnd_1158892 : Nat := 4983230072969 + 3 ^ 40 * 1158892 * 2
def baseEnd_1158892 : Nat := 198356207550128354473453

theorem tailTrace_1158892 : CollatzResearch.WordTrace tailWord_1158892 prefixEnd_1158892 198356207550128354473453 := by
  unfold tailWord_1158892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134131858769840920627465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28178842478359787894169953 21134131858769840920627465)
  ·
    refine ⟨15850598894077380690470599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21134131858769840920627465 15850598894077380690470599)
    ·
      refine ⟨23775898341116071035705899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15850598894077380690470599 23775898341116071035705899)
      ·
        refine ⟨35663847511674106553558849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23775898341116071035705899 35663847511674106553558849)
        ·
          refine ⟨26747885633755579915169137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35663847511674106553558849 26747885633755579915169137)
          ·
            refine ⟨20060914225316684936376853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26747885633755579915169137 20060914225316684936376853)
            ·
              refine ⟨940355354311719606392665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20060914225316684936376853 940355354311719606392665)
              ·
                refine ⟨705266515733789704794499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940355354311719606392665 705266515733789704794499)
                ·
                  refine ⟨1057899773600684557191749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705266515733789704794499 1057899773600684557191749)
                  ·
                    refine ⟨198356207550128354473453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1057899773600684557191749 198356207550128354473453)
                    ·
                      rfl

theorem cell23_1158892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_1158892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158892 prefixEnd_1158892 := by exact prefixLift 1158892
  have htrace : WordTrace (prefixWord ++ tailWord_1158892) baseStart_1158892 baseEnd_1158892 := by
    simpa [prefixWord, tailWord_1158892, baseEnd_1158892] using wordTrace_append hprefix tailTrace_1158892
  have hstable : (prefixWord ++ tailWord_1158892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158892).length < 2 ^ (prefixWord ++ tailWord_1158892).sum := by decide
  have hdescent : baseEnd_1158892 < baseStart_1158892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158919 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1158919 : Nat := 118140960795 + 1158919 * 2 ^ 59
def prefixEnd_1158919 : Nat := 4983230072969 + 3 ^ 40 * 1158919 * 2
def baseEnd_1158919 : Nat := 595082486628056457782735

theorem tailTrace_1158919 : CollatzResearch.WordTrace tailWord_1158919 prefixEnd_1158919 595082486628056457782735 := by
  unfold tailWord_1158919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42269248488441865452487811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28179498992294576968325207 42269248488441865452487811)
  ·
    refine ⟨63403872732662798178731717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42269248488441865452487811 63403872732662798178731717)
    ·
      refine ⟨11888226137374274658512197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63403872732662798178731717 11888226137374274658512197)
      ·
        refine ⟨2229042400757676498471037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11888226137374274658512197 2229042400757676498471037)
        ·
          refine ⟨835890900284128686926639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2229042400757676498471037 835890900284128686926639)
          ·
            refine ⟨1253836350426193030389959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835890900284128686926639 1253836350426193030389959)
            ·
              refine ⟨1880754525639289545584939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253836350426193030389959 1880754525639289545584939)
              ·
                refine ⟨2821131788458934318377409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880754525639289545584939 2821131788458934318377409)
                ·
                  refine ⟨2115848841344200738783057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821131788458934318377409 2115848841344200738783057)
                  ·
                    refine ⟨1586886631008150554087293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2115848841344200738783057 1586886631008150554087293)
                    ·
                      refine ⟨595082486628056457782735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1586886631008150554087293 595082486628056457782735)
                      ·
                        rfl

theorem cell23_1158919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1158919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158919 prefixEnd_1158919 := by exact prefixLift 1158919
  have htrace : WordTrace (prefixWord ++ tailWord_1158919) baseStart_1158919 baseEnd_1158919 := by
    simpa [prefixWord, tailWord_1158919, baseEnd_1158919] using wordTrace_append hprefix tailTrace_1158919
  have hstable : (prefixWord ++ tailWord_1158919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158919).length < 2 ^ (prefixWord ++ tailWord_1158919).sum := by decide
  have hdescent : baseEnd_1158919 < baseStart_1158919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158931 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 3, 6]
def baseStart_1158931 : Nat := 118140960795 + 1158931 * 2 ^ 59
def prefixEnd_1158931 : Nat := 4983230072969 + 3 ^ 40 * 1158931 * 2
def baseEnd_1158931 : Nat := 198362882798636803610893

theorem tailTrace_1158931 : CollatzResearch.WordTrace tailWord_1158931 prefixEnd_1158931 198362882798636803610893 := by
  unfold tailWord_1158931
  simp only [CollatzResearch.WordTrace]
  refine ⟨42269686164398391501924647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28179790776265594334616431 42269686164398391501924647)
  ·
    refine ⟨63404529246597587252886971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42269686164398391501924647 63404529246597587252886971)
    ·
      refine ⟨95106793869896380879330457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63404529246597587252886971 95106793869896380879330457)
      ·
        refine ⟨71330095402422285659497843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95106793869896380879330457 71330095402422285659497843)
        ·
          refine ⟨106995143103633428489246765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71330095402422285659497843 106995143103633428489246765)
          ·
            refine ⟨40123178663862535683467537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106995143103633428489246765 40123178663862535683467537)
            ·
              refine ⟨30092383997896901762600653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40123178663862535683467537 30092383997896901762600653)
              ·
                refine ⟨11284643999211338160975245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30092383997896901762600653 11284643999211338160975245)
                ·
                  refine ⟨4231741499704251810365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11284643999211338160975245 4231741499704251810365717)
                  ·
                    refine ⟨198362882798636803610893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4231741499704251810365717 198362882798636803610893)
                    ·
                      rfl

theorem cell23_1158931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_1158931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158931 prefixEnd_1158931 := by exact prefixLift 1158931
  have htrace : WordTrace (prefixWord ++ tailWord_1158931) baseStart_1158931 baseEnd_1158931 := by
    simpa [prefixWord, tailWord_1158931, baseEnd_1158931] using wordTrace_append hprefix tailTrace_1158931
  have hstable : (prefixWord ++ tailWord_1158931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158931).length < 2 ^ (prefixWord ++ tailWord_1158931).sum := by decide
  have hdescent : baseEnd_1158931 < baseStart_1158931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158935 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 1, 5]
def baseStart_1158935 : Nat := 118140960795 + 1158935 * 2 ^ 59
def prefixEnd_1158935 : Nat := 4983230072969 + 3 ^ 40 * 1158935 * 2
def baseEnd_1158935 : Nat := 198363567439509465060887

theorem tailTrace_1158935 : CollatzResearch.WordTrace tailWord_1158935 prefixEnd_1158935 198363567439509465060887 := by
  unfold tailWord_1158935
  simp only [CollatzResearch.WordTrace]
  refine ⟨42269832056383900185070259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28179888037589266790046839 42269832056383900185070259)
  ·
    refine ⟨63404748084575850277605389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42269832056383900185070259 63404748084575850277605389)
    ·
      refine ⟨23776780531715943854102021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63404748084575850277605389 23776780531715943854102021)
      ·
        refine ⟨4458146349696739472644129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23776780531715943854102021 4458146349696739472644129)
        ·
          refine ⟨3343609762272554604483097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4458146349696739472644129 3343609762272554604483097)
          ·
            refine ⟨2507707321704415953362323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343609762272554604483097 2507707321704415953362323)
            ·
              refine ⟨3761560982556623930043485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507707321704415953362323 3761560982556623930043485)
              ·
                refine ⟨1410585368458733973766307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3761560982556623930043485 1410585368458733973766307)
                ·
                  refine ⟨2115878052688100960649461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410585368458733973766307 2115878052688100960649461)
                  ·
                    refine ⟨198363567439509465060887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2115878052688100960649461 198363567439509465060887)
                    ·
                      rfl

theorem cell23_1158935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_1158935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158935 prefixEnd_1158935 := by exact prefixLift 1158935
  have htrace : WordTrace (prefixWord ++ tailWord_1158935) baseStart_1158935 baseEnd_1158935 := by
    simpa [prefixWord, tailWord_1158935, baseEnd_1158935] using wordTrace_append hprefix tailTrace_1158935
  have hstable : (prefixWord ++ tailWord_1158935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158935).length < 2 ^ (prefixWord ++ tailWord_1158935).sum := by decide
  have hdescent : baseEnd_1158935 < baseStart_1158935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158968 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1158968 : Nat := 118140960795 + 1158968 * 2 ^ 59
def prefixEnd_1158968 : Nat := 4983230072969 + 3 ^ 40 * 1158968 * 2
def baseEnd_1158968 : Nat := 595107647180126766070009

theorem tailTrace_1158968 : CollatzResearch.WordTrace tailWord_1158968 prefixEnd_1158968 595107647180126766070009 := by
  unfold tailWord_1158968
  simp only [CollatzResearch.WordTrace]
  refine ⟨21135517832632173410510779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28180690443509564547347705 21135517832632173410510779)
  ·
    refine ⟨31703276748948260115766169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21135517832632173410510779 31703276748948260115766169)
    ·
      refine ⟨23777457561711195086824627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31703276748948260115766169 23777457561711195086824627)
      ·
        refine ⟨35666186342566792630236941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23777457561711195086824627 35666186342566792630236941)
        ·
          refine ⟨13374819878462547236338853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35666186342566792630236941 13374819878462547236338853)
          ·
            refine ⟨2507778727211727606813535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13374819878462547236338853 2507778727211727606813535)
            ·
              refine ⟨3761668090817591410220303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507778727211727606813535 3761668090817591410220303)
              ·
                refine ⟨5642502136226387115330455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761668090817591410220303 5642502136226387115330455)
                ·
                  refine ⟨8463753204339580672995683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5642502136226387115330455 8463753204339580672995683)
                  ·
                    refine ⟨12695629806509371009493525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8463753204339580672995683 12695629806509371009493525)
                    ·
                      refine ⟨595107647180126766070009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12695629806509371009493525 595107647180126766070009)
                      ·
                        rfl

theorem cell23_1158968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1158968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158968 prefixEnd_1158968 := by exact prefixLift 1158968
  have htrace : WordTrace (prefixWord ++ tailWord_1158968) baseStart_1158968 baseEnd_1158968 := by
    simpa [prefixWord, tailWord_1158968, baseEnd_1158968] using wordTrace_append hprefix tailTrace_1158968
  have hstable : (prefixWord ++ tailWord_1158968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158968).length < 2 ^ (prefixWord ++ tailWord_1158968).sum := by decide
  have hdescent : baseEnd_1158968 < baseStart_1158968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158972 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_1158972 : Nat := 118140960795 + 1158972 * 2 ^ 59
def prefixEnd_1158972 : Nat := 4983230072969 + 3 ^ 40 * 1158972 * 2
def baseEnd_1158972 : Nat := 595109701102744750419991

theorem tailTrace_1158972 : CollatzResearch.WordTrace tailWord_1158972 prefixEnd_1158972 595109701102744750419991 := by
  unfold tailWord_1158972
  simp only [CollatzResearch.WordTrace]
  refine ⟨21135590778624927752083585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28180787704833237002778113 21135590778624927752083585)
  ·
    refine ⟨15851693083968695814062689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21135590778624927752083585 15851693083968695814062689)
    ·
      refine ⟨11888769812976521860547017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15851693083968695814062689 11888769812976521860547017)
      ·
        refine ⟨8916577359732391395410263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11888769812976521860547017 8916577359732391395410263)
        ·
          refine ⟨13374866039598587093115395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916577359732391395410263 13374866039598587093115395)
          ·
            refine ⟨20062299059397880639673093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13374866039598587093115395 20062299059397880639673093)
            ·
              refine ⟨3761681073637102619938705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20062299059397880639673093 3761681073637102619938705)
              ·
                refine ⟨2821260805227826964954029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761681073637102619938705 2821260805227826964954029)
                ·
                  refine ⟨1057972801960435111857761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2821260805227826964954029 1057972801960435111857761)
                  ·
                    refine ⟨793479601470326333893321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057972801960435111857761 793479601470326333893321)
                    ·
                      refine ⟨595109701102744750419991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793479601470326333893321 595109701102744750419991)
                      ·
                        rfl

theorem cell23_1158972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_1158972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1158972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1158972 prefixEnd_1158972 := by exact prefixLift 1158972
  have htrace : WordTrace (prefixWord ++ tailWord_1158972) baseStart_1158972 baseEnd_1158972 := by
    simpa [prefixWord, tailWord_1158972, baseEnd_1158972] using wordTrace_append hprefix tailTrace_1158972
  have hstable : (prefixWord ++ tailWord_1158972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158972).length < 2 ^ (prefixWord ++ tailWord_1158972).sum := by decide
  have hdescent : baseEnd_1158972 < baseStart_1158972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159049 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 1, 3, 2]
def baseStart_1159049 : Nat := 118140960795 + 1159049 * 2 ^ 59
def prefixEnd_1159049 : Nat := 4983230072969 + 3 ^ 40 * 1159049 * 2
def baseEnd_1159049 : Nat := 595149239113140949157137

theorem tailTrace_1159049 : CollatzResearch.WordTrace tailWord_1159049 prefixEnd_1159049 595149239113140949157137 := by
  unfold tailWord_1159049
  simp only [CollatzResearch.WordTrace]
  refine ⟨42273989977970897654720201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28182659985313931769813467 42273989977970897654720201)
  ·
    refine ⟨31705492483478173241040151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42273989977970897654720201 31705492483478173241040151)
    ·
      refine ⟨47558238725217259861560227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31705492483478173241040151 47558238725217259861560227)
      ·
        refine ⟨71337358087825889792340341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47558238725217259861560227 71337358087825889792340341)
        ·
          refine ⟨6687877320733677168031907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71337358087825889792340341 6687877320733677168031907)
          ·
            refine ⟨10031815981100515752047861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687877320733677168031907 10031815981100515752047861)
            ·
              refine ⟨940482748228173351754487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10031815981100515752047861 940482748228173351754487)
              ·
                refine ⟨1410724122342260027631731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940482748228173351754487 1410724122342260027631731)
                ·
                  refine ⟨2116086183513390041447597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410724122342260027631731 2116086183513390041447597)
                  ·
                    refine ⟨793532318817521265542849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116086183513390041447597 793532318817521265542849)
                    ·
                      refine ⟨595149239113140949157137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793532318817521265542849 595149239113140949157137)
                      ·
                        rfl

theorem cell23_1159049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 3, 2].length) (baseStart_1159049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159049 prefixEnd_1159049 := by exact prefixLift 1159049
  have htrace : WordTrace (prefixWord ++ tailWord_1159049) baseStart_1159049 baseEnd_1159049 := by
    simpa [prefixWord, tailWord_1159049, baseEnd_1159049] using wordTrace_append hprefix tailTrace_1159049
  have hstable : (prefixWord ++ tailWord_1159049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159049).length < 2 ^ (prefixWord ++ tailWord_1159049).sum := by decide
  have hdescent : baseEnd_1159049 < baseStart_1159049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159079 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1159079 : Nat := 118140960795 + 1159079 * 2 ^ 59
def prefixEnd_1159079 : Nat := 4983230072969 + 3 ^ 40 * 1159079 * 2
def baseEnd_1159079 : Nat := 595164643532775831781999

theorem tailTrace_1159079 : CollatzResearch.WordTrace tailWord_1159079 prefixEnd_1159079 595164643532775831781999 := by
  unfold tailWord_1159079
  simp only [CollatzResearch.WordTrace]
  refine ⟨42275084167862212778312291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28183389445241475185541527 42275084167862212778312291)
  ·
    refine ⟨63412626251793319167468437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42275084167862212778312291 63412626251793319167468437)
    ·
      refine ⟨2972466855552811835975083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63412626251793319167468437 2972466855552811835975083)
      ·
        refine ⟨4458700283329217753962625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972466855552811835975083 4458700283329217753962625)
        ·
          refine ⟨3344025212496913315471969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4458700283329217753962625 3344025212496913315471969)
          ·
            refine ⟨2508018909372684986603977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344025212496913315471969 2508018909372684986603977)
            ·
              refine ⟨1881014182029513739952983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508018909372684986603977 1881014182029513739952983)
              ·
                refine ⟨2821521273044270609929475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881014182029513739952983 2821521273044270609929475)
                ·
                  refine ⟨4232281909566405914894213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821521273044270609929475 4232281909566405914894213)
                  ·
                    refine ⟨793552858043701109042665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232281909566405914894213 793552858043701109042665)
                    ·
                      refine ⟨595164643532775831781999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793552858043701109042665 595164643532775831781999)
                      ·
                        rfl

theorem cell23_1159079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1159079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159079 prefixEnd_1159079 := by exact prefixLift 1159079
  have htrace : WordTrace (prefixWord ++ tailWord_1159079) baseStart_1159079 baseEnd_1159079 := by
    simpa [prefixWord, tailWord_1159079, baseEnd_1159079] using wordTrace_append hprefix tailTrace_1159079
  have hstable : (prefixWord ++ tailWord_1159079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159079).length < 2 ^ (prefixWord ++ tailWord_1159079).sum := by decide
  have hdescent : baseEnd_1159079 < baseStart_1159079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159100 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1159100 : Nat := 118140960795 + 1159100 * 2 ^ 59
def prefixEnd_1159100 : Nat := 4983230072969 + 3 ^ 40 * 1159100 * 2
def baseEnd_1159100 : Nat := 595175426626520249619403

theorem tailTrace_1159100 : CollatzResearch.WordTrace tailWord_1159100 prefixEnd_1159100 595175426626520249619403 := by
  unfold tailWord_1159100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137925050393066682413377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28183900067190755576551169 21137925050393066682413377)
  ·
    refine ⟨15853443787794800011810033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21137925050393066682413377 15853443787794800011810033)
    ·
      refine ⟨11890082840846100008857525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15853443787794800011810033 11890082840846100008857525)
      ·
        refine ⟨1114695266329321875830393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11890082840846100008857525 1114695266329321875830393)
        ·
          refine ⟨836021449746991406872795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114695266329321875830393 836021449746991406872795)
          ·
            refine ⟨1254032174620487110309193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836021449746991406872795 1254032174620487110309193)
            ·
              refine ⟨940524130965365332731895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254032174620487110309193 940524130965365332731895)
              ·
                refine ⟨1410786196448047999097843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940524130965365332731895 1410786196448047999097843)
                ·
                  refine ⟨2116179294672071998646765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410786196448047999097843 2116179294672071998646765)
                  ·
                    refine ⟨793567235502026999492537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116179294672071998646765 793567235502026999492537)
                    ·
                      refine ⟨595175426626520249619403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793567235502026999492537 595175426626520249619403)
                      ·
                        rfl

theorem cell23_1159100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1159100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159100 prefixEnd_1159100 := by exact prefixLift 1159100
  have htrace : WordTrace (prefixWord ++ tailWord_1159100) baseStart_1159100 baseEnd_1159100 := by
    simpa [prefixWord, tailWord_1159100, baseEnd_1159100] using wordTrace_append hprefix tailTrace_1159100
  have hstable : (prefixWord ++ tailWord_1159100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159100).length < 2 ^ (prefixWord ++ tailWord_1159100).sum := by decide
  have hdescent : baseEnd_1159100 < baseStart_1159100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159102 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1159102 : Nat := 118140960795 + 1159102 * 2 ^ 59
def prefixEnd_1159102 : Nat := 4983230072969 + 3 ^ 40 * 1159102 * 2
def baseEnd_1159102 : Nat := 66130717065314360199377

theorem tailTrace_1159102 : CollatzResearch.WordTrace tailWord_1159102 prefixEnd_1159102 66130717065314360199377 := by
  unfold tailWord_1159102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284490380847360963299945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28183948697852591804266373 5284490380847360963299945)
  ·
    refine ⟨3963367785635520722474959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5284490380847360963299945 3963367785635520722474959)
    ·
      refine ⟨5945051678453281083712439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963367785635520722474959 5945051678453281083712439)
      ·
        refine ⟨8917577517679921625568659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5945051678453281083712439 8917577517679921625568659)
        ·
          refine ⟨13376366276519882438352989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8917577517679921625568659 13376366276519882438352989)
          ·
            refine ⟨5016137353694955914382371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13376366276519882438352989 5016137353694955914382371)
            ·
              refine ⟨7524206030542433871573557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5016137353694955914382371 7524206030542433871573557)
              ·
                refine ⟨705394315363353175460021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7524206030542433871573557 705394315363353175460021)
                ·
                  refine ⟨66130717065314360199377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 705394315363353175460021 66130717065314360199377)
                  ·
                    rfl

theorem cell23_1159102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1159102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159102 prefixEnd_1159102 := by exact prefixLift 1159102
  have htrace : WordTrace (prefixWord ++ tailWord_1159102) baseStart_1159102 baseEnd_1159102 := by
    simpa [prefixWord, tailWord_1159102, baseEnd_1159102] using wordTrace_append hprefix tailTrace_1159102
  have hstable : (prefixWord ++ tailWord_1159102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159102).length < 2 ^ (prefixWord ++ tailWord_1159102).sum := by decide
  have hdescent : baseEnd_1159102 < baseStart_1159102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159135 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1159135 : Nat := 118140960795 + 1159135 * 2 ^ 59
def prefixEnd_1159135 : Nat := 4983230072969 + 3 ^ 40 * 1159135 * 2
def baseEnd_1159135 : Nat := 595193398449427612681741

theorem tailTrace_1159135 : CollatzResearch.WordTrace tailWord_1159135 prefixEnd_1159135 595193398449427612681741 := by
  unfold tailWord_1159135
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277126655659334342350859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28184751103772889561567239 42277126655659334342350859)
  ·
    refine ⟨63415689983489001513526289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42277126655659334342350859 63415689983489001513526289)
    ·
      refine ⟨47561767487616751135144717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63415689983489001513526289 47561767487616751135144717)
      ·
        refine ⟨17835662807856281675679269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47561767487616751135144717 17835662807856281675679269)
        ·
          refine ⟨3344186776473052814189863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17835662807856281675679269 3344186776473052814189863)
          ·
            refine ⟨5016280164709579221284795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344186776473052814189863 5016280164709579221284795)
            ·
              refine ⟨7524420247064368831927193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5016280164709579221284795 7524420247064368831927193)
              ·
                refine ⟨5643315185298276623945395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7524420247064368831927193 5643315185298276623945395)
                ·
                  refine ⟨8464972777947414935918093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643315185298276623945395 8464972777947414935918093)
                  ·
                    refine ⟨3174364791730280600969285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8464972777947414935918093 3174364791730280600969285)
                    ·
                      refine ⟨595193398449427612681741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3174364791730280600969285 595193398449427612681741)
                      ·
                        rfl

theorem cell23_1159135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1159135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159135 prefixEnd_1159135 := by exact prefixLift 1159135
  have htrace : WordTrace (prefixWord ++ tailWord_1159135) baseStart_1159135 baseEnd_1159135 := by
    simpa [prefixWord, tailWord_1159135, baseEnd_1159135] using wordTrace_append hprefix tailTrace_1159135
  have hstable : (prefixWord ++ tailWord_1159135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159135).length < 2 ^ (prefixWord ++ tailWord_1159135).sum := by decide
  have hdescent : baseEnd_1159135 < baseStart_1159135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159155 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3]
def baseStart_1159155 : Nat := 118140960795 + 1159155 * 2 ^ 59
def prefixEnd_1159155 : Nat := 4983230072969 + 3 ^ 40 * 1159155 * 2
def baseEnd_1159155 : Nat := 595203668062517534431649

theorem tailTrace_1159155 : CollatzResearch.WordTrace tailWord_1159155 prefixEnd_1159155 595203668062517534431649 := by
  unfold tailWord_1159155
  simp only [CollatzResearch.WordTrace]
  refine ⟨42277856115586877758078919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28185237410391251838719279 42277856115586877758078919)
  ·
    refine ⟨63416784173380316637118379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42277856115586877758078919 63416784173380316637118379)
    ·
      refine ⟨95125176260070474955677569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63416784173380316637118379 95125176260070474955677569)
      ·
        refine ⟨71343882195052856216758177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95125176260070474955677569 71343882195052856216758177)
        ·
          refine ⟨53507911646289642162568633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71343882195052856216758177 53507911646289642162568633)
          ·
            refine ⟨40130933734717231621926475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53507911646289642162568633 40130933734717231621926475)
            ·
              refine ⟨60196400602075847432889713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40130933734717231621926475 60196400602075847432889713)
              ·
                refine ⟨45147300451556885574667285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60196400602075847432889713 45147300451556885574667285)
                ·
                  refine ⟨2116279708666729011312529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45147300451556885574667285 2116279708666729011312529)
                  ·
                    refine ⟨1587209781500046758484397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2116279708666729011312529 1587209781500046758484397)
                    ·
                      refine ⟨595203668062517534431649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587209781500046758484397 595203668062517534431649)
                      ·
                        rfl

theorem cell23_1159155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_1159155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159155 prefixEnd_1159155 := by exact prefixLift 1159155
  have htrace : WordTrace (prefixWord ++ tailWord_1159155) baseStart_1159155 baseEnd_1159155 := by
    simpa [prefixWord, tailWord_1159155, baseEnd_1159155] using wordTrace_append hprefix tailTrace_1159155
  have hstable : (prefixWord ++ tailWord_1159155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159155).length < 2 ^ (prefixWord ++ tailWord_1159155).sum := by decide
  have hdescent : baseEnd_1159155 < baseStart_1159155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159175 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 8]
def baseStart_1159175 : Nat := 118140960795 + 1159175 * 2 ^ 59
def prefixEnd_1159175 : Nat := 4983230072969 + 3 ^ 40 * 1159175 * 2
def baseEnd_1159175 : Nat := 66134881963956384020173

theorem tailTrace_1159175 : CollatzResearch.WordTrace tailWord_1159175 prefixEnd_1159175 66134881963956384020173 := by
  unfold tailWord_1159175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42278585575514421173806979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28185723717009614115871319 42278585575514421173806979)
  ·
    refine ⟨63417878363271631760710469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42278585575514421173806979 63417878363271631760710469)
    ·
      refine ⟨11890852193113430955133213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63417878363271631760710469 11890852193113430955133213)
      ·
        refine ⟨4459069572417536608174955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11890852193113430955133213 4459069572417536608174955)
        ·
          refine ⟨6688604358626304912262433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459069572417536608174955 6688604358626304912262433)
          ·
            refine ⟨5016453268969728684196825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688604358626304912262433 5016453268969728684196825)
            ·
              refine ⟨3762339951727296513147619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016453268969728684196825 3762339951727296513147619)
              ·
                refine ⟨5643509927590944769721429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762339951727296513147619 5643509927590944769721429)
                ·
                  refine ⟨66134881963956384020173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5643509927590944769721429 66134881963956384020173)
                  ·
                    rfl

theorem cell23_1159175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 8].length) (baseStart_1159175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159175 prefixEnd_1159175 := by exact prefixLift 1159175
  have htrace : WordTrace (prefixWord ++ tailWord_1159175) baseStart_1159175 baseEnd_1159175 := by
    simpa [prefixWord, tailWord_1159175, baseEnd_1159175] using wordTrace_append hprefix tailTrace_1159175
  have hstable : (prefixWord ++ tailWord_1159175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159175).length < 2 ^ (prefixWord ++ tailWord_1159175).sum := by decide
  have hdescent : baseEnd_1159175 < baseStart_1159175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159229 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1159229 : Nat := 118140960795 + 1159229 * 2 ^ 59
def prefixEnd_1159229 : Nat := 4983230072969 + 3 ^ 40 * 1159229 * 2
def baseEnd_1159229 : Nat := 595241665630950244906309

theorem tailTrace_1159229 : CollatzResearch.WordTrace tailWord_1159229 prefixEnd_1159229 595241665630950244906309 := by
  unfold tailWord_1159229
  simp only [CollatzResearch.WordTrace]
  refine ⟨42280555117318788396272741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28187036744879192264181827 42280555117318788396272741)
  ·
    refine ⟨7927604084497272824301139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42280555117318788396272741 7927604084497272824301139)
    ·
      refine ⟨11891406126745909236451709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7927604084497272824301139 11891406126745909236451709)
      ·
        refine ⟨4459277297529715963669391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11891406126745909236451709 4459277297529715963669391)
        ·
          refine ⟨6688915946294573945504087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459277297529715963669391 6688915946294573945504087)
          ·
            refine ⟨10033373919441860918256131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6688915946294573945504087 10033373919441860918256131)
            ·
              refine ⟨15050060879162791377384197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10033373919441860918256131 15050060879162791377384197)
              ·
                refine ⟨2821886414843023383259537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15050060879162791377384197 2821886414843023383259537)
                ·
                  refine ⟨2116414811132267537444653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2821886414843023383259537 2116414811132267537444653)
                  ·
                    refine ⟨793655554174600326541745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116414811132267537444653 793655554174600326541745)
                    ·
                      refine ⟨595241665630950244906309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793655554174600326541745 595241665630950244906309)
                      ·
                        rfl

theorem cell23_1159229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1159229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159229 prefixEnd_1159229 := by exact prefixLift 1159229
  have htrace : WordTrace (prefixWord ++ tailWord_1159229) baseStart_1159229 baseEnd_1159229 := by
    simpa [prefixWord, tailWord_1159229, baseEnd_1159229] using wordTrace_append hprefix tailTrace_1159229
  have hstable : (prefixWord ++ tailWord_1159229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159229).length < 2 ^ (prefixWord ++ tailWord_1159229).sum := by decide
  have hdescent : baseEnd_1159229 < baseStart_1159229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159230 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1159230 : Nat := 118140960795 + 1159230 * 2 ^ 59
def prefixEnd_1159230 : Nat := 4983230072969 + 3 ^ 40 * 1159230 * 2
def baseEnd_1159230 : Nat := 198414059703868246997935

theorem tailTrace_1159230 : CollatzResearch.WordTrace tailWord_1159230 prefixEnd_1159230 198414059703868246997935 := by
  unfold tailWord_1159230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285073948789395695882393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28187061060210110378039429 5285073948789395695882393)
  ·
    refine ⟨3963805461592046771911795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5285073948789395695882393 3963805461592046771911795)
    ·
      refine ⟨5945708192388070157867693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963805461592046771911795 5945708192388070157867693)
      ·
        refine ⟨2229640572145526309200385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5945708192388070157867693 2229640572145526309200385)
        ·
          refine ⟨1672230429109144731900289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229640572145526309200385 1672230429109144731900289)
          ·
            refine ⟨1254172821831858548925217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672230429109144731900289 1254172821831858548925217)
            ·
              refine ⟨940629616373893911693913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254172821831858548925217 940629616373893911693913)
              ·
                refine ⟨705472212280420433770435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940629616373893911693913 705472212280420433770435)
                ·
                  refine ⟨1058208318420630650655653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705472212280420433770435 1058208318420630650655653)
                  ·
                    refine ⟨198414059703868246997935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058208318420630650655653 198414059703868246997935)
                    ·
                      rfl

theorem cell23_1159230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1159230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159230 prefixEnd_1159230 := by exact prefixLift 1159230
  have htrace : WordTrace (prefixWord ++ tailWord_1159230) baseStart_1159230 baseEnd_1159230 := by
    simpa [prefixWord, tailWord_1159230, baseEnd_1159230] using wordTrace_append hprefix tailTrace_1159230
  have hstable : (prefixWord ++ tailWord_1159230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159230).length < 2 ^ (prefixWord ++ tailWord_1159230).sum := by decide
  have hdescent : baseEnd_1159230 < baseStart_1159230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159242 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_1159242 : Nat := 118140960795 + 1159242 * 2 ^ 59
def prefixEnd_1159242 : Nat := 4983230072969 + 3 ^ 40 * 1159242 * 2
def baseEnd_1159242 : Nat := 595248340879458694043749

theorem tailTrace_1159242 : CollatzResearch.WordTrace tailWord_1159242 prefixEnd_1159242 595248340879458694043749 := by
  unfold tailWord_1159242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570257316567922904123995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28187352844181127744330653 10570257316567922904123995)
  ·
    refine ⟨15855385974851884356185993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10570257316567922904123995 15855385974851884356185993)
    ·
      refine ⟨11891539481138913267139495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15855385974851884356185993 11891539481138913267139495)
      ·
        refine ⟨17837309221708369900709243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11891539481138913267139495 17837309221708369900709243)
        ·
          refine ⟨26755963832562554851063865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17837309221708369900709243 26755963832562554851063865)
          ·
            refine ⟨20066972874421916138297899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26755963832562554851063865 20066972874421916138297899)
            ·
              refine ⟨30100459311632874207446849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20066972874421916138297899 30100459311632874207446849)
              ·
                refine ⟨22575344483724655655585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30100459311632874207446849 22575344483724655655585137)
                ·
                  refine ⟨16931508362793491741688853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22575344483724655655585137 16931508362793491741688853)
                  ·
                    refine ⟨793664454505944925391665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16931508362793491741688853 793664454505944925391665)
                    ·
                      refine ⟨595248340879458694043749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793664454505944925391665 595248340879458694043749)
                      ·
                        rfl

theorem cell23_1159242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_1159242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159242 prefixEnd_1159242 := by exact prefixLift 1159242
  have htrace : WordTrace (prefixWord ++ tailWord_1159242) baseStart_1159242 baseEnd_1159242 := by
    simpa [prefixWord, tailWord_1159242, baseEnd_1159242] using wordTrace_append hprefix tailTrace_1159242
  have hstable : (prefixWord ++ tailWord_1159242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159242).length < 2 ^ (prefixWord ++ tailWord_1159242).sum := by decide
  have hdescent : baseEnd_1159242 < baseStart_1159242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159252 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1159252 : Nat := 118140960795 + 1159252 * 2 ^ 59
def prefixEnd_1159252 : Nat := 4983230072969 + 3 ^ 40 * 1159252 * 2
def baseEnd_1159252 : Nat := 198417825228667884972901

theorem tailTrace_1159252 : CollatzResearch.WordTrace tailWord_1159252 prefixEnd_1159252 198417825228667884972901 := by
  unfold tailWord_1159252
  simp only [CollatzResearch.WordTrace]
  refine ⟨21140696998117731662180005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28187595997490308882906673 21140696998117731662180005)
  ·
    refine ⟨3963880687147074686658751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21140696998117731662180005 3963880687147074686658751)
    ·
      refine ⟨5945821030720612029988127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963880687147074686658751 5945821030720612029988127)
      ·
        refine ⟨8918731546080918044982191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5945821030720612029988127 8918731546080918044982191)
        ·
          refine ⟨13378097319121377067473287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8918731546080918044982191 13378097319121377067473287)
          ·
            refine ⟨20067145978682065601209931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13378097319121377067473287 20067145978682065601209931)
            ·
              refine ⟨30100718968023098401814897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20067145978682065601209931 30100718968023098401814897)
              ·
                refine ⟨22575539226017323801361173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30100718968023098401814897 22575539226017323801361173)
                ·
                  refine ⟨1058228401219562053188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22575539226017323801361173 1058228401219562053188805)
                  ·
                    refine ⟨198417825228667884972901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058228401219562053188805 198417825228667884972901)
                    ·
                      rfl

theorem cell23_1159252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1159252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159252 prefixEnd_1159252 := by exact prefixLift 1159252
  have htrace : WordTrace (prefixWord ++ tailWord_1159252) baseStart_1159252 baseEnd_1159252 := by
    simpa [prefixWord, tailWord_1159252, baseEnd_1159252] using wordTrace_append hprefix tailTrace_1159252
  have hstable : (prefixWord ++ tailWord_1159252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159252).length < 2 ^ (prefixWord ++ tailWord_1159252).sum := by decide
  have hdescent : baseEnd_1159252 < baseStart_1159252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159255 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1159255 : Nat := 118140960795 + 1159255 * 2 ^ 59
def prefixEnd_1159255 : Nat := 4983230072969 + 3 ^ 40 * 1159255 * 2
def baseEnd_1159255 : Nat := 595255016127967143181189

theorem tailTrace_1159255 : CollatzResearch.WordTrace tailWord_1159255 prefixEnd_1159255 595255016127967143181189 := by
  unfold tailWord_1159255
  simp only [CollatzResearch.WordTrace]
  refine ⟨42281503415224594836719219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28187668943483063224479479 42281503415224594836719219)
  ·
    refine ⟨63422255122836892255078829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42281503415224594836719219 63422255122836892255078829)
    ·
      refine ⟨23783345671063834595654561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63422255122836892255078829 23783345671063834595654561)
      ·
        refine ⟨17837509253297875946740921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23783345671063834595654561 17837509253297875946740921)
        ·
          refine ⟨13378131939973406960055691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17837509253297875946740921 13378131939973406960055691)
          ·
            refine ⟨20067197909960110440083537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13378131939973406960055691 20067197909960110440083537)
            ·
              refine ⟨15050398432470082830062653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20067197909960110440083537 15050398432470082830062653)
              ·
                refine ⟨5643899412176281061273495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15050398432470082830062653 5643899412176281061273495)
                ·
                  refine ⟨8465849118264421591910243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643899412176281061273495 8465849118264421591910243)
                  ·
                    refine ⟨12698773677396632387865365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8465849118264421591910243 12698773677396632387865365)
                    ·
                      refine ⟨595255016127967143181189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12698773677396632387865365 595255016127967143181189)
                      ·
                        rfl

theorem cell23_1159255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1159255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159255 prefixEnd_1159255 := by exact prefixLift 1159255
  have htrace : WordTrace (prefixWord ++ tailWord_1159255) baseStart_1159255 baseEnd_1159255 := by
    simpa [prefixWord, tailWord_1159255, baseEnd_1159255] using wordTrace_append hprefix tailTrace_1159255
  have hstable : (prefixWord ++ tailWord_1159255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159255).length < 2 ^ (prefixWord ++ tailWord_1159255).sum := by decide
  have hdescent : baseEnd_1159255 < baseStart_1159255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159276 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_1159276 : Nat := 118140960795 + 1159276 * 2 ^ 59
def prefixEnd_1159276 : Nat := 4983230072969 + 3 ^ 40 * 1159276 * 2
def baseEnd_1159276 : Nat := 595265799221711561018593

theorem tailTrace_1159276 : CollatzResearch.WordTrace tailWord_1159276 prefixEnd_1159276 595265799221711561018593 := by
  unfold tailWord_1159276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141134674074257711616841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28188179565432343615489121 21141134674074257711616841)
  ·
    refine ⟨15855851005555693283712631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21141134674074257711616841 15855851005555693283712631)
    ·
      refine ⟨23783776508333539925568947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15855851005555693283712631 23783776508333539925568947)
      ·
        refine ⟨35675664762500309888353421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23783776508333539925568947 35675664762500309888353421)
        ·
          refine ⟨13378374285937616208132533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35675664762500309888353421 13378374285937616208132533)
          ·
            refine ⟨1254222589306651519512425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13378374285937616208132533 1254222589306651519512425)
            ·
              refine ⟨940666941979988639634319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254222589306651519512425 940666941979988639634319)
              ·
                refine ⟨1411000412969982959451479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940666941979988639634319 1411000412969982959451479)
                ·
                  refine ⟨2116500619454974439177219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411000412969982959451479 2116500619454974439177219)
                  ·
                    refine ⟨3174750929182461658765829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116500619454974439177219 3174750929182461658765829)
                    ·
                      refine ⟨595265799221711561018593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3174750929182461658765829 595265799221711561018593)
                      ·
                        rfl

theorem cell23_1159276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_1159276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159276 prefixEnd_1159276 := by exact prefixLift 1159276
  have htrace : WordTrace (prefixWord ++ tailWord_1159276) baseStart_1159276 baseEnd_1159276 := by
    simpa [prefixWord, tailWord_1159276, baseEnd_1159276] using wordTrace_append hprefix tailTrace_1159276
  have hstable : (prefixWord ++ tailWord_1159276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159276).length < 2 ^ (prefixWord ++ tailWord_1159276).sum := by decide
  have hdescent : baseEnd_1159276 < baseStart_1159276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159279 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_1159279 : Nat := 118140960795 + 1159279 * 2 ^ 59
def prefixEnd_1159279 : Nat := 4983230072969 + 3 ^ 40 * 1159279 * 2
def baseEnd_1159279 : Nat := 595267339663675049281079

theorem tailTrace_1159279 : CollatzResearch.WordTrace tailWord_1159279 prefixEnd_1159279 595267339663675049281079 := by
  unfold tailWord_1159279
  simp only [CollatzResearch.WordTrace]
  refine ⟨42282378767137646935592891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28188252511425097957061927 42282378767137646935592891)
  ·
    refine ⟨63423568150706470403389337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42282378767137646935592891 63423568150706470403389337)
    ·
      refine ⟨47567676113029852802542003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63423568150706470403389337 47567676113029852802542003)
      ·
        refine ⟨71351514169544779203813005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47567676113029852802542003 71351514169544779203813005)
        ·
          refine ⟨26756817813579292201429877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71351514169544779203813005 26756817813579292201429877)
          ·
            refine ⟨2508451670023058643884051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26756817813579292201429877 2508451670023058643884051)
            ·
              refine ⟨3762677505034587965826077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508451670023058643884051 3762677505034587965826077)
              ·
                refine ⟨1411004064387970487184779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3762677505034587965826077 1411004064387970487184779)
                ·
                  refine ⟨2116506096581955730777169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411004064387970487184779 2116506096581955730777169)
                  ·
                    refine ⟨1587379572436466798082877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2116506096581955730777169 1587379572436466798082877)
                    ·
                      refine ⟨595267339663675049281079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587379572436466798082877 595267339663675049281079)
                      ·
                        rfl

theorem cell23_1159279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_1159279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159279 prefixEnd_1159279 := by exact prefixLift 1159279
  have htrace : WordTrace (prefixWord ++ tailWord_1159279) baseStart_1159279 baseEnd_1159279 := by
    simpa [prefixWord, tailWord_1159279, baseEnd_1159279] using wordTrace_append hprefix tailTrace_1159279
  have hstable : (prefixWord ++ tailWord_1159279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159279).length < 2 ^ (prefixWord ++ tailWord_1159279).sum := by decide
  have hdescent : baseEnd_1159279 < baseStart_1159279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159286 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1159286 : Nat := 118140960795 + 1159286 * 2 ^ 59
def prefixEnd_1159286 : Nat := 4983230072969 + 3 ^ 40 * 1159286 * 2
def baseEnd_1159286 : Nat := 198423644676085507297849

theorem tailTrace_1159286 : CollatzResearch.WordTrace tailWord_1159286 prefixEnd_1159286 198423644676085507297849 := by
  unfold tailWord_1159286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642664629882017945693607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28188422718741524754065141 2642664629882017945693607)
  ·
    refine ⟨3963996944823026918540411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642664629882017945693607 3963996944823026918540411)
    ·
      refine ⟨5945995417234540377810617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3963996944823026918540411 5945995417234540377810617)
      ·
        refine ⟨4459496562925905283357963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5945995417234540377810617 4459496562925905283357963)
        ·
          refine ⟨6689244844388857925036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459496562925905283357963 6689244844388857925036945)
          ·
            refine ⟨5016933633291643443777709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689244844388857925036945 5016933633291643443777709)
            ·
              refine ⟨1881350112484366291416641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016933633291643443777709 1881350112484366291416641)
              ·
                refine ⟨1411012584363274718562481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881350112484366291416641 1411012584363274718562481)
                ·
                  refine ⟨1058259438272456038921861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411012584363274718562481 1058259438272456038921861)
                  ·
                    refine ⟨198423644676085507297849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1058259438272456038921861 198423644676085507297849)
                    ·
                      rfl

theorem cell23_1159286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1159286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159286 prefixEnd_1159286 := by exact prefixLift 1159286
  have htrace : WordTrace (prefixWord ++ tailWord_1159286) baseStart_1159286 baseEnd_1159286 := by
    simpa [prefixWord, tailWord_1159286, baseEnd_1159286] using wordTrace_append hprefix tailTrace_1159286
  have hstable : (prefixWord ++ tailWord_1159286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159286).length < 2 ^ (prefixWord ++ tailWord_1159286).sum := by decide
  have hdescent : baseEnd_1159286 < baseStart_1159286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159293 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_1159293 : Nat := 118140960795 + 1159293 * 2 ^ 59
def prefixEnd_1159293 : Nat := 4983230072969 + 3 ^ 40 * 1159293 * 2
def baseEnd_1159293 : Nat := 595274528392837994506015

theorem tailTrace_1159293 : CollatzResearch.WordTrace tailWord_1159293 prefixEnd_1159293 595274528392837994506015 := by
  unfold tailWord_1159293
  simp only [CollatzResearch.WordTrace]
  refine ⟨42282889389086927326602533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28188592926057951551068355 42282889389086927326602533)
  ·
    refine ⟨7928041760453798873737975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42282889389086927326602533 7928041760453798873737975)
    ·
      refine ⟨11892062640680698310606963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7928041760453798873737975 11892062640680698310606963)
      ·
        refine ⟨17838093961021047465910445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11892062640680698310606963 17838093961021047465910445)
        ·
          refine ⟨6689285235382892799716417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17838093961021047465910445 6689285235382892799716417)
          ·
            refine ⟨5016963926537169599787313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689285235382892799716417 5016963926537169599787313)
            ·
              refine ⟨3762722944902877199840485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016963926537169599787313 3762722944902877199840485)
              ·
                refine ⟨705510552169289474970091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3762722944902877199840485 705510552169289474970091)
                ·
                  refine ⟨1058265828253934212455137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705510552169289474970091 1058265828253934212455137)
                  ·
                    refine ⟨793699371190450659341353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058265828253934212455137 793699371190450659341353)
                    ·
                      refine ⟨595274528392837994506015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793699371190450659341353 595274528392837994506015)
                      ·
                        rfl

theorem cell23_1159293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_1159293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159293 prefixEnd_1159293 := by exact prefixLift 1159293
  have htrace : WordTrace (prefixWord ++ tailWord_1159293) baseStart_1159293 baseEnd_1159293 := by
    simpa [prefixWord, tailWord_1159293, baseEnd_1159293] using wordTrace_append hprefix tailTrace_1159293
  have hstable : (prefixWord ++ tailWord_1159293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159293).length < 2 ^ (prefixWord ++ tailWord_1159293).sum := by decide
  have hdescent : baseEnd_1159293 < baseStart_1159293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159352 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1159352 : Nat := 118140960795 + 1159352 * 2 ^ 59
def prefixEnd_1159352 : Nat := 4983230072969 + 3 ^ 40 * 1159352 * 2
def baseEnd_1159352 : Nat := 595304823751453263668243

theorem tailTrace_1159352 : CollatzResearch.WordTrace tailWord_1159352 prefixEnd_1159352 595304823751453263668243 := by
  unfold tailWord_1159352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142520647936590201500155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28190027530582120268666873 21142520647936590201500155)
  ·
    refine ⟨31713780971904885302250233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21142520647936590201500155 31713780971904885302250233)
    ·
      refine ⟨23785335728928663976687675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31713780971904885302250233 23785335728928663976687675)
      ·
        refine ⟨35678003593392995965031513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23785335728928663976687675 35678003593392995965031513)
        ·
          refine ⟨26758502695044746973773635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35678003593392995965031513 26758502695044746973773635)
          ·
            refine ⟨40137754042567120460660453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26758502695044746973773635 40137754042567120460660453)
            ·
              refine ⟨7525828882981335086373835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40137754042567120460660453 7525828882981335086373835)
              ·
                refine ⟨11288743324472002629560753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525828882981335086373835 11288743324472002629560753)
                ·
                  refine ⟨8466557493354001972170565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11288743324472002629560753 8466557493354001972170565)
                  ·
                    refine ⟨1587479530003875369781981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8466557493354001972170565 1587479530003875369781981)
                    ·
                      refine ⟨595304823751453263668243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587479530003875369781981 595304823751453263668243)
                      ·
                        rfl

theorem cell23_1159352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1159352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159352 prefixEnd_1159352 := by exact prefixLift 1159352
  have htrace : WordTrace (prefixWord ++ tailWord_1159352) baseStart_1159352 baseEnd_1159352 := by
    simpa [prefixWord, tailWord_1159352, baseEnd_1159352] using wordTrace_append hprefix tailTrace_1159352
  have hstable : (prefixWord ++ tailWord_1159352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159352).length < 2 ^ (prefixWord ++ tailWord_1159352).sum := by decide
  have hdescent : baseEnd_1159352 < baseStart_1159352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159409 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_1159409 : Nat := 118140960795 + 1159409 * 2 ^ 59
def prefixEnd_1159409 : Nat := 4983230072969 + 3 ^ 40 * 1159409 * 2
def baseEnd_1159409 : Nat := 595334092148759540655481

theorem tailTrace_1159409 : CollatzResearch.WordTrace tailWord_1159409 prefixEnd_1159409 595334092148759540655481 := by
  unfold tailWord_1159409
  simp only [CollatzResearch.WordTrace]
  refine ⟨42287120256666679137825281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28191413504444452758550187 42287120256666679137825281)
  ·
    refine ⟨31715340192500009353368961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42287120256666679137825281 31715340192500009353368961)
    ·
      refine ⟨23786505144375007015026721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31715340192500009353368961 23786505144375007015026721)
      ·
        refine ⟨17839878858281255261270041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23786505144375007015026721 17839878858281255261270041)
        ·
          refine ⟨13379909143710941445952531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17839878858281255261270041 13379909143710941445952531)
          ·
            refine ⟨20069863715566412168928797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379909143710941445952531 20069863715566412168928797)
            ·
              refine ⟨7526198893337404563348299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20069863715566412168928797 7526198893337404563348299)
              ·
                refine ⟨11289298340006106845022449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526198893337404563348299 11289298340006106845022449)
                ·
                  refine ⟨8466973755004580133766837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11289298340006106845022449 8466973755004580133766837)
                  ·
                    refine ⟨793778789531679387540641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8466973755004580133766837 793778789531679387540641)
                    ·
                      refine ⟨595334092148759540655481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793778789531679387540641 595334092148759540655481)
                      ·
                        rfl

theorem cell23_1159409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_1159409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159409 prefixEnd_1159409 := by exact prefixLift 1159409
  have htrace : WordTrace (prefixWord ++ tailWord_1159409) baseStart_1159409 baseEnd_1159409 := by
    simpa [prefixWord, tailWord_1159409, baseEnd_1159409] using wordTrace_append hprefix tailTrace_1159409
  have hstable : (prefixWord ++ tailWord_1159409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159409).length < 2 ^ (prefixWord ++ tailWord_1159409).sum := by decide
  have hdescent : baseEnd_1159409 < baseStart_1159409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159456 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1159456 : Nat := 118140960795 + 1159456 * 2 ^ 59
def prefixEnd_1159456 : Nat := 4983230072969 + 3 ^ 40 * 1159456 * 2
def baseEnd_1159456 : Nat := 595358225739520856767765

theorem tailTrace_1159456 : CollatzResearch.WordTrace tailWord_1159456 prefixEnd_1159456 595358225739520856767765 := by
  unfold tailWord_1159456
  simp only [CollatzResearch.WordTrace]
  refine ⟨21144417243748203082393111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28192556324997604109857481 21144417243748203082393111)
  ·
    refine ⟨31716625865622304623589667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21144417243748203082393111 31716625865622304623589667)
    ·
      refine ⟨47574938798433456935384501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31716625865622304623589667 47574938798433456935384501)
      ·
        refine ⟨4460150512353136587692297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47574938798433456935384501 4460150512353136587692297)
        ·
          refine ⟨3345112884264852440769223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4460150512353136587692297 3345112884264852440769223)
          ·
            refine ⟨5017669326397278661153835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345112884264852440769223 5017669326397278661153835)
            ·
              refine ⟨7526503989595917991730753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017669326397278661153835 7526503989595917991730753)
              ·
                refine ⟨5644877992196938493798065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526503989595917991730753 5644877992196938493798065)
                ·
                  refine ⟨4233658494147703870348549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644877992196938493798065 4233658494147703870348549)
                  ·
                    refine ⟨793810967652694475690353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4233658494147703870348549 793810967652694475690353)
                    ·
                      refine ⟨595358225739520856767765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793810967652694475690353 595358225739520856767765)
                      ·
                        rfl

theorem cell23_1159456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1159456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159456 prefixEnd_1159456 := by exact prefixLift 1159456
  have htrace : WordTrace (prefixWord ++ tailWord_1159456) baseStart_1159456 baseEnd_1159456 := by
    simpa [prefixWord, tailWord_1159456, baseEnd_1159456] using wordTrace_append hprefix tailTrace_1159456
  have hstable : (prefixWord ++ tailWord_1159456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159456).length < 2 ^ (prefixWord ++ tailWord_1159456).sum := by decide
  have hdescent : baseEnd_1159456 < baseStart_1159456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159459 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1159459 : Nat := 118140960795 + 1159459 * 2 ^ 59
def prefixEnd_1159459 : Nat := 4983230072969 + 3 ^ 40 * 1159459 * 2
def baseEnd_1159459 : Nat := 595359766181484345030251

theorem tailTrace_1159459 : CollatzResearch.WordTrace tailWord_1159459 prefixEnd_1159459 595359766181484345030251 := by
  unfold tailWord_1159459
  simp only [CollatzResearch.WordTrace]
  refine ⟨42288943906485537677145431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28192629270990358451430287 42288943906485537677145431)
  ·
    refine ⟨63433415859728306515718147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42288943906485537677145431 63433415859728306515718147)
    ·
      refine ⟨95150123789592459773577221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63433415859728306515718147 95150123789592459773577221)
      ·
        refine ⟨17840648210548586207545729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95150123789592459773577221 17840648210548586207545729)
        ·
          refine ⟨13380486157911439655659297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17840648210548586207545729 13380486157911439655659297)
          ·
            refine ⟨10035364618433579741744473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13380486157911439655659297 10035364618433579741744473)
            ·
              refine ⟨7526523463825184806308355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035364618433579741744473 7526523463825184806308355)
              ·
                refine ⟨11289785195737777209462533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526523463825184806308355 11289785195737777209462533)
                ·
                  refine ⟨2116834724200833226774225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11289785195737777209462533 2116834724200833226774225)
                  ·
                    refine ⟨1587626043150624920080669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2116834724200833226774225 1587626043150624920080669)
                    ·
                      refine ⟨595359766181484345030251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587626043150624920080669 595359766181484345030251)
                      ·
                        rfl

theorem cell23_1159459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1159459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159459 prefixEnd_1159459 := by exact prefixLift 1159459
  have htrace : WordTrace (prefixWord ++ tailWord_1159459) baseStart_1159459 baseEnd_1159459 := by
    simpa [prefixWord, tailWord_1159459, baseEnd_1159459] using wordTrace_append hprefix tailTrace_1159459
  have hstable : (prefixWord ++ tailWord_1159459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159459).length < 2 ^ (prefixWord ++ tailWord_1159459).sum := by decide
  have hdescent : baseEnd_1159459 < baseStart_1159459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159476 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1159476 : Nat := 118140960795 + 1159476 * 2 ^ 59
def prefixEnd_1159476 : Nat := 4983230072969 + 3 ^ 40 * 1159476 * 2
def baseEnd_1159476 : Nat := 595368495352610778517673

theorem tailTrace_1159476 : CollatzResearch.WordTrace tailWord_1159476 prefixEnd_1159476 595368495352610778517673 := by
  unfold tailWord_1159476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21144781973711974790257141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28193042631615966387009521 21144781973711974790257141)
  ·
    refine ⟨1982323310035497636586607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21144781973711974790257141 1982323310035497636586607)
    ·
      refine ⟨2973484965053246454879911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982323310035497636586607 2973484965053246454879911)
      ·
        refine ⟨4460227447579869682319867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973484965053246454879911 4460227447579869682319867)
        ·
          refine ⟨6690341171369804523479801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460227447579869682319867 6690341171369804523479801)
          ·
            refine ⟨5017755878527353392609851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6690341171369804523479801 5017755878527353392609851)
            ·
              refine ⟨7526633817791030088914777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017755878527353392609851 7526633817791030088914777)
              ·
                refine ⟨5644975363343272566686083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526633817791030088914777 5644975363343272566686083)
                ·
                  refine ⟨8467463045014908850029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5644975363343272566686083 8467463045014908850029125)
                  ·
                    refine ⟨1587649320940295409380461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8467463045014908850029125 1587649320940295409380461)
                    ·
                      refine ⟨595368495352610778517673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587649320940295409380461 595368495352610778517673)
                      ·
                        rfl

theorem cell23_1159476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1159476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159476 prefixEnd_1159476 := by exact prefixLift 1159476
  have htrace : WordTrace (prefixWord ++ tailWord_1159476) baseStart_1159476 baseEnd_1159476 := by
    simpa [prefixWord, tailWord_1159476, baseEnd_1159476] using wordTrace_append hprefix tailTrace_1159476
  have hstable : (prefixWord ++ tailWord_1159476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159476).length < 2 ^ (prefixWord ++ tailWord_1159476).sum := by decide
  have hdescent : baseEnd_1159476 < baseStart_1159476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159506 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1159506 : Nat := 118140960795 + 1159506 * 2 ^ 59
def prefixEnd_1159506 : Nat := 4983230072969 + 3 ^ 40 * 1159506 * 2
def baseEnd_1159506 : Nat := 595383899772245661142535

theorem tailTrace_1159506 : CollatzResearch.WordTrace tailWord_1159506 prefixEnd_1159506 595383899772245661142535 := by
  unfold tailWord_1159506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10572664534328816176026593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28193772091543509802737581 10572664534328816176026593)
  ·
    refine ⟨7929498400746612132019945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10572664534328816176026593 7929498400746612132019945)
    ·
      refine ⟨5947123800559959099014959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7929498400746612132019945 5947123800559959099014959)
      ·
        refine ⟨8920685700839938648522439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947123800559959099014959 8920685700839938648522439)
        ·
          refine ⟨13381028551259907972783659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8920685700839938648522439 13381028551259907972783659)
          ·
            refine ⟨20071542826889861959175489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13381028551259907972783659 20071542826889861959175489)
            ·
              refine ⟨15053657120167396469381617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20071542826889861959175489 15053657120167396469381617)
              ·
                refine ⟨11290242840125547352036213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15053657120167396469381617 11290242840125547352036213)
                ·
                  refine ⟨1058460266261770064253395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11290242840125547352036213 1058460266261770064253395)
                  ·
                    refine ⟨1587690399392655096380093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1058460266261770064253395 1587690399392655096380093)
                    ·
                      refine ⟨595383899772245661142535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587690399392655096380093 595383899772245661142535)
                      ·
                        rfl

theorem cell23_1159506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1159506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159506 prefixEnd_1159506 := by exact prefixLift 1159506
  have htrace : WordTrace (prefixWord ++ tailWord_1159506) baseStart_1159506 baseEnd_1159506 := by
    simpa [prefixWord, tailWord_1159506, baseEnd_1159506] using wordTrace_append hprefix tailTrace_1159506
  have hstable : (prefixWord ++ tailWord_1159506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159506).length < 2 ^ (prefixWord ++ tailWord_1159506).sum := by decide
  have hdescent : baseEnd_1159506 < baseStart_1159506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159529 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_1159529 : Nat := 118140960795 + 1159529 * 2 ^ 59
def prefixEnd_1159529 : Nat := 4983230072969 + 3 ^ 40 * 1159529 * 2
def baseEnd_1159529 : Nat := 595395709827299071154929

theorem tailTrace_1159529 : CollatzResearch.WordTrace tailWord_1159529 prefixEnd_1159529 595395709827299071154929 := by
  unfold tailWord_1159529
  simp only [CollatzResearch.WordTrace]
  refine ⟨42291497016231939632193641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28194331344154626421462427 42291497016231939632193641)
  ·
    refine ⟨31718622762173954724145231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42291497016231939632193641 31718622762173954724145231)
    ·
      refine ⟨47577934143260932086217847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31718622762173954724145231 47577934143260932086217847)
      ·
        refine ⟨71366901214891398129326771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47577934143260932086217847 71366901214891398129326771)
        ·
          refine ⟨107050351822337097193990157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71366901214891398129326771 107050351822337097193990157)
          ·
            refine ⟨40143881933376411447746309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107050351822337097193990157 40143881933376411447746309)
            ·
              refine ⟨7526977862508077146452433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40143881933376411447746309 7526977862508077146452433)
              ·
                refine ⟨5645233396881057859839325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7526977862508077146452433 5645233396881057859839325)
                ·
                  refine ⟨2116962523830396697439747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5645233396881057859839325 2116962523830396697439747)
                  ·
                    refine ⟨3175443785745595046159621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2116962523830396697439747 3175443785745595046159621)
                    ·
                      refine ⟨595395709827299071154929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3175443785745595046159621 595395709827299071154929)
                      ·
                        rfl

theorem cell23_1159529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_1159529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159529 prefixEnd_1159529 := by exact prefixLift 1159529
  have htrace : WordTrace (prefixWord ++ tailWord_1159529) baseStart_1159529 baseEnd_1159529 := by
    simpa [prefixWord, tailWord_1159529, baseEnd_1159529] using wordTrace_append hprefix tailTrace_1159529
  have hstable : (prefixWord ++ tailWord_1159529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159529).length < 2 ^ (prefixWord ++ tailWord_1159529).sum := by decide
  have hdescent : baseEnd_1159529 < baseStart_1159529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159563 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 1, 1, 4]
def baseStart_1159563 : Nat := 118140960795 + 1159563 * 2 ^ 59
def prefixEnd_1159563 : Nat := 4983230072969 + 3 ^ 40 * 1159563 * 2
def baseEnd_1159563 : Nat := 595413168169551938129773

theorem tailTrace_1159563 : CollatzResearch.WordTrace tailWord_1159563 prefixEnd_1159563 595413168169551938129773 := by
  unfold tailWord_1159563
  simp only [CollatzResearch.WordTrace]
  refine ⟨42292737098108763438931343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28195158065405842292620895 42292737098108763438931343)
  ·
    refine ⟨63439105647163145158397015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42292737098108763438931343 63439105647163145158397015)
    ·
      refine ⟨95158658470744717737595523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63439105647163145158397015 95158658470744717737595523)
      ·
        refine ⟨142737987706117076606393285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95158658470744717737595523 142737987706117076606393285)
        ·
          refine ⟨26763372694896951863698741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142737987706117076606393285 26763372694896951863698741)
          ·
            refine ⟨2509066190146589237221757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26763372694896951863698741 2509066190146589237221757)
            ·
              refine ⟨940899821304970963958159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509066190146589237221757 940899821304970963958159)
              ·
                refine ⟨1411349731957456445937239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940899821304970963958159 1411349731957456445937239)
                ·
                  refine ⟨2117024597936184668905859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411349731957456445937239 2117024597936184668905859)
                  ·
                    refine ⟨3175536896904277003358789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2117024597936184668905859 3175536896904277003358789)
                    ·
                      refine ⟨595413168169551938129773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3175536896904277003358789 595413168169551938129773)
                      ·
                        rfl

theorem cell23_1159563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 1, 4].length) (baseStart_1159563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159563 prefixEnd_1159563 := by exact prefixLift 1159563
  have htrace : WordTrace (prefixWord ++ tailWord_1159563) baseStart_1159563 baseEnd_1159563 := by
    simpa [prefixWord, tailWord_1159563, baseEnd_1159563] using wordTrace_append hprefix tailTrace_1159563
  have hstable : (prefixWord ++ tailWord_1159563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159563).length < 2 ^ (prefixWord ++ tailWord_1159563).sum := by decide
  have hdescent : baseEnd_1159563 < baseStart_1159563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159596 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_1159596 : Nat := 118140960795 + 1159596 * 2 ^ 59
def prefixEnd_1159596 : Nat := 4983230072969 + 3 ^ 40 * 1159596 * 2
def baseEnd_1159596 : Nat := 595430113031150309017121

theorem tailTrace_1159596 : CollatzResearch.WordTrace tailWord_1159596 prefixEnd_1159596 595430113031150309017121 := by
  unfold tailWord_1159596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146970353494605037441321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28195960471326140049921761 21146970353494605037441321)
  ·
    refine ⟨15860227765120953778080991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21146970353494605037441321 15860227765120953778080991)
    ·
      refine ⟨23790341647681430667121487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15860227765120953778080991 23790341647681430667121487)
      ·
        refine ⟨35685512471522146000682231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23790341647681430667121487 35685512471522146000682231)
        ·
          refine ⟨53528268707283219001023347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35685512471522146000682231 53528268707283219001023347)
          ·
            refine ⟨80292403060924828501535021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53528268707283219001023347 80292403060924828501535021)
            ·
              refine ⟨30109651147846810688075633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80292403060924828501535021 30109651147846810688075633)
              ·
                refine ⟨22582238360885108016056725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30109651147846810688075633 22582238360885108016056725)
                ·
                  refine ⟨1058542423166489438252659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22582238360885108016056725 1058542423166489438252659)
                  ·
                    refine ⟨1587813634749734157378989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1058542423166489438252659 1587813634749734157378989)
                    ·
                      refine ⟨595430113031150309017121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1587813634749734157378989 595430113031150309017121)
                      ·
                        rfl

theorem cell23_1159596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_1159596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159596 prefixEnd_1159596 := by exact prefixLift 1159596
  have htrace : WordTrace (prefixWord ++ tailWord_1159596) baseStart_1159596 baseEnd_1159596 := by
    simpa [prefixWord, tailWord_1159596, baseEnd_1159596] using wordTrace_append hprefix tailTrace_1159596
  have hstable : (prefixWord ++ tailWord_1159596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159596).length < 2 ^ (prefixWord ++ tailWord_1159596).sum := by decide
  have hdescent : baseEnd_1159596 < baseStart_1159596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159597 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1159597 : Nat := 118140960795 + 1159597 * 2 ^ 59
def prefixEnd_1159597 : Nat := 4983230072969 + 3 ^ 40 * 1159597 * 2
def baseEnd_1159597 : Nat := 595430626511804805104617

theorem tailTrace_1159597 : CollatzResearch.WordTrace tailWord_1159597 prefixEnd_1159597 595430626511804805104617 := by
  unfold tailWord_1159597
  simp only [CollatzResearch.WordTrace]
  refine ⟨42293977179985587245669045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28195984786657058163779363 42293977179985587245669045)
  ·
    refine ⟨3965060360623648804281473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42293977179985587245669045 3965060360623648804281473)
    ·
      refine ⟨2973795270467736603211105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3965060360623648804281473 2973795270467736603211105)
      ·
        refine ⟨2230346452850802452408329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2973795270467736603211105 2230346452850802452408329)
        ·
          refine ⟨1672759839638101839306247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230346452850802452408329 1672759839638101839306247)
          ·
            refine ⟨2509139759457152758959371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672759839638101839306247 2509139759457152758959371)
            ·
              refine ⟨3763709639185729138439057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509139759457152758959371 3763709639185729138439057)
              ·
                refine ⟨2822782229389296853829293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3763709639185729138439057 2822782229389296853829293)
                ·
                  refine ⟨1058543336020986320185985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2822782229389296853829293 1058543336020986320185985)
                  ·
                    refine ⟨793907502015739740139489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058543336020986320185985 793907502015739740139489)
                    ·
                      refine ⟨595430626511804805104617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793907502015739740139489 595430626511804805104617)
                      ·
                        rfl

theorem cell23_1159597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1159597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159597 prefixEnd_1159597 := by exact prefixLift 1159597
  have htrace : WordTrace (prefixWord ++ tailWord_1159597) baseStart_1159597 baseEnd_1159597 := by
    simpa [prefixWord, tailWord_1159597, baseEnd_1159597] using wordTrace_append hprefix tailTrace_1159597
  have hstable : (prefixWord ++ tailWord_1159597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159597).length < 2 ^ (prefixWord ++ tailWord_1159597).sum := by decide
  have hdescent : baseEnd_1159597 < baseStart_1159597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159639 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1159639 : Nat := 118140960795 + 1159639 * 2 ^ 59
def prefixEnd_1159639 : Nat := 4983230072969 + 3 ^ 40 * 1159639 * 2
def baseEnd_1159639 : Nat := 595452192699293640779423

theorem tailTrace_1159639 : CollatzResearch.WordTrace tailWord_1159639 prefixEnd_1159639 595452192699293640779423 := by
  unfold tailWord_1159639
  simp only [CollatzResearch.WordTrace]
  refine ⟨42295509045833428418697971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28197006030555618945798647 42295509045833428418697971)
  ·
    refine ⟨63443263568750142628046957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42295509045833428418697971 63443263568750142628046957)
    ·
      refine ⟨23791223838281303485517609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63443263568750142628046957 23791223838281303485517609)
      ·
        refine ⟨17843417878710977614138207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23791223838281303485517609 17843417878710977614138207)
        ·
          refine ⟨26765126818066466421207311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17843417878710977614138207 26765126818066466421207311)
          ·
            refine ⟨40147690227099699631810967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26765126818066466421207311 40147690227099699631810967)
            ·
              refine ⟨60221535340649549447716451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40147690227099699631810967 60221535340649549447716451)
              ·
                refine ⟨90332303010974324171574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60221535340649549447716451 90332303010974324171574677)
                ·
                  refine ⟨4234326703639421445542563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90332303010974324171574677 4234326703639421445542563)
                  ·
                    refine ⟨6351490055459132168313845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4234326703639421445542563 6351490055459132168313845)
                    ·
                      refine ⟨595452192699293640779423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6351490055459132168313845 595452192699293640779423)
                      ·
                        rfl

theorem cell23_1159639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1159639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159639 prefixEnd_1159639 := by exact prefixLift 1159639
  have htrace : WordTrace (prefixWord ++ tailWord_1159639) baseStart_1159639 baseEnd_1159639 := by
    simpa [prefixWord, tailWord_1159639, baseEnd_1159639] using wordTrace_append hprefix tailTrace_1159639
  have hstable : (prefixWord ++ tailWord_1159639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159639).length < 2 ^ (prefixWord ++ tailWord_1159639).sum := by decide
  have hdescent : baseEnd_1159639 < baseStart_1159639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159659 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 7]
def baseStart_1159659 : Nat := 118140960795 + 1159659 * 2 ^ 59
def prefixEnd_1159659 : Nat := 4983230072969 + 3 ^ 40 * 1159659 * 2
def baseEnd_1159659 : Nat := 66162495812487062503259

theorem tailTrace_1159659 : CollatzResearch.WordTrace tailWord_1159659 prefixEnd_1159659 66162495812487062503259 := by
  unfold tailWord_1159659
  simp only [CollatzResearch.WordTrace]
  refine ⟨42296238505760971834426031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28197492337173981222950687 42296238505760971834426031)
  ·
    refine ⟨63444357758641457751639047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42296238505760971834426031 63444357758641457751639047)
    ·
      refine ⟨95166536637962186627458571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63444357758641457751639047 95166536637962186627458571)
      ·
        refine ⟨142749804956943279941187857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95166536637962186627458571 142749804956943279941187857)
        ·
          refine ⟨107062353717707459955890893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142749804956943279941187857 107062353717707459955890893)
          ·
            refine ⟨40148382644140297483459085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107062353717707459955890893 40148382644140297483459085)
            ·
              refine ⟨15055643491552611556297157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40148382644140297483459085 15055643491552611556297157)
              ·
                refine ⟨2822933154666114666805717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15055643491552611556297157 2822933154666114666805717)
                ·
                  refine ⟨66162495812487062503259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2822933154666114666805717 66162495812487062503259)
                  ·
                    rfl

theorem cell23_1159659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 7].length) (baseStart_1159659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159659 prefixEnd_1159659 := by exact prefixLift 1159659
  have htrace : WordTrace (prefixWord ++ tailWord_1159659) baseStart_1159659 baseEnd_1159659 := by
    simpa [prefixWord, tailWord_1159659, baseEnd_1159659] using wordTrace_append hprefix tailTrace_1159659
  have hstable : (prefixWord ++ tailWord_1159659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159659).length < 2 ^ (prefixWord ++ tailWord_1159659).sum := by decide
  have hdescent : baseEnd_1159659 < baseStart_1159659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159670 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1159670 : Nat := 118140960795 + 1159670 * 2 ^ 59
def prefixEnd_1159670 : Nat := 4983230072969 + 3 ^ 40 * 1159670 * 2
def baseEnd_1159670 : Nat := 595468110599583019491781

theorem tailTrace_1159670 : CollatzResearch.WordTrace tailWord_1159670 prefixEnd_1159670 595468110599583019491781 := by
  unfold tailWord_1159670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643539981795070044567279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28197759805814080475384309 2643539981795070044567279)
  ·
    refine ⟨3965309972692605066850919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2643539981795070044567279 3965309972692605066850919)
    ·
      refine ⟨5947964959038907600276379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965309972692605066850919 5947964959038907600276379)
      ·
        refine ⟨8921947438558361400414569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947964959038907600276379 8921947438558361400414569)
        ·
          refine ⟨6691460578918771050310927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921947438558361400414569 6691460578918771050310927)
          ·
            refine ⟨10037190868378156575466391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691460578918771050310927 10037190868378156575466391)
            ·
              refine ⟨15055786302567234863199587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10037190868378156575466391 15055786302567234863199587)
              ·
                refine ⟨22583679453850852294799381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15055786302567234863199587 22583679453850852294799381)
                ·
                  refine ⟨1058609974399258701318721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22583679453850852294799381 1058609974399258701318721)
                  ·
                    refine ⟨793957480799444025989041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058609974399258701318721 793957480799444025989041)
                    ·
                      refine ⟨595468110599583019491781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793957480799444025989041 595468110599583019491781)
                      ·
                        rfl

theorem cell23_1159670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1159670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159670 prefixEnd_1159670 := by exact prefixLift 1159670
  have htrace : WordTrace (prefixWord ++ tailWord_1159670) baseStart_1159670 baseEnd_1159670 := by
    simpa [prefixWord, tailWord_1159670, baseEnd_1159670] using wordTrace_append hprefix tailTrace_1159670
  have hstable : (prefixWord ++ tailWord_1159670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159670).length < 2 ^ (prefixWord ++ tailWord_1159670).sum := by decide
  have hdescent : baseEnd_1159670 < baseStart_1159670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159689 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_1159689 : Nat := 118140960795 + 1159689 * 2 ^ 59
def prefixEnd_1159689 : Nat := 4983230072969 + 3 ^ 40 * 1159689 * 2
def baseEnd_1159689 : Nat := 198492622244006148384731

theorem tailTrace_1159689 : CollatzResearch.WordTrace tailWord_1159689 prefixEnd_1159689 198492622244006148384731 := by
  unfold tailWord_1159689
  simp only [CollatzResearch.WordTrace]
  refine ⟨42297332695652286958018121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28198221797101524638678747 42297332695652286958018121)
  ·
    refine ⟨31722999521739215218513591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42297332695652286958018121 31722999521739215218513591)
    ·
      refine ⟨47584499282608822827770387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31722999521739215218513591 47584499282608822827770387)
      ·
        refine ⟨71376748923913234241655581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47584499282608822827770387 71376748923913234241655581)
        ·
          refine ⟨26766280846467462840620843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71376748923913234241655581 26766280846467462840620843)
          ·
            refine ⟨40149421269701194260931265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26766280846467462840620843 40149421269701194260931265)
            ·
              refine ⟨30112065952275895695698449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40149421269701194260931265 30112065952275895695698449)
              ·
                refine ⟨22584049464206921771773837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30112065952275895695698449 22584049464206921771773837)
                ·
                  refine ⟨8469018549077595664415189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22584049464206921771773837 8469018549077595664415189)
                  ·
                    refine ⟨198492622244006148384731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8469018549077595664415189 198492622244006148384731)
                    ·
                      rfl

theorem cell23_1159689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_1159689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159689 prefixEnd_1159689 := by exact prefixLift 1159689
  have htrace : WordTrace (prefixWord ++ tailWord_1159689) baseStart_1159689 baseEnd_1159689 := by
    simpa [prefixWord, tailWord_1159689, baseEnd_1159689] using wordTrace_append hprefix tailTrace_1159689
  have hstable : (prefixWord ++ tailWord_1159689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159689).length < 2 ^ (prefixWord ++ tailWord_1159689).sum := by decide
  have hdescent : baseEnd_1159689 < baseStart_1159689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159704 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1159704 : Nat := 118140960795 + 1159704 * 2 ^ 59
def prefixEnd_1159704 : Nat := 4983230072969 + 3 ^ 40 * 1159704 * 2
def baseEnd_1159704 : Nat := 595485568941835886466625

theorem tailTrace_1159704 : CollatzResearch.WordTrace tailWord_1159704 prefixEnd_1159704 595485568941835886466625 := by
  unfold tailWord_1159704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148939895298972259907083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28198586527065296346542777 21148939895298972259907083)
  ·
    refine ⟨31723409842948458389860625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21148939895298972259907083 31723409842948458389860625)
    ·
      refine ⟨23792557382211343792395469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31723409842948458389860625 23792557382211343792395469)
      ·
        refine ⟨8922209018329253922148301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23792557382211343792395469 8922209018329253922148301)
        ·
          refine ⟨3345828381873470220805613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8922209018329253922148301 3345828381873470220805613)
          ·
            refine ⟨1254685643202551332802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3345828381873470220805613 1254685643202551332802105)
            ·
              refine ⟨941014232401913499601579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254685643202551332802105 941014232401913499601579)
              ·
                refine ⟨1411521348602870249402369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941014232401913499601579 1411521348602870249402369)
                ·
                  refine ⟨1058641011452152687051777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411521348602870249402369 1058641011452152687051777)
                  ·
                    refine ⟨793980758589114515288833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058641011452152687051777 793980758589114515288833)
                    ·
                      refine ⟨595485568941835886466625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 793980758589114515288833 595485568941835886466625)
                      ·
                        rfl

theorem cell23_1159704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1159704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159704 prefixEnd_1159704 := by exact prefixLift 1159704
  have htrace : WordTrace (prefixWord ++ tailWord_1159704) baseStart_1159704 baseEnd_1159704 := by
    simpa [prefixWord, tailWord_1159704, baseEnd_1159704] using wordTrace_append hprefix tailTrace_1159704
  have hstable : (prefixWord ++ tailWord_1159704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159704).length < 2 ^ (prefixWord ++ tailWord_1159704).sum := by decide
  have hdescent : baseEnd_1159704 < baseStart_1159704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159743 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 4, 2]
def baseStart_1159743 : Nat := 118140960795 + 1159743 * 2 ^ 59
def prefixEnd_1159743 : Nat := 4983230072969 + 3 ^ 40 * 1159743 * 2
def baseEnd_1159743 : Nat := 595505594687361233878945

theorem tailTrace_1159743 : CollatzResearch.WordTrace tailWord_1159743 prefixEnd_1159743 595505594687361233878945 := by
  unfold tailWord_1159743
  simp only [CollatzResearch.WordTrace]
  refine ⟨42299302237456654180483883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28199534824971102786989255 42299302237456654180483883)
  ·
    refine ⟨63448953356184981270725825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42299302237456654180483883 63448953356184981270725825)
    ·
      refine ⟨47586715017138735953044369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63448953356184981270725825 47586715017138735953044369)
      ·
        refine ⟨35690036262854051964783277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47586715017138735953044369 35690036262854051964783277)
        ·
          refine ⟨13383763598570269486793729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35690036262854051964783277 13383763598570269486793729)
          ·
            refine ⟨10037822698927702115095297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13383763598570269486793729 10037822698927702115095297)
            ·
              refine ⟨7528367024195776586321473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10037822698927702115095297 7528367024195776586321473)
              ·
                refine ⟨5646275268146832439741105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7528367024195776586321473 5646275268146832439741105)
                ·
                  refine ⟨4234706451110124329805829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5646275268146832439741105 4234706451110124329805829)
                  ·
                    refine ⟨794007459583148311838593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4234706451110124329805829 794007459583148311838593)
                    ·
                      refine ⟨595505594687361233878945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794007459583148311838593 595505594687361233878945)
                      ·
                        rfl

theorem cell23_1159743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_1159743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159743 prefixEnd_1159743 := by exact prefixLift 1159743
  have htrace : WordTrace (prefixWord ++ tailWord_1159743) baseStart_1159743 baseEnd_1159743 := by
    simpa [prefixWord, tailWord_1159743, baseEnd_1159743] using wordTrace_append hprefix tailTrace_1159743
  have hstable : (prefixWord ++ tailWord_1159743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159743).length < 2 ^ (prefixWord ++ tailWord_1159743).sum := by decide
  have hdescent : baseEnd_1159743 < baseStart_1159743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159750 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1159750 : Nat := 118140960795 + 1159750 * 2 ^ 59
def prefixEnd_1159750 : Nat := 4983230072969 + 3 ^ 40 * 1159750 * 2
def baseEnd_1159750 : Nat := 595509189051942706491413

theorem tailTrace_1159750 : CollatzResearch.WordTrace tailWord_1159750 prefixEnd_1159750 595509189051942706491413 := by
  unfold tailWord_1159750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321861173388477949249647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28199705032287529583992469 1321861173388477949249647)
  ·
    refine ⟨1982791760082716923874471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321861173388477949249647 1982791760082716923874471)
    ·
      refine ⟨2974187640124075385811707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982791760082716923874471 2974187640124075385811707)
      ·
        refine ⟨4461281460186113078717561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974187640124075385811707 4461281460186113078717561)
        ·
          refine ⟨3345961095139584809038171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4461281460186113078717561 3345961095139584809038171)
          ·
            refine ⟨5018941642709377213557257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345961095139584809038171 5018941642709377213557257)
            ·
              refine ⟨3764206232032032910167943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018941642709377213557257 3764206232032032910167943)
              ·
                refine ⟨5646309348048049365251915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764206232032032910167943 5646309348048049365251915)
                ·
                  refine ⟨8469464022072074047877873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5646309348048049365251915 8469464022072074047877873)
                  ·
                    refine ⟨6352098016554055535908405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8469464022072074047877873 6352098016554055535908405)
                    ·
                      refine ⟨595509189051942706491413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6352098016554055535908405 595509189051942706491413)
                      ·
                        rfl

theorem cell23_1159750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1159750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159750 prefixEnd_1159750 := by exact prefixLift 1159750
  have htrace : WordTrace (prefixWord ++ tailWord_1159750) baseStart_1159750 baseEnd_1159750 := by
    simpa [prefixWord, tailWord_1159750, baseEnd_1159750] using wordTrace_append hprefix tailTrace_1159750
  have hstable : (prefixWord ++ tailWord_1159750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159750).length < 2 ^ (prefixWord ++ tailWord_1159750).sum := by decide
  have hdescent : baseEnd_1159750 < baseStart_1159750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159833 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 6, 2]
def baseStart_1159833 : Nat := 118140960795 + 1159833 * 2 ^ 59
def prefixEnd_1159833 : Nat := 4983230072969 + 3 ^ 40 * 1159833 * 2
def baseEnd_1159833 : Nat := 595551807946265881753531

theorem tailTrace_1159833 : CollatzResearch.WordTrace tailWord_1159833 prefixEnd_1159833 595551807946265881753531 := by
  unfold tailWord_1159833
  simp only [CollatzResearch.WordTrace]
  refine ⟨42302584807130599551260153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28201723204753733034173435 42302584807130599551260153)
  ·
    refine ⟨31726938605347949663445115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42302584807130599551260153 31726938605347949663445115)
    ·
      refine ⟨47590407908021924495167673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31726938605347949663445115 47590407908021924495167673)
      ·
        refine ⟨35692805931016443371375755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47590407908021924495167673 35692805931016443371375755)
        ·
          refine ⟨53539208896524665057063633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35692805931016443371375755 53539208896524665057063633)
          ·
            refine ⟨40154406672393498792797725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53539208896524665057063633 40154406672393498792797725)
            ·
              refine ⟨15057902502147562047299147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40154406672393498792797725 15057902502147562047299147)
              ·
                refine ⟨22586853753221343070948721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15057902502147562047299147 22586853753221343070948721)
                ·
                  refine ⟨16940140314916007303211541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22586853753221343070948721 16940140314916007303211541)
                  ·
                    refine ⟨794069077261687842338041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16940140314916007303211541 794069077261687842338041)
                    ·
                      refine ⟨595551807946265881753531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794069077261687842338041 595551807946265881753531)
                      ·
                        rfl

theorem cell23_1159833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_1159833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159833 prefixEnd_1159833 := by exact prefixLift 1159833
  have htrace : WordTrace (prefixWord ++ tailWord_1159833) baseStart_1159833 baseEnd_1159833 := by
    simpa [prefixWord, tailWord_1159833, baseEnd_1159833] using wordTrace_append hprefix tailTrace_1159833
  have hstable : (prefixWord ++ tailWord_1159833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159833).length < 2 ^ (prefixWord ++ tailWord_1159833).sum := by decide
  have hdescent : baseEnd_1159833 < baseStart_1159833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159854 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1159854 : Nat := 118140960795 + 1159854 * 2 ^ 59
def prefixEnd_1159854 : Nat := 4983230072969 + 3 ^ 40 * 1159854 * 2
def baseEnd_1159854 : Nat := 595562591040010299590935

theorem tailTrace_1159854 : CollatzResearch.WordTrace tailWord_1159854 prefixEnd_1159854 595562591040010299590935 := by
  unfold tailWord_1159854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287918842506815017221827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28202233826703013425183077 5287918842506815017221827)
  ·
    refine ⟨7931878263760222525832741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287918842506815017221827 7931878263760222525832741)
    ·
      refine ⟨1487227174455041723593639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7931878263760222525832741 1487227174455041723593639)
      ·
        refine ⟨2230840761682562585390459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487227174455041723593639 2230840761682562585390459)
        ·
          refine ⟨3346261142523843878085689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230840761682562585390459 3346261142523843878085689)
          ·
            refine ⟨2509695856892882908564267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3346261142523843878085689 2509695856892882908564267)
            ·
              refine ⟨3764543785339324362846401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509695856892882908564267 3764543785339324362846401)
              ·
                refine ⟨2823407839004493272134801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3764543785339324362846401 2823407839004493272134801)
                ·
                  refine ⟨2117555879253369954101101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2823407839004493272134801 2117555879253369954101101)
                  ·
                    refine ⟨794083454720013732787913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2117555879253369954101101 794083454720013732787913)
                    ·
                      refine ⟨595562591040010299590935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794083454720013732787913 595562591040010299590935)
                      ·
                        rfl

theorem cell23_1159854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1159854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159854 prefixEnd_1159854 := by exact prefixLift 1159854
  have htrace : WordTrace (prefixWord ++ tailWord_1159854) baseStart_1159854 baseEnd_1159854 := by
    simpa [prefixWord, tailWord_1159854, baseEnd_1159854] using wordTrace_append hprefix tailTrace_1159854
  have hstable : (prefixWord ++ tailWord_1159854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159854).length < 2 ^ (prefixWord ++ tailWord_1159854).sum := by decide
  have hdescent : baseEnd_1159854 < baseStart_1159854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159861 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1159861 : Nat := 118140960795 + 1159861 * 2 ^ 59
def prefixEnd_1159861 : Nat := 4983230072969 + 3 ^ 40 * 1159861 * 2
def baseEnd_1159861 : Nat := 595566185404591772203403

theorem tailTrace_1159861 : CollatzResearch.WordTrace tailWord_1159861 prefixEnd_1159861 595566185404591772203403 := by
  unfold tailWord_1159861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42303606051029160333279437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28202404034019440222186291 42303606051029160333279437)
  ·
    refine ⟨15863852269135935124979789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42303606051029160333279437 15863852269135935124979789)
    ·
      refine ⟨5948944600925975671867421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15863852269135935124979789 5948944600925975671867421)
      ·
        refine ⟨2230854225347240876950283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5948944600925975671867421 2230854225347240876950283)
        ·
          refine ⟨3346281338020861315425425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230854225347240876950283 3346281338020861315425425)
          ·
            refine ⟨2509711003515645986569069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3346281338020861315425425 2509711003515645986569069)
            ·
              refine ⟨941141626318367244963401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509711003515645986569069 941141626318367244963401)
              ·
                refine ⟨705856219738775433722551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941141626318367244963401 705856219738775433722551)
                ·
                  refine ⟨1058784329608163150583827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705856219738775433722551 1058784329608163150583827)
                  ·
                    refine ⟨1588176494412244725875741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1058784329608163150583827 1588176494412244725875741)
                    ·
                      refine ⟨595566185404591772203403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588176494412244725875741 595566185404591772203403)
                      ·
                        rfl

theorem cell23_1159861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1159861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159861 prefixEnd_1159861 := by exact prefixLift 1159861
  have htrace : WordTrace (prefixWord ++ tailWord_1159861) baseStart_1159861 baseEnd_1159861 := by
    simpa [prefixWord, tailWord_1159861, baseEnd_1159861] using wordTrace_append hprefix tailTrace_1159861
  have hstable : (prefixWord ++ tailWord_1159861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159861).length < 2 ^ (prefixWord ++ tailWord_1159861).sum := by decide
  have hdescent : baseEnd_1159861 < baseStart_1159861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159870 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1159870 : Nat := 118140960795 + 1159870 * 2 ^ 59
def prefixEnd_1159870 : Nat := 4983230072969 + 3 ^ 40 * 1159870 * 2
def baseEnd_1159870 : Nat := 595570806730482236990861

theorem tailTrace_1159870 : CollatzResearch.WordTrace tailWord_1159870 prefixEnd_1159870 595570806730482236990861 := by
  unfold tailWord_1159870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287991788499569358794633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28202622871997703246904709 5287991788499569358794633)
  ·
    refine ⟨3965993841374677019095975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5287991788499569358794633 3965993841374677019095975)
    ·
      refine ⟨5948990762062015528643963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3965993841374677019095975 5948990762062015528643963)
      ·
        refine ⟨8923486143093023292965945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5948990762062015528643963 8923486143093023292965945)
        ·
          refine ⟨6692614607319767469724459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8923486143093023292965945 6692614607319767469724459)
          ·
            refine ⟨10038921910979651204586689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692614607319767469724459 10038921910979651204586689)
            ·
              refine ⟨7529191433234738403440017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10038921910979651204586689 7529191433234738403440017)
              ·
                refine ⟨5646893574926053802580013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7529191433234738403440017 5646893574926053802580013)
                ·
                  refine ⟨2117585090597270175967505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5646893574926053802580013 2117585090597270175967505)
                  ·
                    refine ⟨1588188817947952631975629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117585090597270175967505 1588188817947952631975629)
                    ·
                      refine ⟨595570806730482236990861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588188817947952631975629 595570806730482236990861)
                      ·
                        rfl

theorem cell23_1159870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1159870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159870 prefixEnd_1159870 := by exact prefixLift 1159870
  have htrace : WordTrace (prefixWord ++ tailWord_1159870) baseStart_1159870 baseEnd_1159870 := by
    simpa [prefixWord, tailWord_1159870, baseEnd_1159870] using wordTrace_append hprefix tailTrace_1159870
  have hstable : (prefixWord ++ tailWord_1159870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159870).length < 2 ^ (prefixWord ++ tailWord_1159870).sum := by decide
  have hdescent : baseEnd_1159870 < baseStart_1159870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159918 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_1159918 : Nat := 118140960795 + 1159918 * 2 ^ 59
def prefixEnd_1159918 : Nat := 4983230072969 + 3 ^ 40 * 1159918 * 2
def baseEnd_1159918 : Nat := 595595453801898049190641

theorem tailTrace_1159918 : CollatzResearch.WordTrace tailWord_1159918 prefixEnd_1159918 595595453801898049190641 := by
  unfold tailWord_1159918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288210626477832383513051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28203790007881772712069605 5288210626477832383513051)
  ·
    refine ⟨7932315939716748575269577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288210626477832383513051 7932315939716748575269577)
    ·
      refine ⟨5949236954787561431452183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7932315939716748575269577 5949236954787561431452183)
      ·
        refine ⟨8923855432181342147178275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949236954787561431452183 8923855432181342147178275)
        ·
          refine ⟨13385783148272013220767413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8923855432181342147178275 13385783148272013220767413)
          ·
            refine ⟨1254917170150501239446945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13385783148272013220767413 1254917170150501239446945)
            ·
              refine ⟨941187877612875929585209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254917170150501239446945 941187877612875929585209)
              ·
                refine ⟨705890908209656947188907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941187877612875929585209 705890908209656947188907)
                ·
                  refine ⟨1058836362314485420783361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705890908209656947188907 1058836362314485420783361)
                  ·
                    refine ⟨794127271735864065587521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058836362314485420783361 794127271735864065587521)
                    ·
                      refine ⟨595595453801898049190641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794127271735864065587521 595595453801898049190641)
                      ·
                        rfl

theorem cell23_1159918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_1159918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159918 prefixEnd_1159918 := by exact prefixLift 1159918
  have htrace : WordTrace (prefixWord ++ tailWord_1159918) baseStart_1159918 baseEnd_1159918 := by
    simpa [prefixWord, tailWord_1159918, baseEnd_1159918] using wordTrace_append hprefix tailTrace_1159918
  have hstable : (prefixWord ++ tailWord_1159918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159918).length < 2 ^ (prefixWord ++ tailWord_1159918).sum := by decide
  have hdescent : baseEnd_1159918 < baseStart_1159918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159924 : List Nat := [2, 6, 1, 1, 2, 2, 1, 8]
def baseStart_1159924 : Nat := 118140960795 + 1159924 * 2 ^ 59
def prefixEnd_1159924 : Nat := 4983230072969 + 3 ^ 40 * 1159924 * 2
def baseEnd_1159924 : Nat := 22059204988363889841319

theorem tailTrace_1159924 : CollatzResearch.WordTrace tailWord_1159924 prefixEnd_1159924 22059204988363889841319 := by
  unfold tailWord_1159924
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152951924900461046411413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28203935899867281395215217 21152951924900461046411413)
  ·
    refine ⟨991544621479709111550535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21152951924900461046411413 991544621479709111550535)
    ·
      refine ⟨1487316932219563667325803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991544621479709111550535 1487316932219563667325803)
      ·
        refine ⟨2230975398329345500988705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487316932219563667325803 2230975398329345500988705)
        ·
          refine ⟨1673231548747009125741529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2230975398329345500988705 1673231548747009125741529)
          ·
            refine ⟨1254923661560256844306147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673231548747009125741529 1254923661560256844306147)
            ·
              refine ⟨1882385492340385266459221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254923661560256844306147 1882385492340385266459221)
              ·
                refine ⟨22059204988363889841319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1882385492340385266459221 22059204988363889841319)
                ·
                  rfl

theorem cell23_1159924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 8].length) (baseStart_1159924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159924 prefixEnd_1159924 := by exact prefixLift 1159924
  have htrace : WordTrace (prefixWord ++ tailWord_1159924) baseStart_1159924 baseEnd_1159924 := by
    simpa [prefixWord, tailWord_1159924, baseEnd_1159924] using wordTrace_append hprefix tailTrace_1159924
  have hstable : (prefixWord ++ tailWord_1159924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159924).length < 2 ^ (prefixWord ++ tailWord_1159924).sum := by decide
  have hdescent : baseEnd_1159924 < baseStart_1159924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159933 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1159933 : Nat := 118140960795 + 1159933 * 2 ^ 59
def prefixEnd_1159933 : Nat := 4983230072969 + 3 ^ 40 * 1159933 * 2
def baseEnd_1159933 : Nat := 198534385337238496834357

theorem tailTrace_1159933 : CollatzResearch.WordTrace tailWord_1159933 prefixEnd_1159933 198534385337238496834357 := by
  unfold tailWord_1159933
  simp only [CollatzResearch.WordTrace]
  refine ⟨42306232106768316629900453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28204154737845544419933635 42306232106768316629900453)
  ·
    refine ⟨7932418520019059368106335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42306232106768316629900453 7932418520019059368106335)
    ·
      refine ⟨11898627780028589052159503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7932418520019059368106335 11898627780028589052159503)
      ·
        refine ⟨17847941670042883578239255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11898627780028589052159503 17847941670042883578239255)
        ·
          refine ⟨26771912505064325367358883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17847941670042883578239255 26771912505064325367358883)
          ·
            refine ⟨40157868757596488051038325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26771912505064325367358883 40157868757596488051038325)
            ·
              refine ⟨3764800196024670754784843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40157868757596488051038325 3764800196024670754784843)
              ·
                refine ⟨5647200294037006132177265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3764800196024670754784843 5647200294037006132177265)
                ·
                  refine ⟨4235400220527754599132949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5647200294037006132177265 4235400220527754599132949)
                  ·
                    refine ⟨198534385337238496834357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4235400220527754599132949 198534385337238496834357)
                    ·
                      rfl

theorem cell23_1159933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1159933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159933 prefixEnd_1159933 := by exact prefixLift 1159933
  have htrace : WordTrace (prefixWord ++ tailWord_1159933) baseStart_1159933 baseEnd_1159933 := by
    simpa [prefixWord, tailWord_1159933, baseEnd_1159933] using wordTrace_append hprefix tailTrace_1159933
  have hstable : (prefixWord ++ tailWord_1159933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159933).length < 2 ^ (prefixWord ++ tailWord_1159933).sum := by decide
  have hdescent : baseEnd_1159933 < baseStart_1159933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159934 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1159934 : Nat := 118140960795 + 1159934 * 2 ^ 59
def prefixEnd_1159934 : Nat := 4983230072969 + 3 ^ 40 * 1159934 * 2
def baseEnd_1159934 : Nat := 595603669492369986590567

theorem tailTrace_1159934 : CollatzResearch.WordTrace tailWord_1159934 prefixEnd_1159934 595603669492369986590567 := by
  unfold tailWord_1159934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288283572470586725085857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28204179053176462533791237 5288283572470586725085857)
  ·
    refine ⟨3966212679352940043814393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5288283572470586725085857 3966212679352940043814393)
    ·
      refine ⟨2974659509514705032860795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3966212679352940043814393 2974659509514705032860795)
      ·
        refine ⟨4461989264272057549291193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974659509514705032860795 4461989264272057549291193)
        ·
          refine ⟨3346491948204043161968395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4461989264272057549291193 3346491948204043161968395)
          ·
            refine ⟨5019737922306064742952593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346491948204043161968395 5019737922306064742952593)
            ·
              refine ⟨3764803441729548557214445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5019737922306064742952593 3764803441729548557214445)
              ·
                refine ⟨1411801290648580708955417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3764803441729548557214445 1411801290648580708955417)
                ·
                  refine ⟨1058850967986435531716563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411801290648580708955417 1058850967986435531716563)
                  ·
                    refine ⟨1588276451979653297574845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1058850967986435531716563 1588276451979653297574845)
                    ·
                      refine ⟨595603669492369986590567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588276451979653297574845 595603669492369986590567)
                      ·
                        rfl

theorem cell23_1159934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1159934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159934 prefixEnd_1159934 := by exact prefixLift 1159934
  have htrace : WordTrace (prefixWord ++ tailWord_1159934) baseStart_1159934 baseEnd_1159934 := by
    simpa [prefixWord, tailWord_1159934, baseEnd_1159934] using wordTrace_append hprefix tailTrace_1159934
  have hstable : (prefixWord ++ tailWord_1159934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159934).length < 2 ^ (prefixWord ++ tailWord_1159934).sum := by decide
  have hdescent : baseEnd_1159934 < baseStart_1159934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159957 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_1159957 : Nat := 118140960795 + 1159957 * 2 ^ 59
def prefixEnd_1159957 : Nat := 4983230072969 + 3 ^ 40 * 1159957 * 2
def baseEnd_1159957 : Nat := 595615479547423396602961

theorem tailTrace_1159957 : CollatzResearch.WordTrace tailWord_1159957 prefixEnd_1159957 595615479547423396602961 := by
  unfold tailWord_1159957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42307107458681368728774125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28204738305787579152516083 42307107458681368728774125)
  ·
    refine ⟨15865165297005513273290297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42307107458681368728774125 15865165297005513273290297)
    ·
      refine ⟨11898873972754134954967723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15865165297005513273290297 11898873972754134954967723)
      ·
        refine ⟨17848310959131202432451585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11898873972754134954967723 17848310959131202432451585)
        ·
          refine ⟨13386233219348401824338689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17848310959131202432451585 13386233219348401824338689)
          ·
            refine ⟨10039674914511301368254017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13386233219348401824338689 10039674914511301368254017)
            ·
              refine ⟨7529756185883476026190513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10039674914511301368254017 7529756185883476026190513)
              ·
                refine ⟨5647317139412607019642885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7529756185883476026190513 5647317139412607019642885)
                ·
                  refine ⟨1058871963639863816183041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5647317139412607019642885 1058871963639863816183041)
                  ·
                    refine ⟨794153972729897862137281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058871963639863816183041 794153972729897862137281)
                    ·
                      refine ⟨595615479547423396602961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794153972729897862137281 595615479547423396602961)
                      ·
                        rfl

theorem cell23_1159957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_1159957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159957 prefixEnd_1159957 := by exact prefixLift 1159957
  have htrace : WordTrace (prefixWord ++ tailWord_1159957) baseStart_1159957 baseEnd_1159957 := by
    simpa [prefixWord, tailWord_1159957, baseEnd_1159957] using wordTrace_append hprefix tailTrace_1159957
  have hstable : (prefixWord ++ tailWord_1159957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159957).length < 2 ^ (prefixWord ++ tailWord_1159957).sum := by decide
  have hdescent : baseEnd_1159957 < baseStart_1159957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159970 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1159970 : Nat := 118140960795 + 1159970 * 2 ^ 59
def prefixEnd_1159970 : Nat := 4983230072969 + 3 ^ 40 * 1159970 * 2
def baseEnd_1159970 : Nat := 595622154795931845740401

theorem tailTrace_1159970 : CollatzResearch.WordTrace tailWord_1159970 prefixEnd_1159970 595622154795931845740401 := by
  unfold tailWord_1159970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10576895401908567987249341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28205054405089514632664909 10576895401908567987249341)
  ·
    refine ⟨3966335775715712995218503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10576895401908567987249341 3966335775715712995218503)
    ·
      refine ⟨5949503663573569492827755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3966335775715712995218503 5949503663573569492827755)
      ·
        refine ⟨8924255495360354239241633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949503663573569492827755 8924255495360354239241633)
        ·
          refine ⟨6693191621520265679431225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8924255495360354239241633 6693191621520265679431225)
          ·
            refine ⟨5019893716140199259573419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6693191621520265679431225 5019893716140199259573419)
            ·
              refine ⟨7529840574210298889360129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019893716140199259573419 7529840574210298889360129)
              ·
                refine ⟨5647380430657724167020097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7529840574210298889360129 5647380430657724167020097)
                ·
                  refine ⟨4235535322993293125265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5647380430657724167020097 4235535322993293125265073)
                  ·
                    refine ⟨3176651492244969843948805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4235535322993293125265073 3176651492244969843948805)
                    ·
                      refine ⟨595622154795931845740401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3176651492244969843948805 595622154795931845740401)
                      ·
                        rfl

theorem cell23_1159970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1159970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159970 prefixEnd_1159970 := by exact prefixLift 1159970
  have htrace : WordTrace (prefixWord ++ tailWord_1159970) baseStart_1159970 baseEnd_1159970 := by
    simpa [prefixWord, tailWord_1159970, baseEnd_1159970] using wordTrace_append hprefix tailTrace_1159970
  have hstable : (prefixWord ++ tailWord_1159970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159970).length < 2 ^ (prefixWord ++ tailWord_1159970).sum := by decide
  have hdescent : baseEnd_1159970 < baseStart_1159970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159980 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 5]
def baseStart_1159980 : Nat := 118140960795 + 1159980 * 2 ^ 59
def prefixEnd_1159980 : Nat := 4983230072969 + 3 ^ 40 * 1159980 * 2
def baseEnd_1159980 : Nat := 66180809955830756290595

theorem tailTrace_1159980 : CollatzResearch.WordTrace tailWord_1159980 prefixEnd_1159980 66180809955830756290595 := by
  unfold tailWord_1159980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21153973168799021828430697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28205297558398695771240929 21153973168799021828430697)
  ·
    refine ⟨15865479876599266371323023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21153973168799021828430697 15865479876599266371323023)
    ·
      refine ⟨23798219814898899556984535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15865479876599266371323023 23798219814898899556984535)
      ·
        refine ⟨35697329722348349335476803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23798219814898899556984535 35697329722348349335476803)
        ·
          refine ⟨53545994583522524003215205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35697329722348349335476803 53545994583522524003215205)
          ·
            refine ⟨10039873984410473250602851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53545994583522524003215205 10039873984410473250602851)
            ·
              refine ⟨15059810976615709875904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10039873984410473250602851 15059810976615709875904277)
              ·
                refine ⟨705928639528861400433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15059810976615709875904277 705928639528861400433013)
                ·
                  refine ⟨66180809955830756290595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 705928639528861400433013 66180809955830756290595)
                  ·
                    rfl

theorem cell23_1159980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_1159980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1159980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1159980 prefixEnd_1159980 := by exact prefixLift 1159980
  have htrace : WordTrace (prefixWord ++ tailWord_1159980) baseStart_1159980 baseEnd_1159980 := by
    simpa [prefixWord, tailWord_1159980, baseEnd_1159980] using wordTrace_append hprefix tailTrace_1159980
  have hstable : (prefixWord ++ tailWord_1159980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159980).length < 2 ^ (prefixWord ++ tailWord_1159980).sum := by decide
  have hdescent : baseEnd_1159980 < baseStart_1159980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160000 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2]
def baseStart_1160000 : Nat := 118140960795 + 1160000 * 2 ^ 59
def prefixEnd_1160000 : Nat := 4983230072969 + 3 ^ 40 * 1160000 * 2
def baseEnd_1160000 : Nat := 595637559215566728365263

theorem tailTrace_1160000 : CollatzResearch.WordTrace tailWord_1160000 prefixEnd_1160000 595637559215566728365263 := by
  unfold tailWord_1160000
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154337898762793536294727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28205783865017058048392969 21154337898762793536294727)
  ·
    refine ⟨31731506848144190304442091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21154337898762793536294727 31731506848144190304442091)
    ·
      refine ⟨47597260272216285456663137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31731506848144190304442091 47597260272216285456663137)
      ·
        refine ⟨35697945204162214092497353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47597260272216285456663137 35697945204162214092497353)
        ·
          refine ⟨26773458903121660569373015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35697945204162214092497353 26773458903121660569373015)
          ·
            refine ⟨40160188354682490854059523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26773458903121660569373015 40160188354682490854059523)
            ·
              refine ⟨60240282532023736281089285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40160188354682490854059523 60240282532023736281089285)
              ·
                refine ⟨11295052974754450552704241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60240282532023736281089285 11295052974754450552704241)
                ·
                  refine ⟨8471289731065837914528181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295052974754450552704241 8471289731065837914528181)
                  ·
                    refine ⟨794183412287422304487017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8471289731065837914528181 794183412287422304487017)
                    ·
                      refine ⟨595637559215566728365263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794183412287422304487017 595637559215566728365263)
                      ·
                        rfl

theorem cell23_1160000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_1160000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160000 prefixEnd_1160000 := by exact prefixLift 1160000
  have htrace : WordTrace (prefixWord ++ tailWord_1160000) baseStart_1160000 baseEnd_1160000 := by
    simpa [prefixWord, tailWord_1160000, baseEnd_1160000] using wordTrace_append hprefix tailTrace_1160000
  have hstable : (prefixWord ++ tailWord_1160000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160000).length < 2 ^ (prefixWord ++ tailWord_1160000).sum := by decide
  have hdescent : baseEnd_1160000 < baseStart_1160000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160033 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1160033 : Nat := 118140960795 + 1160033 * 2 ^ 59
def prefixEnd_1160033 : Nat := 4983230072969 + 3 ^ 40 * 1160033 * 2
def baseEnd_1160033 : Nat := 595654504077165099252611

theorem tailTrace_1160033 : CollatzResearch.WordTrace tailWord_1160033 prefixEnd_1160033 595654504077165099252611 := by
  unfold tailWord_1160033
  simp only [CollatzResearch.WordTrace]
  refine ⟨42309879406406033708540753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28206586270937355805693835 42309879406406033708540753)
  ·
    refine ⟨31732409554804525281405565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42309879406406033708540753 31732409554804525281405565)
    ·
      refine ⟨11899653583051696980527087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31732409554804525281405565 11899653583051696980527087)
      ·
        refine ⟨17849480374577545470790631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11899653583051696980527087 17849480374577545470790631)
        ·
          refine ⟨26774220561866318206185947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17849480374577545470790631 26774220561866318206185947)
          ·
            refine ⟨40161330842799477309278921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26774220561866318206185947 40161330842799477309278921)
            ·
              refine ⟨30120998132099607981959191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40161330842799477309278921 30120998132099607981959191)
              ·
                refine ⟨45181497198149411972938787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30120998132099607981959191 45181497198149411972938787)
                ·
                  refine ⟨67772245797224117959408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45181497198149411972938787 67772245797224117959408181)
                  ·
                    refine ⟨6353648043489761058694517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67772245797224117959408181 6353648043489761058694517)
                    ·
                      refine ⟨595654504077165099252611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6353648043489761058694517 595654504077165099252611)
                      ·
                        rfl

theorem cell23_1160033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1160033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160033 prefixEnd_1160033 := by exact prefixLift 1160033
  have htrace : WordTrace (prefixWord ++ tailWord_1160033) baseStart_1160033 baseEnd_1160033 := by
    simpa [prefixWord, tailWord_1160033, baseEnd_1160033] using wordTrace_append hprefix tailTrace_1160033
  have hstable : (prefixWord ++ tailWord_1160033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160033).length < 2 ^ (prefixWord ++ tailWord_1160033).sum := by decide
  have hdescent : baseEnd_1160033 < baseStart_1160033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160043 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_1160043 : Nat := 118140960795 + 1160043 * 2 ^ 59
def prefixEnd_1160043 : Nat := 4983230072969 + 3 ^ 40 * 1160043 * 2
def baseEnd_1160043 : Nat := 595659638883710060127565

theorem tailTrace_1160043 : CollatzResearch.WordTrace tailWord_1160043 prefixEnd_1160043 595659638883710060127565 := by
  unfold tailWord_1160043
  simp only [CollatzResearch.WordTrace]
  refine ⟨42310244136369805416404783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28206829424246536944269855 42310244136369805416404783)
  ·
    refine ⟨63465366204554708124607175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42310244136369805416404783 63465366204554708124607175)
    ·
      refine ⟨95198049306832062186910763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63465366204554708124607175 95198049306832062186910763)
      ·
        refine ⟨142797073960248093280366145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95198049306832062186910763 142797073960248093280366145)
        ·
          refine ⟨107097805470186069960274609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142797073960248093280366145 107097805470186069960274609)
          ·
            refine ⟨80323354102639552470205957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107097805470186069960274609 80323354102639552470205957)
            ·
              refine ⟨15060628894244916088163617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80323354102639552470205957 15060628894244916088163617)
              ·
                refine ⟨11295471670683687066122713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15060628894244916088163617 11295471670683687066122713)
                ·
                  refine ⟨8471603753012765299592035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11295471670683687066122713 8471603753012765299592035)
                  ·
                    refine ⟨12707405629519147949388053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8471603753012765299592035 12707405629519147949388053)
                    ·
                      refine ⟨595659638883710060127565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12707405629519147949388053 595659638883710060127565)
                      ·
                        rfl

theorem cell23_1160043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_1160043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160043 prefixEnd_1160043 := by exact prefixLift 1160043
  have htrace : WordTrace (prefixWord ++ tailWord_1160043) baseStart_1160043 baseEnd_1160043 := by
    simpa [prefixWord, tailWord_1160043, baseEnd_1160043] using wordTrace_append hprefix tailTrace_1160043
  have hstable : (prefixWord ++ tailWord_1160043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160043).length < 2 ^ (prefixWord ++ tailWord_1160043).sum := by decide
  have hdescent : baseEnd_1160043 < baseStart_1160043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160050 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1160050 : Nat := 118140960795 + 1160050 * 2 ^ 59
def prefixEnd_1160050 : Nat := 4983230072969 + 3 ^ 40 * 1160050 * 2
def baseEnd_1160050 : Nat := 595663233248291532740033

theorem tailTrace_1160050 : CollatzResearch.WordTrace tailWord_1160050 prefixEnd_1160050 595663233248291532740033 := by
  unfold tailWord_1160050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577624861836111402977401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28206999631562963741273069 10577624861836111402977401)
  ·
    refine ⟨7933218646377083552233051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10577624861836111402977401 7933218646377083552233051)
    ·
      refine ⟨11899827969565625328349577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7933218646377083552233051 11899827969565625328349577)
      ·
        refine ⟨8924870977174218996262183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11899827969565625328349577 8924870977174218996262183)
        ·
          refine ⟨13387306465761328494393275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8924870977174218996262183 13387306465761328494393275)
          ·
            refine ⟨20080959698641992741589913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13387306465761328494393275 20080959698641992741589913)
            ·
              refine ⟨15060719773981494556192435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20080959698641992741589913 15060719773981494556192435)
              ·
                refine ⟨22591079660972241834288653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15060719773981494556192435 22591079660972241834288653)
                ·
                  refine ⟨8471654872864590687858245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22591079660972241834288653 8471654872864590687858245)
                  ·
                    refine ⟨1588435288662110753973421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8471654872864590687858245 1588435288662110753973421)
                    ·
                      refine ⟨595663233248291532740033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588435288662110753973421 595663233248291532740033)
                      ·
                        rfl

theorem cell23_1160050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1160050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160050 prefixEnd_1160050 := by exact prefixLift 1160050
  have htrace : WordTrace (prefixWord ++ tailWord_1160050) baseStart_1160050 baseEnd_1160050 := by
    simpa [prefixWord, tailWord_1160050, baseEnd_1160050] using wordTrace_append hprefix tailTrace_1160050
  have hstable : (prefixWord ++ tailWord_1160050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160050).length < 2 ^ (prefixWord ++ tailWord_1160050).sum := by decide
  have hdescent : baseEnd_1160050 < baseStart_1160050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160067 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3]
def baseStart_1160067 : Nat := 118140960795 + 1160067 * 2 ^ 59
def prefixEnd_1160067 : Nat := 4983230072969 + 3 ^ 40 * 1160067 * 2
def baseEnd_1160067 : Nat := 595671962419417966227455

theorem tailTrace_1160067 : CollatzResearch.WordTrace tailWord_1160067 prefixEnd_1160067 595671962419417966227455 := by
  unfold tailWord_1160067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42311119488282857515278455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28207412992188571676852303 42311119488282857515278455)
  ·
    refine ⟨63466679232424286272917683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42311119488282857515278455 63466679232424286272917683)
    ·
      refine ⟨95200018848636429409376525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63466679232424286272917683 95200018848636429409376525)
      ·
        refine ⟨35700007068238661028516197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95200018848636429409376525 35700007068238661028516197)
        ·
          refine ⟨6693751325294748942846787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35700007068238661028516197 6693751325294748942846787)
          ·
            refine ⟨10040626987942123414270181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6693751325294748942846787 10040626987942123414270181)
            ·
              refine ⟨1882617560239148140175659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10040626987942123414270181 1882617560239148140175659)
              ·
                refine ⟨2823926340358722210263489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882617560239148140175659 2823926340358722210263489)
                ·
                  refine ⟨2117944755269041657697617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2823926340358722210263489 2117944755269041657697617)
                  ·
                    refine ⟨1588458566451781243273213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117944755269041657697617 1588458566451781243273213)
                    ·
                      refine ⟨595671962419417966227455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588458566451781243273213 595671962419417966227455)
                      ·
                        rfl

theorem cell23_1160067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_1160067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160067 prefixEnd_1160067 := by exact prefixLift 1160067
  have htrace : WordTrace (prefixWord ++ tailWord_1160067) baseStart_1160067 baseEnd_1160067 := by
    simpa [prefixWord, tailWord_1160067, baseEnd_1160067] using wordTrace_append hprefix tailTrace_1160067
  have hstable : (prefixWord ++ tailWord_1160067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160067).length < 2 ^ (prefixWord ++ tailWord_1160067).sum := by decide
  have hdescent : baseEnd_1160067 < baseStart_1160067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160100 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_1160100 : Nat := 118140960795 + 1160100 * 2 ^ 59
def prefixEnd_1160100 : Nat := 4983230072969 + 3 ^ 40 * 1160100 * 2
def baseEnd_1160100 : Nat := 198562969093672112371601

theorem tailTrace_1160100 : CollatzResearch.WordTrace tailWord_1160100 prefixEnd_1160100 198562969093672112371601 := by
  unfold tailWord_1160100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21156161548581652075614877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28208215398108869434153169 21156161548581652075614877)
  ·
    refine ⟨7933560580718119528355579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21156161548581652075614877 7933560580718119528355579)
    ·
      refine ⟨11900340871077179292533369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7933560580718119528355579 11900340871077179292533369)
      ·
        refine ⟨8925255653307884469400027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11900340871077179292533369 8925255653307884469400027)
        ·
          refine ⟨13387883479961826704100041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925255653307884469400027 13387883479961826704100041)
          ·
            refine ⟨10040912609971370028075031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13387883479961826704100041 10040912609971370028075031)
            ·
              refine ⟨15061368914957055042112547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10040912609971370028075031 15061368914957055042112547)
              ·
                refine ⟨22592053372435582563168821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15061368914957055042112547 22592053372435582563168821)
                ·
                  refine ⟨2118005003665835865297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22592053372435582563168821 2118005003665835865297077)
                  ·
                    refine ⟨198562969093672112371601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2118005003665835865297077 198562969093672112371601)
                    ·
                      rfl

theorem cell23_1160100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_1160100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160100 prefixEnd_1160100 := by exact prefixLift 1160100
  have htrace : WordTrace (prefixWord ++ tailWord_1160100) baseStart_1160100 baseEnd_1160100 := by
    simpa [prefixWord, tailWord_1160100, baseEnd_1160100] using wordTrace_append hprefix tailTrace_1160100
  have hstable : (prefixWord ++ tailWord_1160100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160100).length < 2 ^ (prefixWord ++ tailWord_1160100).sum := by decide
  have hdescent : baseEnd_1160100 < baseStart_1160100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160117 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1160117 : Nat := 118140960795 + 1160117 * 2 ^ 59
def prefixEnd_1160117 : Nat := 4983230072969 + 3 ^ 40 * 1160117 * 2
def baseEnd_1160117 : Nat := 198565878817380923534075

theorem tailTrace_1160117 : CollatzResearch.WordTrace tailWord_1160117 prefixEnd_1160117 198565878817380923534075 := by
  unfold tailWord_1160117
  simp only [CollatzResearch.WordTrace]
  refine ⟨42312943138101716054598605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28208628758734477369732403 42312943138101716054598605)
  ·
    refine ⟨15867353676788143520474477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42312943138101716054598605 15867353676788143520474477)
    ·
      refine ⟨5950257628795553820177929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15867353676788143520474477 5950257628795553820177929)
      ·
        refine ⟨4462693221596665365133447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5950257628795553820177929 4462693221596665365133447)
        ·
          refine ⟨6694039832394998047700171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462693221596665365133447 6694039832394998047700171)
          ·
            refine ⟨10041059748592497071550257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694039832394998047700171 10041059748592497071550257)
            ·
              refine ⟨7530794811444372803662693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10041059748592497071550257 7530794811444372803662693)
              ·
                refine ⟨1412024027145819900686755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7530794811444372803662693 1412024027145819900686755)
                ·
                  refine ⟨2118036040718729851030133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412024027145819900686755 2118036040718729851030133)
                  ·
                    refine ⟨198565878817380923534075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2118036040718729851030133 198565878817380923534075)
                    ·
                      rfl

theorem cell23_1160117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1160117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160117 prefixEnd_1160117 := by exact prefixLift 1160117
  have htrace : WordTrace (prefixWord ++ tailWord_1160117) baseStart_1160117 baseEnd_1160117 := by
    simpa [prefixWord, tailWord_1160117, baseEnd_1160117] using wordTrace_append hprefix tailTrace_1160117
  have hstable : (prefixWord ++ tailWord_1160117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160117).length < 2 ^ (prefixWord ++ tailWord_1160117).sum := by decide
  have hdescent : baseEnd_1160117 < baseStart_1160117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160118 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1160118 : Nat := 118140960795 + 1160118 * 2 ^ 59
def prefixEnd_1160118 : Nat := 4983230072969 + 3 ^ 40 * 1160118 * 2
def baseEnd_1160118 : Nat := 595698149932797266689721

theorem tailTrace_1160118 : CollatzResearch.WordTrace tailWord_1160118 prefixEnd_1160118 595698149932797266689721 := by
  unfold tailWord_1160118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644561225693630826586563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28208653074065395483590005 2644561225693630826586563)
  ·
    refine ⟨3966841838540446239879845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2644561225693630826586563 3966841838540446239879845)
    ·
      refine ⟨743782844726333669977471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3966841838540446239879845 743782844726333669977471)
      ·
        refine ⟨1115674267089500504966207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743782844726333669977471 1115674267089500504966207)
        ·
          refine ⟨1673511400634250757449311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115674267089500504966207 1673511400634250757449311)
          ·
            refine ⟨2510267100951376136173967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673511400634250757449311 2510267100951376136173967)
            ·
              refine ⟨3765400651427064204260951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510267100951376136173967 3765400651427064204260951)
              ·
                refine ⟨5648100977140596306391427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765400651427064204260951 5648100977140596306391427)
                ·
                  refine ⟨8472151465710894459587141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648100977140596306391427 8472151465710894459587141)
                  ·
                    refine ⟨1588528399820792711172589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8472151465710894459587141 1588528399820792711172589)
                    ·
                      refine ⟨595698149932797266689721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588528399820792711172589 595698149932797266689721)
                      ·
                        rfl

theorem cell23_1160118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1160118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160118 prefixEnd_1160118 := by exact prefixLift 1160118
  have htrace : WordTrace (prefixWord ++ tailWord_1160118) baseStart_1160118 baseEnd_1160118 := by
    simpa [prefixWord, tailWord_1160118, baseEnd_1160118] using wordTrace_append hprefix tailTrace_1160118
  have hstable : (prefixWord ++ tailWord_1160118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160118).length < 2 ^ (prefixWord ++ tailWord_1160118).sum := by decide
  have hdescent : baseEnd_1160118 < baseStart_1160118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160157 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1160157 : Nat := 118140960795 + 1160157 * 2 ^ 59
def prefixEnd_1160157 : Nat := 4983230072969 + 3 ^ 40 * 1160157 * 2
def baseEnd_1160157 : Nat := 595718175678322614102041

theorem tailTrace_1160157 : CollatzResearch.WordTrace tailWord_1160157 prefixEnd_1160157 595718175678322614102041 := by
  unfold tailWord_1160157
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314402057956802886054725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28209601371971201924036483 42314402057956802886054725)
  ·
    refine ⟨7933950385866900541135261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42314402057956802886054725 7933950385866900541135261)
    ·
      refine ⟨2975231394700087702925723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7933950385866900541135261 2975231394700087702925723)
      ·
        refine ⟨4462847092050131554388585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975231394700087702925723 4462847092050131554388585)
        ·
          refine ⟨3347135319037598665791439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462847092050131554388585 3347135319037598665791439)
          ·
            refine ⟨5020702978556397998687159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347135319037598665791439 5020702978556397998687159)
            ·
              refine ⟨7531054467834596998030739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020702978556397998687159 7531054467834596998030739)
              ·
                refine ⟨11296581701751895497046109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7531054467834596998030739 11296581701751895497046109)
                ·
                  refine ⟨4236218138156960811392291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11296581701751895497046109 4236218138156960811392291)
                  ·
                    refine ⟨6354327207235441217088437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4236218138156960811392291 6354327207235441217088437)
                    ·
                      refine ⟨595718175678322614102041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6354327207235441217088437 595718175678322614102041)
                      ·
                        rfl

theorem cell23_1160157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1160157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160157 prefixEnd_1160157 := by exact prefixLift 1160157
  have htrace : WordTrace (prefixWord ++ tailWord_1160157) baseStart_1160157 baseEnd_1160157 := by
    simpa [prefixWord, tailWord_1160157, baseEnd_1160157] using wordTrace_append hprefix tailTrace_1160157
  have hstable : (prefixWord ++ tailWord_1160157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160157).length < 2 ^ (prefixWord ++ tailWord_1160157).sum := by decide
  have hdescent : baseEnd_1160157 < baseStart_1160157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160167 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1160167 : Nat := 118140960795 + 1160167 * 2 ^ 59
def prefixEnd_1160167 : Nat := 4983230072969 + 3 ^ 40 * 1160167 * 2
def baseEnd_1160167 : Nat := 595723310484867574976995

theorem tailTrace_1160167 : CollatzResearch.WordTrace tailWord_1160167 prefixEnd_1160167 595723310484867574976995 := by
  unfold tailWord_1160167
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314766787920574593918755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28209844525280383062612503 42314766787920574593918755)
  ·
    refine ⟨63472150181880861890878133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42314766787920574593918755 63472150181880861890878133)
    ·
      refine ⟨5950514079551330802269825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63472150181880861890878133 5950514079551330802269825)
      ·
        refine ⟨4462885559663498101702369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5950514079551330802269825 4462885559663498101702369)
        ·
          refine ⟨3347164169747623576276777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462885559663498101702369 3347164169747623576276777)
          ·
            refine ⟨2510373127310717682207583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347164169747623576276777 2510373127310717682207583)
            ·
              refine ⟨3765559690966076523311375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510373127310717682207583 3765559690966076523311375)
              ·
                refine ⟨5648339536449114784967063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765559690966076523311375 5648339536449114784967063)
                ·
                  refine ⟨8472509304673672177450595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648339536449114784967063 8472509304673672177450595)
                  ·
                    refine ⟨12708763957010508266175893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8472509304673672177450595 12708763957010508266175893)
                    ·
                      refine ⟨595723310484867574976995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12708763957010508266175893 595723310484867574976995)
                      ·
                        rfl

theorem cell23_1160167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1160167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160167 prefixEnd_1160167 := by exact prefixLift 1160167
  have htrace : WordTrace (prefixWord ++ tailWord_1160167) baseStart_1160167 baseEnd_1160167 := by
    simpa [prefixWord, tailWord_1160167, baseEnd_1160167] using wordTrace_append hprefix tailTrace_1160167
  have hstable : (prefixWord ++ tailWord_1160167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160167).length < 2 ^ (prefixWord ++ tailWord_1160167).sum := by decide
  have hdescent : baseEnd_1160167 < baseStart_1160167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160177 : List Nat := [1, 2, 2, 2, 4, 1, 4, 7]
def baseStart_1160177 : Nat := 118140960795 + 1160177 * 2 ^ 59
def prefixEnd_1160177 : Nat := 4983230072969 + 3 ^ 40 * 1160177 * 2
def baseEnd_1160177 : Nat := 22064016492274538364887

theorem tailTrace_1160177 : CollatzResearch.WordTrace tailWord_1160177 prefixEnd_1160177 22064016492274538364887 := by
  unfold tailWord_1160177
  simp only [CollatzResearch.WordTrace]
  refine ⟨42315131517884346301782785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28210087678589564201188523 42315131517884346301782785)
  ·
    refine ⟨31736348638413259726337089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42315131517884346301782785 31736348638413259726337089)
    ·
      refine ⟨23802261478809944794752817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31736348638413259726337089 23802261478809944794752817)
      ·
        refine ⟨17851696109107458596064613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23802261478809944794752817 17851696109107458596064613)
        ·
          refine ⟨3347193020457648486762115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17851696109107458596064613 3347193020457648486762115)
          ·
            refine ⟨5020789530686472730143173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347193020457648486762115 5020789530686472730143173)
            ·
              refine ⟨941398037003713636901845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5020789530686472730143173 941398037003713636901845)
              ·
                refine ⟨22064016492274538364887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 941398037003713636901845 22064016492274538364887)
                ·
                  rfl

theorem cell23_1160177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 7].length) (baseStart_1160177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160177 prefixEnd_1160177 := by exact prefixLift 1160177
  have htrace : WordTrace (prefixWord ++ tailWord_1160177) baseStart_1160177 baseEnd_1160177 := by
    simpa [prefixWord, tailWord_1160177, baseEnd_1160177] using wordTrace_append hprefix tailTrace_1160177
  have hstable : (prefixWord ++ tailWord_1160177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160177).length < 2 ^ (prefixWord ++ tailWord_1160177).sum := by decide
  have hdescent : baseEnd_1160177 < baseStart_1160177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160188 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_1160188 : Nat := 118140960795 + 1160188 * 2 ^ 59
def prefixEnd_1160188 : Nat := 4983230072969 + 3 ^ 40 * 1160188 * 2
def baseEnd_1160188 : Nat := 595734093578611992814399

theorem tailTrace_1160188 : CollatzResearch.WordTrace tailWord_1160188 prefixEnd_1160188 595734093578611992814399 := by
  unfold tailWord_1160188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21157766360422247590216609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28210355147229663453622145 21157766360422247590216609)
  ·
    refine ⟨15868324770316685692662457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21157766360422247590216609 15868324770316685692662457)
    ·
      refine ⟨11901243577737514269496843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15868324770316685692662457 11901243577737514269496843)
      ·
        refine ⟨17851865366606271404245265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11901243577737514269496843 17851865366606271404245265)
        ·
          refine ⟨13388899024954703553183949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17851865366606271404245265 13388899024954703553183949)
          ·
            refine ⟨5020837134358013832443981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13388899024954703553183949 5020837134358013832443981)
            ·
              refine ⟨1882813925384255187166493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5020837134358013832443981 1882813925384255187166493)
              ·
                refine ⟨706055222019095695187435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1882813925384255187166493 706055222019095695187435)
                ·
                  refine ⟨1059082833028643542781153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706055222019095695187435 1059082833028643542781153)
                  ·
                    refine ⟨794312124771482657085865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059082833028643542781153 794312124771482657085865)
                    ·
                      refine ⟨595734093578611992814399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794312124771482657085865 595734093578611992814399)
                      ·
                        rfl

theorem cell23_1160188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_1160188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160188 prefixEnd_1160188 := by exact prefixLift 1160188
  have htrace : WordTrace (prefixWord ++ tailWord_1160188) baseStart_1160188 baseEnd_1160188 := by
    simpa [prefixWord, tailWord_1160188, baseEnd_1160188] using wordTrace_append hprefix tailTrace_1160188
  have hstable : (prefixWord ++ tailWord_1160188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160188).length < 2 ^ (prefixWord ++ tailWord_1160188).sum := by decide
  have hdescent : baseEnd_1160188 < baseStart_1160188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160204 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1160204 : Nat := 118140960795 + 1160204 * 2 ^ 59
def prefixEnd_1160204 : Nat := 4983230072969 + 3 ^ 40 * 1160204 * 2
def baseEnd_1160204 : Nat := 595742309269083930214325

theorem tailTrace_1160204 : CollatzResearch.WordTrace tailWord_1160204 prefixEnd_1160204 595742309269083930214325 := by
  unfold tailWord_1160204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21158058144393264956507833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28210744192524353275343777 21158058144393264956507833)
  ·
    refine ⟨15868543608294948717380875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21158058144393264956507833 15868543608294948717380875)
    ·
      refine ⟨23802815412442423076071313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15868543608294948717380875 23802815412442423076071313)
      ·
        refine ⟨17852111559331817307053485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23802815412442423076071313 17852111559331817307053485)
        ·
          refine ⟨6694541834749431490145057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17852111559331817307053485 6694541834749431490145057)
          ·
            refine ⟨5020906376062073617608793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6694541834749431490145057 5020906376062073617608793)
            ·
              refine ⟨3765679782046555213206595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020906376062073617608793 3765679782046555213206595)
              ·
                refine ⟨5648519673069832819809893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765679782046555213206595 5648519673069832819809893)
                ·
                  refine ⟨1059097438700593653714355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5648519673069832819809893 1059097438700593653714355)
                  ·
                    refine ⟨1588646158050890480571533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059097438700593653714355 1588646158050890480571533)
                    ·
                      refine ⟨595742309269083930214325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588646158050890480571533 595742309269083930214325)
                      ·
                        rfl

theorem cell23_1160204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1160204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160204 prefixEnd_1160204 := by exact prefixLift 1160204
  have htrace : WordTrace (prefixWord ++ tailWord_1160204) baseStart_1160204 baseEnd_1160204 := by
    simpa [prefixWord, tailWord_1160204, baseEnd_1160204] using wordTrace_append hprefix tailTrace_1160204
  have hstable : (prefixWord ++ tailWord_1160204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160204).length < 2 ^ (prefixWord ++ tailWord_1160204).sum := by decide
  have hdescent : baseEnd_1160204 < baseStart_1160204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160248 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_1160248 : Nat := 118140960795 + 1160248 * 2 ^ 59
def prefixEnd_1160248 : Nat := 4983230072969 + 3 ^ 40 * 1160248 * 2
def baseEnd_1160248 : Nat := 595764902417881758064123

theorem tailTrace_1160248 : CollatzResearch.WordTrace tailWord_1160248 prefixEnd_1160248 595764902417881758064123 := by
  unfold tailWord_1160248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21158860550313562713808699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28211814067084750285078265 21158860550313562713808699)
  ·
    refine ⟨31738290825470344070713049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21158860550313562713808699 31738290825470344070713049)
    ·
      refine ⟨23803718119102758053034787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31738290825470344070713049 23803718119102758053034787)
      ·
        refine ⟨35705577178654137079552181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23803718119102758053034787 35705577178654137079552181)
        ·
          refine ⟨3347397860498825351208017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35705577178654137079552181 3347397860498825351208017)
          ·
            refine ⟨2510548395374119013406013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347397860498825351208017 2510548395374119013406013)
            ·
              refine ⟨941455648265294630027255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2510548395374119013406013 941455648265294630027255)
              ·
                refine ⟨1412183472397941945040883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941455648265294630027255 1412183472397941945040883)
                ·
                  refine ⟨2118275208596912917561325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412183472397941945040883 2118275208596912917561325)
                  ·
                    refine ⟨794353203223842344085497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2118275208596912917561325 794353203223842344085497)
                    ·
                      refine ⟨595764902417881758064123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794353203223842344085497 595764902417881758064123)
                      ·
                        rfl

theorem cell23_1160248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_1160248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160248 prefixEnd_1160248 := by exact prefixLift 1160248
  have htrace : WordTrace (prefixWord ++ tailWord_1160248) baseStart_1160248 baseEnd_1160248 := by
    simpa [prefixWord, tailWord_1160248, baseEnd_1160248] using wordTrace_append hprefix tailTrace_1160248
  have hstable : (prefixWord ++ tailWord_1160248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160248).length < 2 ^ (prefixWord ++ tailWord_1160248).sum := by decide
  have hdescent : baseEnd_1160248 < baseStart_1160248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160261 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_1160261 : Nat := 118140960795 + 1160261 * 2 ^ 59
def prefixEnd_1160261 : Nat := 4983230072969 + 3 ^ 40 * 1160261 * 2
def baseEnd_1160261 : Nat := 595771577666390207201563

theorem tailTrace_1160261 : CollatzResearch.WordTrace tailWord_1160261 prefixEnd_1160261 595771577666390207201563 := by
  unfold tailWord_1160261
  simp only [CollatzResearch.WordTrace]
  refine ⟨42318195249580028647840637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28212130166386685765227091 42318195249580028647840637)
  ·
    refine ⟨15869323218592510742940239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42318195249580028647840637 15869323218592510742940239)
    ·
      refine ⟨23803984827888766114410359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15869323218592510742940239 23803984827888766114410359)
      ·
        refine ⟨35705977241833149171615539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23803984827888766114410359 35705977241833149171615539)
        ·
          refine ⟨53558965862749723757423309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35705977241833149171615539 53558965862749723757423309)
          ·
            refine ⟨20084612198531146409033741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53558965862749723757423309 20084612198531146409033741)
            ·
              refine ⟨7531729574449179903387653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20084612198531146409033741 7531729574449179903387653)
              ·
                refine ⟨1412199295209221231885185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7531729574449179903387653 1412199295209221231885185)
                ·
                  refine ⟨1059149471406915923913889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412199295209221231885185 1059149471406915923913889)
                  ·
                    refine ⟨794362103555186942935417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059149471406915923913889 794362103555186942935417)
                    ·
                      refine ⟨595771577666390207201563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794362103555186942935417 595771577666390207201563)
                      ·
                        rfl

theorem cell23_1160261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_1160261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160261 prefixEnd_1160261 := by exact prefixLift 1160261
  have htrace : WordTrace (prefixWord ++ tailWord_1160261) baseStart_1160261 baseEnd_1160261 := by
    simpa [prefixWord, tailWord_1160261, baseEnd_1160261] using wordTrace_append hprefix tailTrace_1160261
  have hstable : (prefixWord ++ tailWord_1160261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160261).length < 2 ^ (prefixWord ++ tailWord_1160261).sum := by decide
  have hdescent : baseEnd_1160261 < baseStart_1160261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160274 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1160274 : Nat := 118140960795 + 1160274 * 2 ^ 59
def prefixEnd_1160274 : Nat := 4983230072969 + 3 ^ 40 * 1160274 * 2
def baseEnd_1160274 : Nat := 595778252914898656339003

theorem tailTrace_1160274 : CollatzResearch.WordTrace tailWord_1160274 prefixEnd_1160274 595778252914898656339003 := by
  unfold tailWord_1160274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579667349633232967015969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28212446265688621245375917 10579667349633232967015969)
  ·
    refine ⟨7934750512224924725261977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10579667349633232967015969 7934750512224924725261977)
    ·
      refine ⟨5951062884168693543946483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7934750512224924725261977 5951062884168693543946483)
      ·
        refine ⟨8926594326253040315919725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951062884168693543946483 8926594326253040315919725)
        ·
          refine ⟨3347472872344890118469897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8926594326253040315919725 3347472872344890118469897)
          ·
            refine ⟨2510604654258667588852423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3347472872344890118469897 2510604654258667588852423)
            ·
              refine ⟨3765906981388001383278635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510604654258667588852423 3765906981388001383278635)
              ·
                refine ⟨5648860472082002074917953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765906981388001383278635 5648860472082002074917953)
                ·
                  refine ⟨4236645354061501556188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5648860472082002074917953 4236645354061501556188465)
                  ·
                    refine ⟨3177484015546126167141349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236645354061501556188465 3177484015546126167141349)
                    ·
                      refine ⟨595778252914898656339003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3177484015546126167141349 595778252914898656339003)
                      ·
                        rfl

theorem cell23_1160274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1160274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160274 prefixEnd_1160274 := by exact prefixLift 1160274
  have htrace : WordTrace (prefixWord ++ tailWord_1160274) baseStart_1160274 baseEnd_1160274 := by
    simpa [prefixWord, tailWord_1160274, baseEnd_1160274] using wordTrace_append hprefix tailTrace_1160274
  have hstable : (prefixWord ++ tailWord_1160274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160274).length < 2 ^ (prefixWord ++ tailWord_1160274).sum := by decide
  have hdescent : baseEnd_1160274 < baseStart_1160274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160297 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_1160297 : Nat := 118140960795 + 1160297 * 2 ^ 59
def prefixEnd_1160297 : Nat := 4983230072969 + 3 ^ 40 * 1160297 * 2
def baseEnd_1160297 : Nat := 198596687656650688783799

theorem tailTrace_1160297 : CollatzResearch.WordTrace tailWord_1160297 prefixEnd_1160297 198596687656650688783799 := by
  unfold tailWord_1160297
  simp only [CollatzResearch.WordTrace]
  refine ⟨42319508277449606796151145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28213005518299737864100763 42319508277449606796151145)
  ·
    refine ⟨31739631208087205097113359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42319508277449606796151145 31739631208087205097113359)
    ·
      refine ⟨47609446812130807645670039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31739631208087205097113359 47609446812130807645670039)
      ·
        refine ⟨71414170218196211468505059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47609446812130807645670039 71414170218196211468505059)
        ·
          refine ⟨107121255327294317202757589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71414170218196211468505059 107121255327294317202757589)
          ·
            refine ⟨2510654421733460559439631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107121255327294317202757589 2510654421733460559439631)
            ·
              refine ⟨3765981632600190839159447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510654421733460559439631 3765981632600190839159447)
              ·
                refine ⟨5648972448900286258739171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3765981632600190839159447 5648972448900286258739171)
                ·
                  refine ⟨8473458673350429388108757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5648972448900286258739171 8473458673350429388108757)
                  ·
                    refine ⟨198596687656650688783799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8473458673350429388108757 198596687656650688783799)
                    ·
                      rfl

theorem cell23_1160297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_1160297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160297 prefixEnd_1160297 := by exact prefixLift 1160297
  have htrace : WordTrace (prefixWord ++ tailWord_1160297) baseStart_1160297 baseEnd_1160297 := by
    simpa [prefixWord, tailWord_1160297, baseEnd_1160297] using wordTrace_append hprefix tailTrace_1160297
  have hstable : (prefixWord ++ tailWord_1160297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160297).length < 2 ^ (prefixWord ++ tailWord_1160297).sum := by decide
  have hdescent : baseEnd_1160297 < baseStart_1160297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160301 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1160301 : Nat := 118140960795 + 1160301 * 2 ^ 59
def prefixEnd_1160301 : Nat := 4983230072969 + 3 ^ 40 * 1160301 * 2
def baseEnd_1160301 : Nat := 66199124099174450077931

theorem tailTrace_1160301 : CollatzResearch.WordTrace tailWord_1160301 prefixEnd_1160301 66199124099174450077931 := by
  unfold tailWord_1160301
  simp only [CollatzResearch.WordTrace]
  refine ⟨42319654169435115479296757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28213102779623410319531171 42319654169435115479296757)
  ·
    refine ⟨3967467578384542076184071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42319654169435115479296757 3967467578384542076184071)
    ·
      refine ⟨5951201367576813114276107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3967467578384542076184071 5951201367576813114276107)
      ·
        refine ⟨8926802051365219671414161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951201367576813114276107 8926802051365219671414161)
        ·
          refine ⟨6695101538523914753560621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8926802051365219671414161 6695101538523914753560621)
          ·
            refine ⟨2510663076946468032585233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6695101538523914753560621 2510663076946468032585233)
            ·
              refine ⟨1882997307709851024438925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510663076946468032585233 1882997307709851024438925)
              ·
                refine ⟨706123990391194134164597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1882997307709851024438925 706123990391194134164597)
                ·
                  refine ⟨66199124099174450077931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706123990391194134164597 66199124099174450077931)
                  ·
                    rfl

theorem cell23_1160301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1160301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160301 prefixEnd_1160301 := by exact prefixLift 1160301
  have htrace : WordTrace (prefixWord ++ tailWord_1160301) baseStart_1160301 baseEnd_1160301 := by
    simpa [prefixWord, tailWord_1160301, baseEnd_1160301] using wordTrace_append hprefix tailTrace_1160301
  have hstable : (prefixWord ++ tailWord_1160301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160301).length < 2 ^ (prefixWord ++ tailWord_1160301).sum := by decide
  have hdescent : baseEnd_1160301 < baseStart_1160301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160334 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1160334 : Nat := 118140960795 + 1160334 * 2 ^ 59
def prefixEnd_1160334 : Nat := 4983230072969 + 3 ^ 40 * 1160334 * 2
def baseEnd_1160334 : Nat := 595809061754168421588727

theorem tailTrace_1160334 : CollatzResearch.WordTrace tailWord_1160334 prefixEnd_1160334 595809061754168421588727 := by
  unfold tailWord_1160334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290107222289445264406007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28213905185543708076832037 5290107222289445264406007)
  ·
    refine ⟨7935160833434167896609011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5290107222289445264406007 7935160833434167896609011)
    ·
      refine ⟨11902741250151251844913517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7935160833434167896609011 11902741250151251844913517)
      ·
        refine ⟨4463527968806719441842569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11902741250151251844913517 4463527968806719441842569)
        ·
          refine ⟨3347645976605039581381927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463527968806719441842569 3347645976605039581381927)
          ·
            refine ⟨5021468964907559372072891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347645976605039581381927 5021468964907559372072891)
            ·
              refine ⟨7532203447361339058109337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021468964907559372072891 7532203447361339058109337)
              ·
                refine ⟨5649152585521004293582003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532203447361339058109337 5649152585521004293582003)
                ·
                  refine ⟨8473728878281506440373005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649152585521004293582003 8473728878281506440373005)
                  ·
                    refine ⟨3177648329355564915139877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8473728878281506440373005 3177648329355564915139877)
                    ·
                      refine ⟨595809061754168421588727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3177648329355564915139877 595809061754168421588727)
                      ·
                        rfl

theorem cell23_1160334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1160334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160334 prefixEnd_1160334 := by exact prefixLift 1160334
  have htrace : WordTrace (prefixWord ++ tailWord_1160334) baseStart_1160334 baseEnd_1160334 := by
    simpa [prefixWord, tailWord_1160334, baseEnd_1160334] using wordTrace_append hprefix tailTrace_1160334
  have hstable : (prefixWord ++ tailWord_1160334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160334).length < 2 ^ (prefixWord ++ tailWord_1160334).sum := by decide
  have hdescent : baseEnd_1160334 < baseStart_1160334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160357 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 8]
def baseStart_1160357 : Nat := 118140960795 + 1160357 * 2 ^ 59
def prefixEnd_1160357 : Nat := 4983230072969 + 3 ^ 40 * 1160357 * 2
def baseEnd_1160357 : Nat := 66202319089913536844569

theorem tailTrace_1160357 : CollatzResearch.WordTrace tailWord_1160357 prefixEnd_1160357 66202319089913536844569 := by
  unfold tailWord_1160357
  simp only [CollatzResearch.WordTrace]
  refine ⟨42321696657232237043335325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28214464438154824695556883 42321696657232237043335325)
  ·
    refine ⟨15870636246462088891250747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42321696657232237043335325 15870636246462088891250747)
    ·
      refine ⟨23805954369693133336876121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15870636246462088891250747 23805954369693133336876121)
      ·
        refine ⟨17854465777269850002657091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23805954369693133336876121 17854465777269850002657091)
        ·
          refine ⟨26781698665904775003985637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17854465777269850002657091 26781698665904775003985637)
          ·
            refine ⟨5021568499857145313247307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26781698665904775003985637 5021568499857145313247307)
            ·
              refine ⟨7532352749785717969870961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021568499857145313247307 7532352749785717969870961)
              ·
                refine ⟨5649264562339288477403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532352749785717969870961 5649264562339288477403221)
                ·
                  refine ⟨66202319089913536844569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5649264562339288477403221 66202319089913536844569)
                  ·
                    rfl

theorem cell23_1160357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_1160357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160357 prefixEnd_1160357 := by exact prefixLift 1160357
  have htrace : WordTrace (prefixWord ++ tailWord_1160357) baseStart_1160357 baseEnd_1160357 := by
    simpa [prefixWord, tailWord_1160357, baseEnd_1160357] using wordTrace_append hprefix tailTrace_1160357
  have hstable : (prefixWord ++ tailWord_1160357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160357).length < 2 ^ (prefixWord ++ tailWord_1160357).sum := by decide
  have hdescent : baseEnd_1160357 < baseStart_1160357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160435 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 1, 1, 3]
def baseStart_1160435 : Nat := 118140960795 + 1160435 * 2 ^ 59
def prefixEnd_1160435 : Nat := 4983230072969 + 3 ^ 40 * 1160435 * 2
def baseEnd_1160435 : Nat := 595860923300272526425763

theorem tailTrace_1160435 : CollatzResearch.WordTrace tailWord_1160435 prefixEnd_1160435 595860923300272526425763 := by
  unfold tailWord_1160435
  simp only [CollatzResearch.WordTrace]
  refine ⟨42324541550949656364674759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28216361033966437576449839 42324541550949656364674759)
  ·
    refine ⟨63486812326424484547012139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42324541550949656364674759 63486812326424484547012139)
    ·
      refine ⟨95230218489636726820518209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63486812326424484547012139 95230218489636726820518209)
      ·
        refine ⟨71422663867227545115388657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95230218489636726820518209 71422663867227545115388657)
        ·
          refine ⟨53566997900420658836541493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71422663867227545115388657 53566997900420658836541493)
          ·
            refine ⟨5021906053164436765925765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53566997900420658836541493 5021906053164436765925765)
            ·
              refine ⟨941607384968331893611081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5021906053164436765925765 941607384968331893611081)
              ·
                refine ⟨706205538726248920208311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941607384968331893611081 706205538726248920208311)
                ·
                  refine ⟨1059308308089373380312467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706205538726248920208311 1059308308089373380312467)
                  ·
                    refine ⟨1588962462134060070468701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1059308308089373380312467 1588962462134060070468701)
                    ·
                      refine ⟨595860923300272526425763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1588962462134060070468701 595860923300272526425763)
                      ·
                        rfl

theorem cell23_1160435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 1, 3].length) (baseStart_1160435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160435 prefixEnd_1160435 := by exact prefixLift 1160435
  have htrace : WordTrace (prefixWord ++ tailWord_1160435) baseStart_1160435 baseEnd_1160435 := by
    simpa [prefixWord, tailWord_1160435, baseEnd_1160435] using wordTrace_append hprefix tailTrace_1160435
  have hstable : (prefixWord ++ tailWord_1160435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160435).length < 2 ^ (prefixWord ++ tailWord_1160435).sum := by decide
  have hdescent : baseEnd_1160435 < baseStart_1160435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160451 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 2, 4]
def baseStart_1160451 : Nat := 118140960795 + 1160451 * 2 ^ 59
def prefixEnd_1160451 : Nat := 4983230072969 + 3 ^ 40 * 1160451 * 2
def baseEnd_1160451 : Nat := 198623046330248154608563

theorem tailTrace_1160451 : CollatzResearch.WordTrace tailWord_1160451 prefixEnd_1160451 198623046330248154608563 := by
  unfold tailWord_1160451
  simp only [CollatzResearch.WordTrace]
  refine ⟨42325125118891691097257207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28216750079261127398171471 42325125118891691097257207)
  ·
    refine ⟨63487687678337536645885811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42325125118891691097257207 63487687678337536645885811)
    ·
      refine ⟨95231531517506304968828717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63487687678337536645885811 95231531517506304968828717)
      ·
        refine ⟨35711824319064864363310769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95231531517506304968828717 35711824319064864363310769)
        ·
          refine ⟨26783868239298648272483077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35711824319064864363310769 26783868239298648272483077)
          ·
            refine ⟨5021975294868496551090577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26783868239298648272483077 5021975294868496551090577)
            ·
              refine ⟨3766481471151372413317933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5021975294868496551090577 3766481471151372413317933)
              ·
                refine ⟨1412430551681764654994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766481471151372413317933 1412430551681764654994225)
                ·
                  refine ⟨1059322913761323491245669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412430551681764654994225 1059322913761323491245669)
                  ·
                    refine ⟨198623046330248154608563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1059322913761323491245669 198623046330248154608563)
                    ·
                      rfl

theorem cell23_1160451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 4].length) (baseStart_1160451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160451 prefixEnd_1160451 := by exact prefixLift 1160451
  have htrace : WordTrace (prefixWord ++ tailWord_1160451) baseStart_1160451 baseEnd_1160451 := by
    simpa [prefixWord, tailWord_1160451, baseEnd_1160451] using wordTrace_append hprefix tailTrace_1160451
  have hstable : (prefixWord ++ tailWord_1160451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160451).length < 2 ^ (prefixWord ++ tailWord_1160451).sum := by decide
  have hdescent : baseEnd_1160451 < baseStart_1160451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160502 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1160502 : Nat := 118140960795 + 1160502 * 2 ^ 59
def prefixEnd_1160502 : Nat := 4983230072969 + 3 ^ 40 * 1160502 * 2
def baseEnd_1160502 : Nat := 198631775501374588095985

theorem tailTrace_1160502 : CollatzResearch.WordTrace tailWord_1160502 prefixEnd_1160502 198631775501374588095985 := by
  unfold tailWord_1160502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645436577606682925460235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28217990161137951204909173 2645436577606682925460235)
  ·
    refine ⟨3968154866410024388190353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645436577606682925460235 3968154866410024388190353)
    ·
      refine ⟨2976116149807518291142765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3968154866410024388190353 2976116149807518291142765)
      ·
        refine ⟨1116043556177819359178537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2976116149807518291142765 1116043556177819359178537)
        ·
          refine ⟨837032667133364519383903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1116043556177819359178537 837032667133364519383903)
          ·
            refine ⟨1255549000700046779075855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837032667133364519383903 1255549000700046779075855)
            ·
              refine ⟨1883323501050070168613783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255549000700046779075855 1883323501050070168613783)
              ·
                refine ⟨2824985251575105252920675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883323501050070168613783 2824985251575105252920675)
                ·
                  refine ⟨4237477877362657879381013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824985251575105252920675 4237477877362657879381013)
                  ·
                    refine ⟨198631775501374588095985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4237477877362657879381013 198631775501374588095985)
                    ·
                      rfl

theorem cell23_1160502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1160502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160502 prefixEnd_1160502 := by exact prefixLift 1160502
  have htrace : WordTrace (prefixWord ++ tailWord_1160502) baseStart_1160502 baseEnd_1160502 := by
    simpa [prefixWord, tailWord_1160502, baseEnd_1160502] using wordTrace_append hprefix tailTrace_1160502
  have hstable : (prefixWord ++ tailWord_1160502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160502).length < 2 ^ (prefixWord ++ tailWord_1160502).sum := by decide
  have hdescent : baseEnd_1160502 < baseStart_1160502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160505 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1160505 : Nat := 118140960795 + 1160505 * 2 ^ 59
def prefixEnd_1160505 : Nat := 4983230072969 + 3 ^ 40 * 1160505 * 2
def baseEnd_1160505 : Nat := 595896866946087252550441

theorem tailTrace_1160505 : CollatzResearch.WordTrace tailWord_1160505 prefixEnd_1160505 595896866946087252550441 := by
  unfold tailWord_1160505
  simp only [CollatzResearch.WordTrace]
  refine ⟨42327094660696058319722969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28218063107130705546481979 42327094660696058319722969)
  ·
    refine ⟨31745320995522043739792227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42327094660696058319722969 31745320995522043739792227)
    ·
      refine ⟨47617981493283065609688341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31745320995522043739792227 47617981493283065609688341)
      ·
        refine ⟨2232092882497643700454141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47617981493283065609688341 2232092882497643700454141)
        ·
          refine ⟨837034830936616387670303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2232092882497643700454141 837034830936616387670303)
          ·
            refine ⟨1255552246404924581505455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837034830936616387670303 1255552246404924581505455)
            ·
              refine ⟨1883328369607386872258183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255552246404924581505455 1883328369607386872258183)
              ·
                refine ⟨2824992554411080308387275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883328369607386872258183 2824992554411080308387275)
                ·
                  refine ⟨4237488831616620462580913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824992554411080308387275 4237488831616620462580913)
                  ·
                    refine ⟨3178116623712465346935685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4237488831616620462580913 3178116623712465346935685)
                    ·
                      refine ⟨595896866946087252550441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3178116623712465346935685 595896866946087252550441)
                      ·
                        rfl

theorem cell23_1160505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1160505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160505 prefixEnd_1160505 := by exact prefixLift 1160505
  have htrace : WordTrace (prefixWord ++ tailWord_1160505) baseStart_1160505 baseEnd_1160505 := by
    simpa [prefixWord, tailWord_1160505, baseEnd_1160505] using wordTrace_append hprefix tailTrace_1160505
  have hstable : (prefixWord ++ tailWord_1160505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160505).length < 2 ^ (prefixWord ++ tailWord_1160505).sum := by decide
  have hdescent : baseEnd_1160505 < baseStart_1160505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160508 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_1160508 : Nat := 118140960795 + 1160508 * 2 ^ 59
def prefixEnd_1160508 : Nat := 4983230072969 + 3 ^ 40 * 1160508 * 2
def baseEnd_1160508 : Nat := 595898407388050740812927

theorem tailTrace_1160508 : CollatzResearch.WordTrace tailWord_1160508 prefixEnd_1160508 595898407388050740812927 := by
  unfold tailWord_1160508
  simp only [CollatzResearch.WordTrace]
  refine ⟨21163602039842594916041089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28218136053123459888054785 21163602039842594916041089)
  ·
    refine ⟨15872701529881946187030817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21163602039842594916041089 15872701529881946187030817)
    ·
      refine ⟨11904526147411459640273113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15872701529881946187030817 11904526147411459640273113)
      ·
        refine ⟨8928394610558594730204835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11904526147411459640273113 8928394610558594730204835)
        ·
          refine ⟨13392591915837892095307253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8928394610558594730204835 13392591915837892095307253)
          ·
            refine ⟨1255555492109802383935055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13392591915837892095307253 1255555492109802383935055)
            ·
              refine ⟨1883333238164703575902583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255555492109802383935055 1883333238164703575902583)
              ·
                refine ⟨2824999857247055363853875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883333238164703575902583 2824999857247055363853875)
                ·
                  refine ⟨4237499785870583045780813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824999857247055363853875 4237499785870583045780813)
                  ·
                    refine ⟨1589062419701468642167805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4237499785870583045780813 1589062419701468642167805)
                    ·
                      refine ⟨595898407388050740812927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1589062419701468642167805 595898407388050740812927)
                      ·
                        rfl

theorem cell23_1160508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_1160508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160508 prefixEnd_1160508 := by exact prefixLift 1160508
  have htrace : WordTrace (prefixWord ++ tailWord_1160508) baseStart_1160508 baseEnd_1160508 := by
    simpa [prefixWord, tailWord_1160508, baseEnd_1160508] using wordTrace_append hprefix tailTrace_1160508
  have hstable : (prefixWord ++ tailWord_1160508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160508).length < 2 ^ (prefixWord ++ tailWord_1160508).sum := by decide
  have hdescent : baseEnd_1160508 < baseStart_1160508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160531 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 4, 2]
def baseStart_1160531 : Nat := 118140960795 + 1160531 * 2 ^ 59
def prefixEnd_1160531 : Nat := 4983230072969 + 3 ^ 40 * 1160531 * 2
def baseEnd_1160531 : Nat := 595910217443104150825321

theorem tailTrace_1160531 : CollatzResearch.WordTrace tailWord_1160531 prefixEnd_1160531 595910217443104150825321 := by
  unfold tailWord_1160531
  simp only [CollatzResearch.WordTrace]
  refine ⟨42328042958601864760169447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28218695305734576506779631 42328042958601864760169447)
  ·
    refine ⟨63492064437902797140254171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42328042958601864760169447 63492064437902797140254171)
    ·
      refine ⟨95238096656854195710381257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63492064437902797140254171 95238096656854195710381257)
      ·
        refine ⟨71428572492640646782785943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95238096656854195710381257 71428572492640646782785943)
        ·
          refine ⟨107142858738960970174178915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71428572492640646782785943 107142858738960970174178915)
          ·
            refine ⟨160714288108441455261268373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107142858738960970174178915 160714288108441455261268373)
            ·
              refine ⟨7533482255083193215371955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160714288108441455261268373 7533482255083193215371955)
              ·
                refine ⟨11300223382624789823057933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7533482255083193215371955 11300223382624789823057933)
                ·
                  refine ⟨4237583768484296183646725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11300223382624789823057933 4237583768484296183646725)
                  ·
                    refine ⟨794546956590805534433761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4237583768484296183646725 794546956590805534433761)
                    ·
                      refine ⟨595910217443104150825321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794546956590805534433761 595910217443104150825321)
                      ·
                        rfl

theorem cell23_1160531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 4, 2].length) (baseStart_1160531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160531 prefixEnd_1160531 := by exact prefixLift 1160531
  have htrace : WordTrace (prefixWord ++ tailWord_1160531) baseStart_1160531 baseEnd_1160531 := by
    simpa [prefixWord, tailWord_1160531, baseEnd_1160531] using wordTrace_append hprefix tailTrace_1160531
  have hstable : (prefixWord ++ tailWord_1160531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160531).length < 2 ^ (prefixWord ++ tailWord_1160531).sum := by decide
  have hdescent : baseEnd_1160531 < baseStart_1160531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160601 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_1160601 : Nat := 118140960795 + 1160601 * 2 ^ 59
def prefixEnd_1160601 : Nat := 4983230072969 + 3 ^ 40 * 1160601 * 2
def baseEnd_1160601 : Nat := 198648720362972958983333

theorem tailTrace_1160601 : CollatzResearch.WordTrace tailWord_1160601 prefixEnd_1160601 198648720362972958983333 := by
  unfold tailWord_1160601
  simp only [CollatzResearch.WordTrace]
  refine ⟨42330596068348266715217657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28220397378898844476811771 42330596068348266715217657)
  ·
    refine ⟨31747947051261200036413243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42330596068348266715217657 31747947051261200036413243)
    ·
      refine ⟨47621920576891800054619865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31747947051261200036413243 47621920576891800054619865)
      ·
        refine ⟨35716440432668850040964899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47621920576891800054619865 35716440432668850040964899)
        ·
          refine ⟨53574660649003275061447349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35716440432668850040964899 53574660649003275061447349)
          ·
            refine ⟨5022624435844057037010689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53574660649003275061447349 5022624435844057037010689)
            ·
              refine ⟨3766968326883042777758017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022624435844057037010689 3766968326883042777758017)
              ·
                refine ⟨2825226245162282083318513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766968326883042777758017 2825226245162282083318513)
                ·
                  refine ⟨2118919683871711562488885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825226245162282083318513 2118919683871711562488885)
                  ·
                    refine ⟨198648720362972958983333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2118919683871711562488885 198648720362972958983333)
                    ·
                      rfl

theorem cell23_1160601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_1160601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160601 prefixEnd_1160601 := by exact prefixLift 1160601
  have htrace : WordTrace (prefixWord ++ tailWord_1160601) baseStart_1160601 baseEnd_1160601 := by
    simpa [prefixWord, tailWord_1160601, baseEnd_1160601] using wordTrace_append hprefix tailTrace_1160601
  have hstable : (prefixWord ++ tailWord_1160601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160601).length < 2 ^ (prefixWord ++ tailWord_1160601).sum := by decide
  have hdescent : baseEnd_1160601 < baseStart_1160601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160605 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 5]
def baseStart_1160605 : Nat := 118140960795 + 1160605 * 2 ^ 59
def prefixEnd_1160605 : Nat := 4983230072969 + 3 ^ 40 * 1160605 * 2
def baseEnd_1160605 : Nat := 66216468334615206811109

theorem tailTrace_1160605 : CollatzResearch.WordTrace tailWord_1160605 prefixEnd_1160605 66216468334615206811109 := by
  unfold tailWord_1160605
  simp only [CollatzResearch.WordTrace]
  refine ⟨42330741960333775398363269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28220494640222516932242179 42330741960333775398363269)
  ·
    refine ⟨7937014117562582887193113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42330741960333775398363269 7937014117562582887193113)
    ·
      refine ⟨5952760588171937165394835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7937014117562582887193113 5952760588171937165394835)
      ·
        refine ⟨8929140882257905748092253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952760588171937165394835 8929140882257905748092253)
        ·
          refine ⟨3348427830846714655534595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8929140882257905748092253 3348427830846714655534595)
          ·
            refine ⟨5022641746270071983301893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348427830846714655534595 5022641746270071983301893)
            ·
              refine ⟨941745327425638496869105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5022641746270071983301893 941745327425638496869105)
              ·
                refine ⟨706308995569228872651829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941745327425638496869105 706308995569228872651829)
                ·
                  refine ⟨66216468334615206811109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706308995569228872651829 66216468334615206811109)
                  ·
                    rfl

theorem cell23_1160605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_1160605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160605 prefixEnd_1160605 := by exact prefixLift 1160605
  have htrace : WordTrace (prefixWord ++ tailWord_1160605) baseStart_1160605 baseEnd_1160605 := by
    simpa [prefixWord, tailWord_1160605, baseEnd_1160605] using wordTrace_append hprefix tailTrace_1160605
  have hstable : (prefixWord ++ tailWord_1160605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160605).length < 2 ^ (prefixWord ++ tailWord_1160605).sum := by decide
  have hdescent : baseEnd_1160605 < baseStart_1160605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160638 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_1160638 : Nat := 118140960795 + 1160638 * 2 ^ 59
def prefixEnd_1160638 : Nat := 4983230072969 + 3 ^ 40 * 1160638 * 2
def baseEnd_1160638 : Nat := 595965159873135232187329

theorem tailTrace_1160638 : CollatzResearch.WordTrace tailWord_1160638 prefixEnd_1160638 595965159873135232187329 := by
  unfold tailWord_1160638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5291493196151777754289321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28221297046142814689543045 5291493196151777754289321)
  ·
    refine ⟨3968619897113833315716991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5291493196151777754289321 3968619897113833315716991)
    ·
      refine ⟨5952929845670749973575487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3968619897113833315716991 5952929845670749973575487)
      ·
        refine ⟨8929394768506124960363231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5952929845670749973575487 8929394768506124960363231)
        ·
          refine ⟨13394092152759187440544847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8929394768506124960363231 13394092152759187440544847)
          ·
            refine ⟨20091138229138781160817271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13394092152759187440544847 20091138229138781160817271)
            ·
              refine ⟨30136707343708171741225907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20091138229138781160817271 30136707343708171741225907)
              ·
                refine ⟨45205061015562257611838861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30136707343708171741225907 45205061015562257611838861)
                ·
                  refine ⟨16951897880835846604439573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45205061015562257611838861 16951897880835846604439573)
                  ·
                    refine ⟨794620213164180309583105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16951897880835846604439573 794620213164180309583105)
                    ·
                      refine ⟨595965159873135232187329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 794620213164180309583105 595965159873135232187329)
                      ·
                        rfl

theorem cell23_1160638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_1160638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1160638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1160638 prefixEnd_1160638 := by exact prefixLift 1160638
  have htrace : WordTrace (prefixWord ++ tailWord_1160638) baseStart_1160638 baseEnd_1160638 := by
    simpa [prefixWord, tailWord_1160638, baseEnd_1160638] using wordTrace_append hprefix tailTrace_1160638
  have hstable : (prefixWord ++ tailWord_1160638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160638).length < 2 ^ (prefixWord ++ tailWord_1160638).sum := by decide
  have hdescent : baseEnd_1160638 < baseStart_1160638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
