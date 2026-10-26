import V185TrunkScan21Chunk170

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2082766 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2082766 : Nat := 118140960795 + 2082766 * 2 ^ 59
def prefixEnd_2082766 : Nat := 4983230072969 + 3 ^ 40 * 2082766 * 2
def baseEnd_2082766 : Nat := 475315577263245956509573

theorem tailTrace_2082766 : CollatzResearch.WordTrace tailWord_2082766 prefixEnd_2082766 475315577263245956509573 := by
  unfold tailWord_2082766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495589596562745619817519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50643144515001309972360101 9495589596562745619817519)
  ·
    refine ⟨14243384394844118429726279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495589596562745619817519 14243384394844118429726279)
    ·
      refine ⟨21365076592266177644589419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14243384394844118429726279 21365076592266177644589419)
      ·
        refine ⟨32047614888399266466884129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21365076592266177644589419 32047614888399266466884129)
        ·
          refine ⟨24035711166299449850163097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32047614888399266466884129 24035711166299449850163097)
          ·
            refine ⟨18026783374724587387622323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24035711166299449850163097 18026783374724587387622323)
            ·
              refine ⟨27040175062086881081433485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18026783374724587387622323 27040175062086881081433485)
              ·
                refine ⟨10140065648282580405537557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27040175062086881081433485 10140065648282580405537557)
                ·
                  refine ⟨475315577263245956509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10140065648282580405537557 475315577263245956509573)
                  ·
                    rfl

theorem cell21_2082766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2082766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082766 prefixEnd_2082766 := by exact prefixLift 2082766
  have htrace : WordTrace (prefixWord ++ tailWord_2082766) baseStart_2082766 baseEnd_2082766 := by
    simpa [prefixWord, tailWord_2082766, baseEnd_2082766] using wordTrace_append hprefix tailTrace_2082766
  have hstable : (prefixWord ++ tailWord_2082766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082766).length < 2 ^ (prefixWord ++ tailWord_2082766).sum := by decide
  have hdescent : baseEnd_2082766 < baseStart_2082766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082783 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_2082783 : Nat := 118140960795 + 2082783 * 2 ^ 59
def prefixEnd_2082783 : Nat := 4983230072969 + 3 ^ 40 * 2082783 * 2
def baseEnd_2082783 : Nat := 475319456894857704726205

theorem tailTrace_2082783 : CollatzResearch.WordTrace tailWord_2082783 prefixEnd_2082783 475319456894857704726205 := by
  unfold tailWord_2082783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75965336813440376861909003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50643557875626917907939335 75965336813440376861909003)
  ·
    refine ⟨113948005220160565292863505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75965336813440376861909003 113948005220160565292863505)
    ·
      refine ⟨85461003915120423969647629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113948005220160565292863505 85461003915120423969647629)
      ·
        refine ⟨32047876468170158988617861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85461003915120423969647629 32047876468170158988617861)
        ·
          refine ⟨6008976837781904810365849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32047876468170158988617861 6008976837781904810365849)
          ·
            refine ⟨4506732628336428607774387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6008976837781904810365849 4506732628336428607774387)
            ·
              refine ⟨6760098942504642911661581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506732628336428607774387 6760098942504642911661581)
              ·
                refine ⟨2535037103439241091873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760098942504642911661581 2535037103439241091873093)
                ·
                  refine ⟨475319456894857704726205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535037103439241091873093 475319456894857704726205)
                  ·
                    rfl

theorem cell21_2082783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_2082783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082783 prefixEnd_2082783 := by exact prefixLift 2082783
  have htrace : WordTrace (prefixWord ++ tailWord_2082783) baseStart_2082783 baseEnd_2082783 := by
    simpa [prefixWord, tailWord_2082783, baseEnd_2082783] using wordTrace_append hprefix tailTrace_2082783
  have hstable : (prefixWord ++ tailWord_2082783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082783).length < 2 ^ (prefixWord ++ tailWord_2082783).sum := by decide
  have hdescent : baseEnd_2082783 < baseStart_2082783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082820 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2082820 : Nat := 118140960795 + 2082820 * 2 ^ 59
def prefixEnd_2082820 : Nat := 4983230072969 + 3 ^ 40 * 2082820 * 2
def baseEnd_2082820 : Nat := 475327900798953862609463

theorem tailTrace_2082820 : CollatzResearch.WordTrace tailWord_2082820 prefixEnd_2082820 475327900798953862609463 := by
  unfold tailWord_2082820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37983343157153166090502957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50644457542870888120670609 37983343157153166090502957)
  ·
    refine ⟨14243753683932437283938609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37983343157153166090502957 14243753683932437283938609)
    ·
      refine ⟨10682815262949327962953957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14243753683932437283938609 10682815262949327962953957)
      ·
        refine ⟨2003027861802998993053867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10682815262949327962953957 2003027861802998993053867)
        ·
          refine ⟨3004541792704498489580801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003027861802998993053867 3004541792704498489580801)
          ·
            refine ⟨2253406344528373867185601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004541792704498489580801 2253406344528373867185601)
            ·
              refine ⟨1690054758396280400389201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253406344528373867185601 1690054758396280400389201)
              ·
                refine ⟨1267541068797210300291901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690054758396280400389201 1267541068797210300291901)
                ·
                  refine ⟨475327900798953862609463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267541068797210300291901 475327900798953862609463)
                  ·
                    rfl

theorem cell21_2082820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2082820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082820 prefixEnd_2082820 := by exact prefixLift 2082820
  have htrace : WordTrace (prefixWord ++ tailWord_2082820) baseStart_2082820 baseEnd_2082820 := by
    simpa [prefixWord, tailWord_2082820, baseEnd_2082820] using wordTrace_append hprefix tailTrace_2082820
  have hstable : (prefixWord ++ tailWord_2082820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082820).length < 2 ^ (prefixWord ++ tailWord_2082820).sum := by decide
  have hdescent : baseEnd_2082820 < baseStart_2082820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082862 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2082862 : Nat := 118140960795 + 2082862 * 2 ^ 59
def prefixEnd_2082862 : Nat := 4983230072969 + 3 ^ 40 * 2082862 * 2
def baseEnd_2082862 : Nat := 475337485771171122909377

theorem tailTrace_2082862 : CollatzResearch.WordTrace tailWord_2082862 prefixEnd_2082862 475337485771171122909377 := by
  unfold tailWord_2082862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496027272519271669254355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50645478786769448902689893 9496027272519271669254355)
  ·
    refine ⟨14244040908778907503881533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9496027272519271669254355 14244040908778907503881533)
    ·
      refine ⟨5341515340792090313955575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14244040908778907503881533 5341515340792090313955575)
      ·
        refine ⟨8012273011188135470933363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341515340792090313955575 8012273011188135470933363)
        ·
          refine ⟨12018409516782203206400045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012273011188135470933363 12018409516782203206400045)
          ·
            refine ⟨4506903568793326202400017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12018409516782203206400045 4506903568793326202400017)
            ·
              refine ⟨3380177676594994651800013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506903568793326202400017 3380177676594994651800013)
              ·
                refine ⟨1267566628723122994425005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3380177676594994651800013 1267566628723122994425005)
                ·
                  refine ⟨475337485771171122909377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267566628723122994425005 475337485771171122909377)
                  ·
                    rfl

theorem cell21_2082862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2082862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082862 prefixEnd_2082862 := by exact prefixLift 2082862
  have htrace : WordTrace (prefixWord ++ tailWord_2082862) baseStart_2082862 baseEnd_2082862 := by
    simpa [prefixWord, tailWord_2082862, baseEnd_2082862] using wordTrace_append hprefix tailTrace_2082862
  have hstable : (prefixWord ++ tailWord_2082862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082862).length < 2 ^ (prefixWord ++ tailWord_2082862).sum := by decide
  have hdescent : baseEnd_2082862 < baseStart_2082862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082873 : List Nat := [1, 2, 1, 5, 3, 1, 8]
def baseStart_2082873 : Nat := 118140960795 + 2082873 * 2 ^ 59
def prefixEnd_2082873 : Nat := 4983230072969 + 3 ^ 40 * 2082873 * 2
def baseEnd_2082873 : Nat := 52815555124559727580669

theorem tailTrace_2082873 : CollatzResearch.WordTrace tailWord_2082873 prefixEnd_2082873 52815555124559727580669 := by
  unfold tailWord_2082873
  simp only [CollatzResearch.WordTrace]
  refine ⟨75968619383114322232685273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50645746255409548155123515 75968619383114322232685273)
  ·
    refine ⟨56976464537335741674513955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75968619383114322232685273 56976464537335741674513955)
    ·
      refine ⟨85464696806003612511770933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56976464537335741674513955 85464696806003612511770933)
      ·
        refine ⟨8012315325562838672978525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85464696806003612511770933 8012315325562838672978525)
        ·
          refine ⟨3004618247086064502366947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8012315325562838672978525 3004618247086064502366947)
          ·
            refine ⟨4506927370629096753550421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004618247086064502366947 4506927370629096753550421)
            ·
              refine ⟨52815555124559727580669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4506927370629096753550421 52815555124559727580669)
              ·
                rfl

theorem cell21_2082873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 8].length) (baseStart_2082873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082873 prefixEnd_2082873 := by exact prefixLift 2082873
  have htrace : WordTrace (prefixWord ++ tailWord_2082873) baseStart_2082873 baseEnd_2082873 := by
    simpa [prefixWord, tailWord_2082873, baseEnd_2082873] using wordTrace_append hprefix tailTrace_2082873
  have hstable : (prefixWord ++ tailWord_2082873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082873).length < 2 ^ (prefixWord ++ tailWord_2082873).sum := by decide
  have hdescent : baseEnd_2082873 < baseStart_2082873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082949 : List Nat := [1, 3, 1, 1, 5, 2, 2, 6]
def baseStart_2082949 : Nat := 118140960795 + 2082949 * 2 ^ 59
def prefixEnd_2082949 : Nat := 4983230072969 + 3 ^ 40 * 2082949 * 2
def baseEnd_2082949 : Nat := 158452446785492768319733

theorem tailTrace_2082949 : CollatzResearch.WordTrace tailWord_2082949 prefixEnd_2082949 158452446785492768319733 := by
  unfold tailWord_2082949
  simp only [CollatzResearch.WordTrace]
  refine ⟨75971391330838987212451901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50647594220559324808301267 75971391330838987212451901)
  ·
    refine ⟨28489271749064620204669463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75971391330838987212451901 28489271749064620204669463)
    ·
      refine ⟨42733907623596930307004195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28489271749064620204669463 42733907623596930307004195)
      ·
        refine ⟨64100861435395395460506293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42733907623596930307004195 64100861435395395460506293)
        ·
          refine ⟨6009455759568318324422465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64100861435395395460506293 6009455759568318324422465)
          ·
            refine ⟨4507091819676238743316849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6009455759568318324422465 4507091819676238743316849)
            ·
              refine ⟨3380318864757179057487637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507091819676238743316849 3380318864757179057487637)
              ·
                refine ⟨158452446785492768319733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3380318864757179057487637 158452446785492768319733)
                ·
                  rfl

theorem cell21_2082949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_2082949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082949 prefixEnd_2082949 := by exact prefixLift 2082949
  have htrace : WordTrace (prefixWord ++ tailWord_2082949) baseStart_2082949 baseEnd_2082949 := by
    simpa [prefixWord, tailWord_2082949, baseEnd_2082949] using wordTrace_append hprefix tailTrace_2082949
  have hstable : (prefixWord ++ tailWord_2082949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082949).length < 2 ^ (prefixWord ++ tailWord_2082949).sum := by decide
  have hdescent : baseEnd_2082949 < baseStart_2082949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2082952 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_2082952 : Nat := 118140960795 + 2082952 * 2 ^ 59
def prefixEnd_2082952 : Nat := 4983230072969 + 3 ^ 40 * 2082952 * 2
def baseEnd_2082952 : Nat := 475358024997350966409193

theorem tailTrace_2082952 : CollatzResearch.WordTrace tailWord_2082952 prefixEnd_2082952 475358024997350966409193 := by
  unfold tailWord_2082952
  simp only [CollatzResearch.WordTrace]
  refine ⟨37985750374914059362405555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50647667166552079149874073 37985750374914059362405555)
  ·
    refine ⟨56978625562371089043608333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37985750374914059362405555 56978625562371089043608333)
    ·
      refine ⟨21366984585889158391353125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56978625562371089043608333 21366984585889158391353125)
      ·
        refine ⟨4006309609854217198378711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21366984585889158391353125 4006309609854217198378711)
        ·
          refine ⟨6009464414781325797568067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006309609854217198378711 6009464414781325797568067)
          ·
            refine ⟨9014196622171988696352101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009464414781325797568067 9014196622171988696352101)
            ·
              refine ⟨1690161866657247880566019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9014196622171988696352101 1690161866657247880566019)
              ·
                refine ⟨2535242799985871820849029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690161866657247880566019 2535242799985871820849029)
                ·
                  refine ⟨475358024997350966409193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535242799985871820849029 475358024997350966409193)
                  ·
                    rfl

theorem cell21_2082952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_2082952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2082952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2082952 prefixEnd_2082952 := by exact prefixLift 2082952
  have htrace : WordTrace (prefixWord ++ tailWord_2082952) baseStart_2082952 baseEnd_2082952 := by
    simpa [prefixWord, tailWord_2082952, baseEnd_2082952] using wordTrace_append hprefix tailTrace_2082952
  have hstable : (prefixWord ++ tailWord_2082952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2082952).length < 2 ^ (prefixWord ++ tailWord_2082952).sum := by decide
  have hdescent : baseEnd_2082952 < baseStart_2082952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2082952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083084 : List Nat := [2, 2, 1, 2, 2, 2, 3, 7]
def baseStart_2083084 : Nat := 118140960795 + 2083084 * 2 ^ 59
def prefixEnd_2083084 : Nat := 4983230072969 + 3 ^ 40 * 2083084 * 2
def baseEnd_2083084 : Nat := 158462716398582690069641

theorem tailTrace_2083084 : CollatzResearch.WordTrace tailWord_2083084 prefixEnd_2083084 158462716398582690069641 := by
  unfold tailWord_2083084
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988157592674952634308153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50650876790233270179077537 37988157592674952634308153)
  ·
    refine ⟨28491118194506214475731115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37988157592674952634308153 28491118194506214475731115)
    ·
      refine ⟨42736677291759321713596673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28491118194506214475731115 42736677291759321713596673)
      ·
        refine ⟨32052507968819491285197505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42736677291759321713596673 32052507968819491285197505)
        ·
          refine ⟨24039380976614618463898129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32052507968819491285197505 24039380976614618463898129)
          ·
            refine ⟨18029535732460963847923597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24039380976614618463898129 18029535732460963847923597)
            ·
              refine ⟨6761075899672861442971349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18029535732460963847923597 6761075899672861442971349)
              ·
                refine ⟨158462716398582690069641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6761075899672861442971349 158462716398582690069641)
                ·
                  rfl

theorem cell21_2083084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_2083084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083084 prefixEnd_2083084 := by exact prefixLift 2083084
  have htrace : WordTrace (prefixWord ++ tailWord_2083084) baseStart_2083084 baseEnd_2083084 := by
    simpa [prefixWord, tailWord_2083084, baseEnd_2083084] using wordTrace_append hprefix tailTrace_2083084
  have hstable : (prefixWord ++ tailWord_2083084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083084).length < 2 ^ (prefixWord ++ tailWord_2083084).sum := by decide
  have hdescent : baseEnd_2083084 < baseStart_2083084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083121 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 4]
def baseStart_2083121 : Nat := 118140960795 + 2083121 * 2 ^ 59
def prefixEnd_2083121 : Nat := 4983230072969 + 3 ^ 40 * 2083121 * 2
def baseEnd_2083121 : Nat := 475396593099844228092181

theorem tailTrace_2083121 : CollatzResearch.WordTrace tailWord_2083121 prefixEnd_2083121 475396593099844228092181 := by
  unfold tailWord_2083121
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977664686215860587713217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50651776457477240391808811 75977664686215860587713217)
  ·
    refine ⟨56983248514661895440784913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75977664686215860587713217 56983248514661895440784913)
    ·
      refine ⟨42737436385996421580588685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56983248514661895440784913 42737436385996421580588685)
      ·
        refine ⟨16026538644748658092720757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42737436385996421580588685 16026538644748658092720757)
        ·
          refine ⟨1502487997945186696192571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16026538644748658092720757 1502487997945186696192571)
          ·
            refine ⟨2253731996917780044288857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502487997945186696192571 2253731996917780044288857)
            ·
              refine ⟨1690298997688335033216643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253731996917780044288857 1690298997688335033216643)
              ·
                refine ⟨2535448496532502549824965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690298997688335033216643 2535448496532502549824965)
                ·
                  refine ⟨475396593099844228092181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535448496532502549824965 475396593099844228092181)
                  ·
                    rfl

theorem cell21_2083121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_2083121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083121 prefixEnd_2083121 := by exact prefixLift 2083121
  have htrace : WordTrace (prefixWord ++ tailWord_2083121) baseStart_2083121 baseEnd_2083121 := by
    simpa [prefixWord, tailWord_2083121, baseEnd_2083121] using wordTrace_append hprefix tailTrace_2083121
  have hstable : (prefixWord ++ tailWord_2083121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083121).length < 2 ^ (prefixWord ++ tailWord_2083121).sum := by decide
  have hdescent : baseEnd_2083121 < baseStart_2083121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083205 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_2083205 : Nat := 118140960795 + 2083205 * 2 ^ 59
def prefixEnd_2083205 : Nat := 4983230072969 + 3 ^ 40 * 2083205 * 2
def baseEnd_2083205 : Nat := 475415763044278748692009

theorem tailTrace_2083205 : CollatzResearch.WordTrace tailWord_2083205 prefixEnd_2083205 475415763044278748692009 := by
  unfold tailWord_2083205
  simp only [CollatzResearch.WordTrace]
  refine ⟨75980728417911542933771069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50653818945274361955847379 75980728417911542933771069)
  ·
    refine ⟨28492773156716828600164151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75980728417911542933771069 28492773156716828600164151)
    ·
      refine ⟨42739159735075242900246227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28492773156716828600164151 42739159735075242900246227)
      ·
        refine ⟨64108739602612864350369341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42739159735075242900246227 64108739602612864350369341)
        ·
          refine ⟨24040777350979824131388503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64108739602612864350369341 24040777350979824131388503)
          ·
            refine ⟨36061166026469736197082755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24040777350979824131388503 36061166026469736197082755)
            ·
              refine ⟨54091749039704604295624133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36061166026469736197082755 54091749039704604295624133)
              ·
                refine ⟨10142202944944613305429525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54091749039704604295624133 10142202944944613305429525)
                ·
                  refine ⟨475415763044278748692009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10142202944944613305429525 475415763044278748692009)
                  ·
                    rfl

theorem cell21_2083205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_2083205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083205 prefixEnd_2083205 := by exact prefixLift 2083205
  have htrace : WordTrace (prefixWord ++ tailWord_2083205) baseStart_2083205 baseEnd_2083205 := by
    simpa [prefixWord, tailWord_2083205, baseEnd_2083205] using wordTrace_append hprefix tailTrace_2083205
  have hstable : (prefixWord ++ tailWord_2083205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083205).length < 2 ^ (prefixWord ++ tailWord_2083205).sum := by decide
  have hdescent : baseEnd_2083205 < baseStart_2083205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083253 : List Nat := [1, 3, 3, 2, 3, 1, 1, 7]
def baseStart_2083253 : Nat := 118140960795 + 2083253 * 2 ^ 59
def prefixEnd_2083253 : Nat := 4983230072969 + 3 ^ 40 * 2083253 * 2
def baseEnd_2083253 : Nat := 158475572432747110630637

theorem tailTrace_2083253 : CollatzResearch.WordTrace tailWord_2083253 prefixEnd_2083253 158475572432747110630637 := by
  unfold tailWord_2083253
  simp only [CollatzResearch.WordTrace]
  refine ⟨75982479121737647131518413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50654986081158431421012275 75982479121737647131518413)
  ·
    refine ⟨28493429670651617674319405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75982479121737647131518413 28493429670651617674319405)
    ·
      refine ⟨10685036126494356627869777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28493429670651617674319405 10685036126494356627869777)
      ·
        refine ⟨8013777094870767470902333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10685036126494356627869777 8013777094870767470902333)
        ·
          refine ⟨3005166410576537801588375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8013777094870767470902333 3005166410576537801588375)
          ·
            refine ⟨4507749615864806702382563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005166410576537801588375 4507749615864806702382563)
            ·
              refine ⟨6761624423797210053573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507749615864806702382563 6761624423797210053573845)
              ·
                refine ⟨158475572432747110630637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6761624423797210053573845 158475572432747110630637)
                ·
                  rfl

theorem cell21_2083253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_2083253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083253 prefixEnd_2083253 := by exact prefixLift 2083253
  have htrace : WordTrace (prefixWord ++ tailWord_2083253) baseStart_2083253 baseEnd_2083253 := by
    simpa [prefixWord, tailWord_2083253, baseEnd_2083253] using wordTrace_append hprefix tailTrace_2083253
  have hstable : (prefixWord ++ tailWord_2083253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083253).length < 2 ^ (prefixWord ++ tailWord_2083253).sum := by decide
  have hdescent : baseEnd_2083253 < baseStart_2083253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083284 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2083284 : Nat := 118140960795 + 2083284 * 2 ^ 59
def prefixEnd_2083284 : Nat := 4983230072969 + 3 ^ 40 * 2083284 * 2
def baseEnd_2083284 : Nat := 475433791920592166875181

theorem tailTrace_2083284 : CollatzResearch.WordTrace tailWord_2083284 prefixEnd_2083284 475433791920592166875181 := by
  unfold tailWord_2083284
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991804892312669712948453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50655739856416892950597937 37991804892312669712948453)
  ·
    refine ⟨7123463417308625571177835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37991804892312669712948453 7123463417308625571177835)
    ·
      refine ⟨10685195125962938356766753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123463417308625571177835 10685195125962938356766753)
      ·
        refine ⟨8013896344472203767575065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10685195125962938356766753 8013896344472203767575065)
        ·
          refine ⟨6010422258354152825681299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013896344472203767575065 6010422258354152825681299)
          ·
            refine ⟨9015633387531229238521949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010422258354152825681299 9015633387531229238521949)
            ·
              refine ⟨3380862520324210964445731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9015633387531229238521949 3380862520324210964445731)
              ·
                refine ⟨5071293780486316446668597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380862520324210964445731 5071293780486316446668597)
                ·
                  refine ⟨475433791920592166875181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071293780486316446668597 475433791920592166875181)
                  ·
                    rfl

theorem cell21_2083284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2083284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083284 prefixEnd_2083284 := by exact prefixLift 2083284
  have htrace : WordTrace (prefixWord ++ tailWord_2083284) baseStart_2083284 baseEnd_2083284 := by
    simpa [prefixWord, tailWord_2083284, baseEnd_2083284] using wordTrace_append hprefix tailTrace_2083284
  have hstable : (prefixWord ++ tailWord_2083284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083284).length < 2 ^ (prefixWord ++ tailWord_2083284).sum := by decide
  have hdescent : baseEnd_2083284 < baseStart_2083284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083335 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 3]
def baseStart_2083335 : Nat := 118140960795 + 2083335 * 2 ^ 59
def prefixEnd_2083335 : Nat := 4983230072969 + 3 ^ 40 * 2083335 * 2
def baseEnd_2083335 : Nat := 475445430815427411525077

theorem tailTrace_2083335 : CollatzResearch.WordTrace tailWord_2083335 prefixEnd_2083335 475445430815427411525077 := by
  unfold tailWord_2083335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75985469907440575136003459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50656979938293716757335639 75985469907440575136003459)
  ·
    refine ⟨113978204861160862704005189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75985469907440575136003459 113978204861160862704005189)
    ·
      refine ⟨21370913411467661757000973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113978204861160862704005189 21370913411467661757000973)
      ·
        refine ⟨8014092529300373158875365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21370913411467661757000973 8014092529300373158875365)
        ·
          refine ⟨1502642349243819967289131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8014092529300373158875365 1502642349243819967289131)
          ·
            refine ⟨2253963523865729950933697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502642349243819967289131 2253963523865729950933697)
            ·
              refine ⟨1690472642899297463200273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2253963523865729950933697 1690472642899297463200273)
              ·
                refine ⟨1267854482174473097400205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690472642899297463200273 1267854482174473097400205)
                ·
                  refine ⟨475445430815427411525077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267854482174473097400205 475445430815427411525077)
                  ·
                    rfl

theorem cell21_2083335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 3].length) (baseStart_2083335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083335 prefixEnd_2083335 := by exact prefixLift 2083335
  have htrace : WordTrace (prefixWord ++ tailWord_2083335) baseStart_2083335 baseEnd_2083335 := by
    simpa [prefixWord, tailWord_2083335, baseEnd_2083335] using wordTrace_append hprefix tailTrace_2083335
  have hstable : (prefixWord ++ tailWord_2083335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083335).length < 2 ^ (prefixWord ++ tailWord_2083335).sum := by decide
  have hdescent : baseEnd_2083335 < baseStart_2083335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083360 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_2083360 : Nat := 118140960795 + 2083360 * 2 ^ 59
def prefixEnd_2083360 : Nat := 4983230072969 + 3 ^ 40 * 2083360 * 2
def baseEnd_2083360 : Nat := 475451136156032923608359

theorem tailTrace_2083360 : CollatzResearch.WordTrace tailWord_2083360 prefixEnd_2083360 475451136156032923608359 := by
  unfold tailWord_2083360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993190866175002202831767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50657587821566669603775689 37993190866175002202831767)
  ·
    refine ⟨56989786299262503304247651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37993190866175002202831767 56989786299262503304247651)
    ·
      refine ⟨85484679448893754956371477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56989786299262503304247651 85484679448893754956371477)
      ·
        refine ⟨4007094349166894763579913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85484679448893754956371477 4007094349166894763579913)
        ·
          refine ⟨3005320761875171072684935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007094349166894763579913 3005320761875171072684935)
          ·
            refine ⟨4507981142812756609027403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005320761875171072684935 4507981142812756609027403)
            ·
              refine ⟨6761971714219134913541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507981142812756609027403 6761971714219134913541105)
              ·
                refine ⟨5071478785664351185155829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761971714219134913541105 5071478785664351185155829)
                ·
                  refine ⟨475451136156032923608359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071478785664351185155829 475451136156032923608359)
                  ·
                    rfl

theorem cell21_2083360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_2083360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083360 prefixEnd_2083360 := by exact prefixLift 2083360
  have htrace : WordTrace (prefixWord ++ tailWord_2083360) baseStart_2083360 baseEnd_2083360 := by
    simpa [prefixWord, tailWord_2083360, baseEnd_2083360] using wordTrace_append hprefix tailTrace_2083360
  have hstable : (prefixWord ++ tailWord_2083360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083360).length < 2 ^ (prefixWord ++ tailWord_2083360).sum := by decide
  have hdescent : baseEnd_2083360 < baseStart_2083360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083371 : List Nat := [1, 1, 1, 1, 2, 1, 3, 11]
def baseStart_2083371 : Nat := 118140960795 + 2083371 * 2 ^ 59
def prefixEnd_2083371 : Nat := 4983230072969 + 3 ^ 40 * 2083371 * 2
def baseEnd_2083371 : Nat := 158484548835299782975001

theorem tailTrace_2083371 : CollatzResearch.WordTrace tailWord_2083371 prefixEnd_2083371 158484548835299782975001 := by
  unfold tailWord_2083371
  simp only [CollatzResearch.WordTrace]
  refine ⟨75986782935310153284313967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50657855290206768856209311 75986782935310153284313967)
  ·
    refine ⟨113980174402965229926470951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75986782935310153284313967 113980174402965229926470951)
    ·
      refine ⟨170970261604447844889706427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113980174402965229926470951 170970261604447844889706427)
      ·
        refine ⟨256455392406671767334559641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170970261604447844889706427 256455392406671767334559641)
        ·
          refine ⟨192341544305003825500919731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256455392406671767334559641 192341544305003825500919731)
          ·
            refine ⟨288512316457505738251379597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192341544305003825500919731 288512316457505738251379597)
            ·
              refine ⟨108192118671564651844267349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288512316457505738251379597 108192118671564651844267349)
              ·
                refine ⟨158484548835299782975001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108192118671564651844267349 158484548835299782975001)
                ·
                  rfl

theorem cell21_2083371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_2083371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083371 prefixEnd_2083371 := by exact prefixLift 2083371
  have htrace : WordTrace (prefixWord ++ tailWord_2083371) baseStart_2083371 baseEnd_2083371 := by
    simpa [prefixWord, tailWord_2083371, baseEnd_2083371] using wordTrace_append hprefix tailTrace_2083371
  have hstable : (prefixWord ++ tailWord_2083371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083371).length < 2 ^ (prefixWord ++ tailWord_2083371).sum := by decide
  have hdescent : baseEnd_2083371 < baseStart_2083371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083388 : List Nat := [2, 2, 2, 2, 3, 2, 8]
def baseStart_2083388 : Nat := 118140960795 + 2083388 * 2 ^ 59
def prefixEnd_2083388 : Nat := 4983230072969 + 3 ^ 40 * 2083388 * 2
def baseEnd_2083388 : Nat := 52828614015279010793515

theorem tailTrace_2083388 : CollatzResearch.WordTrace tailWord_2083388 prefixEnd_2083388 52828614015279010793515 := by
  unfold tailWord_2083388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993701488124282593841409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50658268650832376791788545 37993701488124282593841409)
  ·
    refine ⟨28495276116093211945381057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37993701488124282593841409 28495276116093211945381057)
    ·
      refine ⟨21371457087069908959035793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28495276116093211945381057 21371457087069908959035793)
      ·
        refine ⟨16028592815302431719276845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21371457087069908959035793 16028592815302431719276845)
        ·
          refine ⟨6010722305738411894728817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16028592815302431719276845 6010722305738411894728817)
          ·
            refine ⟨4508041729303808921046613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010722305738411894728817 4508041729303808921046613)
            ·
              refine ⟨52828614015279010793515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4508041729303808921046613 52828614015279010793515)
              ·
                rfl

theorem cell21_2083388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 8].length) (baseStart_2083388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083388 prefixEnd_2083388 := by exact prefixLift 2083388
  have htrace : WordTrace (prefixWord ++ tailWord_2083388) baseStart_2083388 baseEnd_2083388 := by
    simpa [prefixWord, tailWord_2083388, baseEnd_2083388] using wordTrace_append hprefix tailTrace_2083388
  have hstable : (prefixWord ++ tailWord_2083388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083388).length < 2 ^ (prefixWord ++ tailWord_2083388).sum := by decide
  have hdescent : baseEnd_2083388 < baseStart_2083388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083436 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_2083436 : Nat := 118140960795 + 2083436 * 2 ^ 59
def prefixEnd_2083436 : Nat := 4983230072969 + 3 ^ 40 * 2083436 * 2
def baseEnd_2083436 : Nat := 475468480391473680341537

theorem tailTrace_2083436 : CollatzResearch.WordTrace tailWord_2083436 prefixEnd_2083436 475468480391473680341537 := by
  unfold tailWord_2083436
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994576840037334692715081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50659435786716446256953441 37994576840037334692715081)
  ·
    refine ⟨28495932630028001019536311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37994576840037334692715081 28495932630028001019536311)
    ·
      refine ⟨42743898945042001529304467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28495932630028001019536311 42743898945042001529304467)
      ·
        refine ⟨64115848417563002293956701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42743898945042001529304467 64115848417563002293956701)
        ·
          refine ⟨24043443156586125860233763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64115848417563002293956701 24043443156586125860233763)
          ·
            refine ⟨36065164734879188790350645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24043443156586125860233763 36065164734879188790350645)
            ·
              refine ⟨3381109193894923949095373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36065164734879188790350645 3381109193894923949095373)
              ·
                refine ⟨1267915947710596480910765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381109193894923949095373 1267915947710596480910765)
                ·
                  refine ⟨475468480391473680341537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267915947710596480910765 475468480391473680341537)
                  ·
                    rfl

theorem cell21_2083436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_2083436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083436 prefixEnd_2083436 := by exact prefixLift 2083436
  have htrace : WordTrace (prefixWord ++ tailWord_2083436) baseStart_2083436 baseEnd_2083436 := by
    simpa [prefixWord, tailWord_2083436, baseEnd_2083436] using wordTrace_append hprefix tailTrace_2083436
  have hstable : (prefixWord ++ tailWord_2083436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083436).length < 2 ^ (prefixWord ++ tailWord_2083436).sum := by decide
  have hdescent : baseEnd_2083436 < baseStart_2083436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083447 : List Nat := [1, 1, 3, 1, 1, 3, 11]
def baseStart_2083447 : Nat := 118140960795 + 2083447 * 2 ^ 59
def prefixEnd_2083447 : Nat := 4983230072969 + 3 ^ 40 * 2083447 * 2
def baseEnd_2083447 : Nat := 52830110082371122850909

theorem tailTrace_2083447 : CollatzResearch.WordTrace tailWord_2083447 prefixEnd_2083447 52830110082371122850909 := by
  unfold tailWord_2083447
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989554883034818264080595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50659703255356545509387063 75989554883034818264080595)
  ·
    refine ⟨113984332324552227396120893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75989554883034818264080595 113984332324552227396120893)
    ·
      refine ⟨42744124621707085273545335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113984332324552227396120893 42744124621707085273545335)
      ·
        refine ⟨64116186932560627910318003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42744124621707085273545335 64116186932560627910318003)
        ·
          refine ⟨96174280398840941865477005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64116186932560627910318003 96174280398840941865477005)
          ·
            refine ⟨36065355149565353199553877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96174280398840941865477005 36065355149565353199553877)
            ·
              refine ⟨52830110082371122850909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36065355149565353199553877 52830110082371122850909)
              ·
                rfl

theorem cell21_2083447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_2083447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083447 prefixEnd_2083447 := by exact prefixLift 2083447
  have htrace : WordTrace (prefixWord ++ tailWord_2083447) baseStart_2083447 baseEnd_2083447 := by
    simpa [prefixWord, tailWord_2083447, baseEnd_2083447] using wordTrace_append hprefix tailTrace_2083447
  have hstable : (prefixWord ++ tailWord_2083447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083447).length < 2 ^ (prefixWord ++ tailWord_2083447).sum := by decide
  have hdescent : baseEnd_2083447 < baseStart_2083447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083453 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2083453 : Nat := 118140960795 + 2083453 * 2 ^ 59
def prefixEnd_2083453 : Nat := 4983230072969 + 3 ^ 40 * 2083453 * 2
def baseEnd_2083453 : Nat := 475472360023085428558169

theorem tailTrace_2083453 : CollatzResearch.WordTrace tailWord_2083453 prefixEnd_2083453 475472360023085428558169 := by
  unfold tailWord_2083453
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989773721013081288799013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50659849147342054192532675 75989773721013081288799013)
  ·
    refine ⟨14248082572689952741649815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75989773721013081288799013 14248082572689952741649815)
    ·
      refine ⟨21372123859034929112474723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14248082572689952741649815 21372123859034929112474723)
      ·
        refine ⟨32058185788552393668712085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21372123859034929112474723 32058185788552393668712085)
        ·
          refine ⟨1502727458838393453220879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32058185788552393668712085 1502727458838393453220879)
          ·
            refine ⟨2254091188257590179831319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502727458838393453220879 2254091188257590179831319)
            ·
              refine ⟨3381136782386385269746979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254091188257590179831319 3381136782386385269746979)
              ·
                refine ⟨5071705173579577904620469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381136782386385269746979 5071705173579577904620469)
                ·
                  refine ⟨475472360023085428558169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071705173579577904620469 475472360023085428558169)
                  ·
                    rfl

theorem cell21_2083453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2083453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083453 prefixEnd_2083453 := by exact prefixLift 2083453
  have htrace : WordTrace (prefixWord ++ tailWord_2083453) baseStart_2083453 baseEnd_2083453 := by
    simpa [prefixWord, tailWord_2083453, baseEnd_2083453] using wordTrace_append hprefix tailTrace_2083453
  have hstable : (prefixWord ++ tailWord_2083453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083453).length < 2 ^ (prefixWord ++ tailWord_2083453).sum := by decide
  have hdescent : baseEnd_2083453 < baseStart_2083453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083498 : List Nat := [3, 1, 5, 2, 2, 8]
def baseStart_2083498 : Nat := 118140960795 + 2083498 * 2 ^ 59
def prefixEnd_2083498 : Nat := 4983230072969 + 3 ^ 40 * 2083498 * 2
def baseEnd_2083498 : Nat := 17610467764302790752151

theorem tailTrace_2083498 : CollatzResearch.WordTrace tailWord_2083498 prefixEnd_2083498 17610467764302790752151 := by
  unfold tailWord_2083498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997853751462513493546787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50660943337233369316124765 18997853751462513493546787)
  ·
    refine ⟨28496780627193770240320181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997853751462513493546787 28496780627193770240320181)
    ·
      refine ⟨2671573183799415960030017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28496780627193770240320181 2671573183799415960030017)
      ·
        refine ⟨2003679887849561970022513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2671573183799415960030017 2003679887849561970022513)
        ·
          refine ⟨1502759915887171477516885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2003679887849561970022513 1502759915887171477516885)
          ·
            refine ⟨17610467764302790752151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1502759915887171477516885 17610467764302790752151)
            ·
              rfl

theorem cell21_2083498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 8].length) (baseStart_2083498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083498 prefixEnd_2083498 := by exact prefixLift 2083498
  have htrace : WordTrace (prefixWord ++ tailWord_2083498) baseStart_2083498 baseEnd_2083498 := by
    simpa [prefixWord, tailWord_2083498, baseEnd_2083498] using wordTrace_append hprefix tailTrace_2083498
  have hstable : (prefixWord ++ tailWord_2083498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083498).length < 2 ^ (prefixWord ++ tailWord_2083498).sum := by decide
  have hdescent : baseEnd_2083498 < baseStart_2083498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083560 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_2083560 : Nat := 118140960795 + 2083560 * 2 ^ 59
def prefixEnd_2083560 : Nat := 4983230072969 + 3 ^ 40 * 2083560 * 2
def baseEnd_2083560 : Nat := 475496778880877020274617

theorem tailTrace_2083560 : CollatzResearch.WordTrace tailWord_2083560 prefixEnd_2083560 475496778880877020274617 := by
  unfold tailWord_2083560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996838165812719281472067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50662450887750292375296089 37996838165812719281472067)
  ·
    refine ⟨56995257248719078922208101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37996838165812719281472067 56995257248719078922208101)
    ·
      refine ⟨10686610734134827297914019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56995257248719078922208101 10686610734134827297914019)
      ·
        refine ⟨16029916101202240946871029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686610734134827297914019 16029916101202240946871029)
        ·
          refine ⟨1502804634487710088769159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16029916101202240946871029 1502804634487710088769159)
          ·
            refine ⟨2254206951731565133153739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502804634487710088769159 2254206951731565133153739)
            ·
              refine ⟨3381310427597347699730609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254206951731565133153739 3381310427597347699730609)
              ·
                refine ⟨2535982820698010774797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381310427597347699730609 2535982820698010774797957)
                ·
                  refine ⟨475496778880877020274617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535982820698010774797957 475496778880877020274617)
                  ·
                    rfl

theorem cell21_2083560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_2083560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083560 prefixEnd_2083560 := by exact prefixLift 2083560
  have htrace : WordTrace (prefixWord ++ tailWord_2083560) baseStart_2083560 baseEnd_2083560 := by
    simpa [prefixWord, tailWord_2083560, baseEnd_2083560] using wordTrace_append hprefix tailTrace_2083560
  have hstable : (prefixWord ++ tailWord_2083560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083560).length < 2 ^ (prefixWord ++ tailWord_2083560).sum := by decide
  have hdescent : baseEnd_2083560 < baseStart_2083560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083599 : List Nat := [1, 1, 2, 1, 1, 1, 7, 7]
def baseStart_2083599 : Nat := 118140960795 + 2083599 * 2 ^ 59
def prefixEnd_2083599 : Nat := 4983230072969 + 3 ^ 40 * 2083599 * 2
def baseEnd_2083599 : Nat := 158501893070740539708179

theorem tailTrace_2083599 : CollatzResearch.WordTrace tailWord_2083599 prefixEnd_2083599 158501893070740539708179 := by
  unfold tailWord_2083599
  simp only [CollatzResearch.WordTrace]
  refine ⟨75995098778484148223613851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50663399185656098815742567 75995098778484148223613851)
  ·
    refine ⟨113992648167726222335420777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75995098778484148223613851 113992648167726222335420777)
    ·
      refine ⟨85494486125794666751565583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113992648167726222335420777 85494486125794666751565583)
      ·
        refine ⟨128241729188692000127348375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85494486125794666751565583 128241729188692000127348375)
        ·
          refine ⟨192362593783038000191022563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128241729188692000127348375 192362593783038000191022563)
          ·
            refine ⟨288543890674557000286533845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192362593783038000191022563 288543890674557000286533845)
            ·
              refine ⟨6762747437684929694215637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 288543890674557000286533845 6762747437684929694215637)
              ·
                refine ⟨158501893070740539708179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6762747437684929694215637 158501893070740539708179)
                ·
                  rfl

theorem cell21_2083599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_2083599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083599 prefixEnd_2083599 := by exact prefixLift 2083599
  have htrace : WordTrace (prefixWord ++ tailWord_2083599) baseStart_2083599 baseEnd_2083599 := by
    simpa [prefixWord, tailWord_2083599, baseEnd_2083599] using wordTrace_append hprefix tailTrace_2083599
  have hstable : (prefixWord ++ tailWord_2083599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083599).length < 2 ^ (prefixWord ++ tailWord_2083599).sum := by decide
  have hdescent : baseEnd_2083599 < baseStart_2083599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083616 : List Nat := [2, 1, 1, 5, 1, 4, 7]
def baseStart_2083616 : Nat := 118140960795 + 2083616 * 2 ^ 59
def prefixEnd_2083616 : Nat := 4983230072969 + 3 ^ 40 * 2083616 * 2
def baseEnd_2083616 : Nat := 52834395427092596371241

theorem tailTrace_2083616 : CollatzResearch.WordTrace tailWord_2083616 prefixEnd_2083616 52834395427092596371241 := by
  unfold tailWord_2083616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997859409711280063491351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50663812546281706751321801 37997859409711280063491351)
  ·
    refine ⟨56996789114566920095237027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37997859409711280063491351 56996789114566920095237027)
    ·
      refine ⟨85495183671850380142855541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56996789114566920095237027 85495183671850380142855541)
      ·
        refine ⟨8015173469235973138392707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85495183671850380142855541 8015173469235973138392707)
        ·
          refine ⟨12022760203853959707589061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015173469235973138392707 12022760203853959707589061)
          ·
            refine ⟨2254267538222617445172949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12022760203853959707589061 2254267538222617445172949)
            ·
              refine ⟨52834395427092596371241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2254267538222617445172949 52834395427092596371241)
              ·
                rfl

theorem cell21_2083616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 7].length) (baseStart_2083616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083616 prefixEnd_2083616 := by exact prefixLift 2083616
  have htrace : WordTrace (prefixWord ++ tailWord_2083616) baseStart_2083616 baseEnd_2083616 := by
    simpa [prefixWord, tailWord_2083616, baseEnd_2083616] using wordTrace_append hprefix tailTrace_2083616
  have hstable : (prefixWord ++ tailWord_2083616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083616).length < 2 ^ (prefixWord ++ tailWord_2083616).sum := by decide
  have hdescent : baseEnd_2083616 < baseStart_2083616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083723 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 3]
def baseStart_2083723 : Nat := 118140960795 + 2083723 * 2 ^ 59
def prefixEnd_2083723 : Nat := 4983230072969 + 3 ^ 40 * 2083723 * 2
def baseEnd_2083723 : Nat := 475533977701624959057617

theorem tailTrace_2083723 : CollatzResearch.WordTrace tailWord_2083723 prefixEnd_2083723 475533977701624959057617 := by
  unfold tailWord_2083723
  simp only [CollatzResearch.WordTrace]
  refine ⟨75999621430034917401127823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50666414286689944934085215 75999621430034917401127823)
  ·
    refine ⟨113999432145052376101691735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75999621430034917401127823 113999432145052376101691735)
    ·
      refine ⟨170999148217578564152537603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113999432145052376101691735 170999148217578564152537603)
      ·
        refine ⟨256498722326367846228806405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170999148217578564152537603 256498722326367846228806405)
        ·
          refine ⟨48093510436193971167901201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256498722326367846228806405 48093510436193971167901201)
          ·
            refine ⟨36070132827145478375925901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48093510436193971167901201 36070132827145478375925901)
            ·
              refine ⟨13526299810179554390972213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36070132827145478375925901 13526299810179554390972213)
              ·
                refine ⟨1268090607204333224153645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13526299810179554390972213 1268090607204333224153645)
                ·
                  refine ⟨475533977701624959057617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268090607204333224153645 475533977701624959057617)
                  ·
                    rfl

theorem cell21_2083723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 3].length) (baseStart_2083723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083723 prefixEnd_2083723 := by exact prefixLift 2083723
  have htrace : WordTrace (prefixWord ++ tailWord_2083723) baseStart_2083723 baseEnd_2083723 := by
    simpa [prefixWord, tailWord_2083723, baseEnd_2083723] using wordTrace_append hprefix tailTrace_2083723
  have hstable : (prefixWord ++ tailWord_2083723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083723).length < 2 ^ (prefixWord ++ tailWord_2083723).sum := by decide
  have hdescent : baseEnd_2083723 < baseStart_2083723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083740 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2083740 : Nat := 118140960795 + 2083740 * 2 ^ 59
def prefixEnd_2083740 : Nat := 4983230072969 + 3 ^ 40 * 2083740 * 2
def baseEnd_2083740 : Nat := 475537857333236707274249

theorem tailTrace_2083740 : CollatzResearch.WordTrace tailWord_2083740 prefixEnd_2083740 475537857333236707274249 := by
  unfold tailWord_2083740
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000120735486664652248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50666827647315552869664449 38000120735486664652248337)
  ·
    refine ⟨28500090551614998489186253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38000120735486664652248337 28500090551614998489186253)
    ·
      refine ⟨10687533956855624433444845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28500090551614998489186253 10687533956855624433444845)
      ·
        refine ⟨4007825233820859162541817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10687533956855624433444845 4007825233820859162541817)
        ·
          refine ⟨3005868925365644371906363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007825233820859162541817 3005868925365644371906363)
          ·
            refine ⟨4508803388048466557859545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005868925365644371906363 4508803388048466557859545)
            ·
              refine ⟨3381602541036349918394659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508803388048466557859545 3381602541036349918394659)
              ·
                refine ⟨5072403811554524877591989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381602541036349918394659 5072403811554524877591989)
                ·
                  refine ⟨475537857333236707274249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5072403811554524877591989 475537857333236707274249)
                  ·
                    rfl

theorem cell21_2083740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2083740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083740 prefixEnd_2083740 := by exact prefixLift 2083740
  have htrace : WordTrace (prefixWord ++ tailWord_2083740) baseStart_2083740 baseEnd_2083740 := by
    simpa [prefixWord, tailWord_2083740, baseEnd_2083740] using wordTrace_append hprefix tailTrace_2083740
  have hstable : (prefixWord ++ tailWord_2083740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083740).length < 2 ^ (prefixWord ++ tailWord_2083740).sum := by decide
  have hdescent : baseEnd_2083740 < baseStart_2083740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083768 : List Nat := [2, 1, 2, 1, 2, 4, 4, 5]
def baseStart_2083768 : Nat := 118140960795 + 2083768 * 2 ^ 59
def prefixEnd_2083768 : Nat := 4983230072969 + 3 ^ 40 * 2083768 * 2
def baseEnd_2083768 : Nat := 158514749104904960269175

theorem tailTrace_2083768 : CollatzResearch.WordTrace tailWord_2083768 prefixEnd_2083768 158514749104904960269175 := by
  unfold tailWord_2083768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000631357435945043257979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50667508476581260057677305 38000631357435945043257979)
  ·
    refine ⟨57000947036153917564886969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38000631357435945043257979 57000947036153917564886969)
    ·
      refine ⟨42750710277115438173665227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57000947036153917564886969 42750710277115438173665227)
      ·
        refine ⟨64126065415673157260497841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42750710277115438173665227 64126065415673157260497841)
        ·
          refine ⟨48094549061754867945373381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64126065415673157260497841 48094549061754867945373381)
          ·
            refine ⟨9017727949079037739757509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48094549061754867945373381 9017727949079037739757509)
            ·
              refine ⟨1690823990452319576204533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9017727949079037739757509 1690823990452319576204533)
              ·
                refine ⟨158514749104904960269175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1690823990452319576204533 158514749104904960269175)
                ·
                  rfl

theorem cell21_2083768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_2083768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083768 prefixEnd_2083768 := by exact prefixLift 2083768
  have htrace : WordTrace (prefixWord ++ tailWord_2083768) baseStart_2083768 baseEnd_2083768 := by
    simpa [prefixWord, tailWord_2083768, baseEnd_2083768] using wordTrace_append hprefix tailTrace_2083768
  have hstable : (prefixWord ++ tailWord_2083768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083768).length < 2 ^ (prefixWord ++ tailWord_2083768).sum := by decide
  have hdescent : baseEnd_2083768 < baseStart_2083768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083948 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2083948 : Nat := 118140960795 + 2083948 * 2 ^ 59
def prefixEnd_2083948 : Nat := 4983230072969 + 3 ^ 40 * 2083948 * 2
def baseEnd_2083948 : Nat := 475585325767074567807157

theorem tailTrace_2083948 : CollatzResearch.WordTrace tailWord_2083948 prefixEnd_2083948 475585325767074567807157 := by
  unfold tailWord_2083948
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003913927109890414034249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50671885236146520552045665 38003913927109890414034249)
  ·
    refine ⟨28502935445332417810525687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38003913927109890414034249 28502935445332417810525687)
    ·
      refine ⟨42754403167998626715788531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28502935445332417810525687 42754403167998626715788531)
      ·
        refine ⟨64131604751997940073682797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42754403167998626715788531 64131604751997940073682797)
        ·
          refine ⟨24049351781999227527631049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64131604751997940073682797 24049351781999227527631049)
          ·
            refine ⟨18037013836499420645723287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24049351781999227527631049 18037013836499420645723287)
            ·
              refine ⟨27055520754749130968584931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18037013836499420645723287 27055520754749130968584931)
              ·
                refine ⟨40583281132123696452877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27055520754749130968584931 40583281132123696452877397)
                ·
                  refine ⟨475585325767074567807157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40583281132123696452877397 475585325767074567807157)
                  ·
                    rfl

theorem cell21_2083948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2083948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083948 prefixEnd_2083948 := by exact prefixLift 2083948
  have htrace : WordTrace (prefixWord ++ tailWord_2083948) baseStart_2083948 baseEnd_2083948 := by
    simpa [prefixWord, tailWord_2083948, baseEnd_2083948] using wordTrace_append hprefix tailTrace_2083948
  have hstable : (prefixWord ++ tailWord_2083948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083948).length < 2 ^ (prefixWord ++ tailWord_2083948).sum := by decide
  have hdescent : baseEnd_2083948 < baseStart_2083948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083965 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2083965 : Nat := 118140960795 + 2083965 * 2 ^ 59
def prefixEnd_2083965 : Nat := 4983230072969 + 3 ^ 40 * 2083965 * 2
def baseEnd_2083965 : Nat := 475589205398686316023789

theorem tailTrace_2083965 : CollatzResearch.WordTrace tailWord_2083965 prefixEnd_2083965 475589205398686316023789 := by
  unfold tailWord_2083965
  simp only [CollatzResearch.WordTrace]
  refine ⟨76008447895158192731437349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50672298596772128487624899 76008447895158192731437349)
  ·
    refine ⟨14251583980342161137144503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76008447895158192731437349 14251583980342161137144503)
    ·
      refine ⟨21377375970513241705716755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14251583980342161137144503 21377375970513241705716755)
      ·
        refine ⟨32066063955769862558575133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21377375970513241705716755 32066063955769862558575133)
        ·
          refine ⟨12024773983413698459465675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32066063955769862558575133 12024773983413698459465675)
          ·
            refine ⟨18037160975120547689198513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024773983413698459465675 18037160975120547689198513)
            ·
              refine ⟨13527870731340410766898885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18037160975120547689198513 13527870731340410766898885)
              ·
                refine ⟨2536475762126327018793541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13527870731340410766898885 2536475762126327018793541)
                ·
                  refine ⟨475589205398686316023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536475762126327018793541 475589205398686316023789)
                  ·
                    rfl

theorem cell21_2083965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2083965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083965 prefixEnd_2083965 := by exact prefixLift 2083965
  have htrace : WordTrace (prefixWord ++ tailWord_2083965) baseStart_2083965 baseEnd_2083965 := by
    simpa [prefixWord, tailWord_2083965, baseEnd_2083965] using wordTrace_append hprefix tailTrace_2083965
  have hstable : (prefixWord ++ tailWord_2083965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083965).length < 2 ^ (prefixWord ++ tailWord_2083965).sum := by decide
  have hdescent : baseEnd_2083965 < baseStart_2083965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2083982 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_2083982 : Nat := 118140960795 + 2083982 * 2 ^ 59
def prefixEnd_2083982 : Nat := 4983230072969 + 3 ^ 40 * 2083982 * 2
def baseEnd_2083982 : Nat := 475593085030298064240421

theorem tailTrace_2083982 : CollatzResearch.WordTrace tailWord_2083982 prefixEnd_2083982 475593085030298064240421 := by
  unfold tailWord_2083982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501133492012075579350775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50672711957397736423204133 9501133492012075579350775)
  ·
    refine ⟨14251700238018113369026163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501133492012075579350775 14251700238018113369026163)
    ·
      refine ⟨21377550357027170053539245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14251700238018113369026163 21377550357027170053539245)
      ·
        refine ⟨8016581383885188770077217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21377550357027170053539245 8016581383885188770077217)
        ·
          refine ⟨6012436037913891577557913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8016581383885188770077217 6012436037913891577557913)
          ·
            refine ⟨4509327028435418683168435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012436037913891577557913 4509327028435418683168435)
            ·
              refine ⟨6763990542653128024752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509327028435418683168435 6763990542653128024752653)
              ·
                refine ⟨2536496453494923009282245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6763990542653128024752653 2536496453494923009282245)
                ·
                  refine ⟨475593085030298064240421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536496453494923009282245 475593085030298064240421)
                  ·
                    rfl

theorem cell21_2083982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_2083982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2083982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2083982 prefixEnd_2083982 := by exact prefixLift 2083982
  have htrace : WordTrace (prefixWord ++ tailWord_2083982) baseStart_2083982 baseEnd_2083982 := by
    simpa [prefixWord, tailWord_2083982, baseEnd_2083982] using wordTrace_append hprefix tailTrace_2083982
  have hstable : (prefixWord ++ tailWord_2083982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2083982).length < 2 ^ (prefixWord ++ tailWord_2083982).sum := by decide
  have hdescent : baseEnd_2083982 < baseStart_2083982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2083982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084061 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2084061 : Nat := 118140960795 + 2084061 * 2 ^ 59
def prefixEnd_2084061 : Nat := 4983230072969 + 3 ^ 40 * 2084061 * 2
def baseEnd_2084061 : Nat := 475611113906611482423593

theorem tailTrace_2084061 : CollatzResearch.WordTrace tailWord_2084061 prefixEnd_2084061 475611113906611482423593 := by
  unfold tailWord_2084061
  simp only [CollatzResearch.WordTrace]
  refine ⟨76011949302810401126932037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50674632868540267417954691 76011949302810401126932037)
  ·
    refine ⟨14252240494276950211299757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76011949302810401126932037 14252240494276950211299757)
    ·
      refine ⟨5344590185353856329237409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14252240494276950211299757 5344590185353856329237409)
      ·
        refine ⟨4008442639015392246928057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5344590185353856329237409 4008442639015392246928057)
        ·
          refine ⟨3006331979261544185196043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008442639015392246928057 3006331979261544185196043)
          ·
            refine ⟨4509497968892316277794065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006331979261544185196043 4509497968892316277794065)
            ·
              refine ⟨3382123476669237208345549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509497968892316277794065 3382123476669237208345549)
              ·
                refine ⟨1268296303750963953129581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382123476669237208345549 1268296303750963953129581)
                ·
                  refine ⟨475611113906611482423593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268296303750963953129581 475611113906611482423593)
                  ·
                    rfl

theorem cell21_2084061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2084061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084061 prefixEnd_2084061 := by exact prefixLift 2084061
  have htrace : WordTrace (prefixWord ++ tailWord_2084061) baseStart_2084061 baseEnd_2084061 := by
    simpa [prefixWord, tailWord_2084061, baseEnd_2084061] using wordTrace_append hprefix tailTrace_2084061
  have hstable : (prefixWord ++ tailWord_2084061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084061).length < 2 ^ (prefixWord ++ tailWord_2084061).sum := by decide
  have hdescent : baseEnd_2084061 < baseStart_2084061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084120 : List Nat := [2, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_2084120 : Nat := 118140960795 + 2084120 * 2 ^ 59
def prefixEnd_2084120 : Nat := 4983230072969 + 3 ^ 40 * 2084120 * 2
def baseEnd_2084120 : Nat := 475624578510440490940139

theorem tailTrace_2084120 : CollatzResearch.WordTrace tailWord_2084120 prefixEnd_2084120 475624578510440490940139 := by
  unfold tailWord_2084120
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007050604798327101664907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50676067473064436135553209 38007050604798327101664907)
  ·
    refine ⟨57010575907197490652497361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38007050604798327101664907 57010575907197490652497361)
    ·
      refine ⟨42757931930398117989373021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57010575907197490652497361 42757931930398117989373021)
      ·
        refine ⟨16034224473899294246014883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42757931930398117989373021 16034224473899294246014883)
        ·
          refine ⟨24051336710848941369022325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034224473899294246014883 24051336710848941369022325)
          ·
            refine ⟨2254812816642088253345843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24051336710848941369022325 2254812816642088253345843)
            ·
              refine ⟨3382219224963132380018765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254812816642088253345843 3382219224963132380018765)
              ·
                refine ⟨1268332209361174642507037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382219224963132380018765 1268332209361174642507037)
                ·
                  refine ⟨475624578510440490940139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268332209361174642507037 475624578510440490940139)
                  ·
                    rfl

theorem cell21_2084120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_2084120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084120 prefixEnd_2084120 := by exact prefixLift 2084120
  have htrace : WordTrace (prefixWord ++ tailWord_2084120) baseStart_2084120 baseEnd_2084120 := by
    simpa [prefixWord, tailWord_2084120, baseEnd_2084120] using wordTrace_append hprefix tailTrace_2084120
  have hstable : (prefixWord ++ tailWord_2084120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084120).length < 2 ^ (prefixWord ++ tailWord_2084120).sum := by decide
  have hdescent : baseEnd_2084120 < baseStart_2084120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084131 : List Nat := [1, 1, 1, 4, 2, 5, 7]
def baseStart_2084131 : Nat := 118140960795 + 2084131 * 2 ^ 59
def prefixEnd_2084131 : Nat := 4983230072969 + 3 ^ 40 * 2084131 * 2
def baseEnd_2084131 : Nat := 52847454317811879584087

theorem tailTrace_2084131 : CollatzResearch.WordTrace tailWord_2084131 prefixEnd_2084131 52847454317811879584087 := by
  unfold tailWord_2084131
  simp only [CollatzResearch.WordTrace]
  refine ⟨76014502412556803081980247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50676334941704535387986831 76014502412556803081980247)
  ·
    refine ⟨114021753618835204622970371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76014502412556803081980247 114021753618835204622970371)
    ·
      refine ⟨171032630428252806934455557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114021753618835204622970371 171032630428252806934455557)
      ·
        refine ⟨32068618205297401300210417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171032630428252806934455557 32068618205297401300210417)
        ·
          refine ⟨24051463653973050975157813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32068618205297401300210417 24051463653973050975157813)
          ·
            refine ⟨2254824717559973528921045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24051463653973050975157813 2254824717559973528921045)
            ·
              refine ⟨52847454317811879584087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2254824717559973528921045 52847454317811879584087)
              ·
                rfl

theorem cell21_2084131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 7].length) (baseStart_2084131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084131 prefixEnd_2084131 := by exact prefixLift 2084131
  have htrace : WordTrace (prefixWord ++ tailWord_2084131) baseStart_2084131 baseEnd_2084131 := by
    simpa [prefixWord, tailWord_2084131, baseEnd_2084131] using wordTrace_append hprefix tailTrace_2084131
  have hstable : (prefixWord ++ tailWord_2084131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084131).length < 2 ^ (prefixWord ++ tailWord_2084131).sum := by decide
  have hdescent : baseEnd_2084131 < baseStart_2084131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084148 : List Nat := [2, 5, 1, 1, 1, 1, 4, 6]
def baseStart_2084148 : Nat := 118140960795 + 2084148 * 2 ^ 59
def prefixEnd_2084148 : Nat := 4983230072969 + 3 ^ 40 * 2084148 * 2
def baseEnd_2084148 : Nat := 158543656163972888157805

theorem tailTrace_2084148 : CollatzResearch.WordTrace tailWord_2084148 prefixEnd_2084148 158543656163972888157805 := by
  unfold tailWord_2084148
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007561226747607492674549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50676748302330143323566065 38007561226747607492674549)
  ·
    refine ⟨3563208865007588202438239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38007561226747607492674549 3563208865007588202438239)
    ·
      refine ⟨5344813297511382303657359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563208865007588202438239 5344813297511382303657359)
      ·
        refine ⟨8017219946267073455486039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5344813297511382303657359 8017219946267073455486039)
        ·
          refine ⟨12025829919400610183229059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017219946267073455486039 12025829919400610183229059)
          ·
            refine ⟨18038744879100915274843589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12025829919400610183229059 18038744879100915274843589)
            ·
              refine ⟨3382264664831421614033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18038744879100915274843589 3382264664831421614033173)
              ·
                refine ⟨158543656163972888157805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3382264664831421614033173 158543656163972888157805)
                ·
                  rfl

theorem cell21_2084148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_2084148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084148 prefixEnd_2084148 := by exact prefixLift 2084148
  have htrace : WordTrace (prefixWord ++ tailWord_2084148) baseStart_2084148 baseEnd_2084148 := by
    simpa [prefixWord, tailWord_2084148, baseEnd_2084148] using wordTrace_append hprefix tailTrace_2084148
  have hstable : (prefixWord ++ tailWord_2084148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084148).length < 2 ^ (prefixWord ++ tailWord_2084148).sum := by decide
  have hdescent : baseEnd_2084148 < baseStart_2084148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084182 : List Nat := [5, 2, 3, 1, 1, 9]
def baseStart_2084182 : Nat := 118140960795 + 2084182 * 2 ^ 59
def prefixEnd_2084182 : Nat := 4983230072969 + 3 ^ 40 * 2084182 * 2
def baseEnd_2084182 : Nat := 17616249176116376329877

theorem tailTrace_2084182 : CollatzResearch.WordTrace tailWord_2084182 prefixEnd_2084182 17616249176116376329877 := by
  unfold tailWord_2084182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751022658460752424505425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50677575023581359194724533 4751022658460752424505425)
  ·
    refine ⟨3563266993845564318379069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4751022658460752424505425 3563266993845564318379069)
    ·
      refine ⟨1336225122692086619392151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3563266993845564318379069 1336225122692086619392151)
      ·
        refine ⟨2004337684038129929088227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336225122692086619392151 2004337684038129929088227)
        ·
          refine ⟨3006506526057194893632341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004337684038129929088227 3006506526057194893632341)
          ·
            refine ⟨17616249176116376329877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3006506526057194893632341 17616249176116376329877)
            ·
              rfl

theorem cell21_2084182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 9].length) (baseStart_2084182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084182 prefixEnd_2084182 := by exact prefixLift 2084182
  have htrace : WordTrace (prefixWord ++ tailWord_2084182) baseStart_2084182 baseEnd_2084182 := by
    simpa [prefixWord, tailWord_2084182, baseEnd_2084182] using wordTrace_append hprefix tailTrace_2084182
  have hstable : (prefixWord ++ tailWord_2084182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084182).length < 2 ^ (prefixWord ++ tailWord_2084182).sum := by decide
  have hdescent : baseEnd_2084182 < baseStart_2084182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084196 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2084196 : Nat := 118140960795 + 2084196 * 2 ^ 59
def prefixEnd_2084196 : Nat := 4983230072969 + 3 ^ 40 * 2084196 * 2
def baseEnd_2084196 : Nat := 475641922745881247673317

theorem tailTrace_2084196 : CollatzResearch.WordTrace tailWord_2084196 prefixEnd_2084196 475641922745881247673317 := by
  unfold tailWord_2084196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38008436578660659591548221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50677915438214212788730961 38008436578660659591548221)
  ·
    refine ⟨14253163716997747346830583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38008436578660659591548221 14253163716997747346830583)
    ·
      refine ⟨21379745575496621020245875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14253163716997747346830583 21379745575496621020245875)
      ·
        refine ⟨32069618363244931530368813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21379745575496621020245875 32069618363244931530368813)
        ·
          refine ⟨12026106886216849323888305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32069618363244931530368813 12026106886216849323888305)
          ·
            refine ⟨9019580164662636992916229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026106886216849323888305 9019580164662636992916229)
            ·
              refine ⟨1691171280874244436171793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9019580164662636992916229 1691171280874244436171793)
              ·
                refine ⟨1268378460655683327128845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691171280874244436171793 1268378460655683327128845)
                ·
                  refine ⟨475641922745881247673317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268378460655683327128845 475641922745881247673317)
                  ·
                    rfl

theorem cell21_2084196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2084196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084196 prefixEnd_2084196 := by exact prefixLift 2084196
  have htrace : WordTrace (prefixWord ++ tailWord_2084196) baseStart_2084196 baseEnd_2084196 := by
    simpa [prefixWord, tailWord_2084196, baseEnd_2084196] using wordTrace_append hprefix tailTrace_2084196
  have hstable : (prefixWord ++ tailWord_2084196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084196).length < 2 ^ (prefixWord ++ tailWord_2084196).sum := by decide
  have hdescent : baseEnd_2084196 < baseStart_2084196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084255 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 3]
def baseStart_2084255 : Nat := 118140960795 + 2084255 * 2 ^ 59
def prefixEnd_2084255 : Nat := 4983230072969 + 3 ^ 40 * 2084255 * 2
def baseEnd_2084255 : Nat := 475655387349710256189863

theorem tailTrace_2084255 : CollatzResearch.WordTrace tailWord_2084255 prefixEnd_2084255 475655387349710256189863 := by
  unfold tailWord_2084255
  simp only [CollatzResearch.WordTrace]
  refine ⟨76019025064107572259494219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50679350042738381506329479 76019025064107572259494219)
  ·
    refine ⟨114028537596161358389241329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76019025064107572259494219 114028537596161358389241329)
    ·
      refine ⟨85521403197121018791930997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114028537596161358389241329 85521403197121018791930997)
      ·
        refine ⟨8017631549730095511743531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85521403197121018791930997 8017631549730095511743531)
        ·
          refine ⟨12026447324595143267615297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017631549730095511743531 12026447324595143267615297)
          ·
            refine ⟨9019835493446357450711473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026447324595143267615297 9019835493446357450711473)
            ·
              refine ⟨6764876620084768088033605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9019835493446357450711473 6764876620084768088033605)
              ·
                refine ⟨1268414366265894016506301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6764876620084768088033605 1268414366265894016506301)
                ·
                  refine ⟨475655387349710256189863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268414366265894016506301 475655387349710256189863)
                  ·
                    rfl

theorem cell21_2084255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].length) (baseStart_2084255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084255 prefixEnd_2084255 := by exact prefixLift 2084255
  have htrace : WordTrace (prefixWord ++ tailWord_2084255) baseStart_2084255 baseEnd_2084255 := by
    simpa [prefixWord, tailWord_2084255, baseEnd_2084255] using wordTrace_append hprefix tailTrace_2084255
  have hstable : (prefixWord ++ tailWord_2084255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084255).length < 2 ^ (prefixWord ++ tailWord_2084255).sum := by decide
  have hdescent : baseEnd_2084255 < baseStart_2084255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084314 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2084314 : Nat := 118140960795 + 2084314 * 2 ^ 59
def prefixEnd_2084314 : Nat := 4983230072969 + 3 ^ 40 * 2084314 * 2
def baseEnd_2084314 : Nat := 475668851953539264706409

theorem tailTrace_2084314 : CollatzResearch.WordTrace tailWord_2084314 prefixEnd_2084314 475668851953539264706409 := by
  unfold tailWord_2084314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005294242723456333972999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50680784647262550223927997 19005294242723456333972999)
  ·
    refine ⟨28507941364085184500959499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19005294242723456333972999 28507941364085184500959499)
    ·
      refine ⟨42761912046127776751439249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28507941364085184500959499 42761912046127776751439249)
      ·
        refine ⟨32071434034595832563579437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42761912046127776751439249 32071434034595832563579437)
        ·
          refine ⟨12026787762973437211342289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32071434034595832563579437 12026787762973437211342289)
          ·
            refine ⟨9020090822230077908506717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026787762973437211342289 9020090822230077908506717)
            ·
              refine ⟨3382534058336279215690019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9020090822230077908506717 3382534058336279215690019)
              ·
                refine ⟨5073801087504418823535029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382534058336279215690019 5073801087504418823535029)
                ·
                  refine ⟨475668851953539264706409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5073801087504418823535029 475668851953539264706409)
                  ·
                    rfl

theorem cell21_2084314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2084314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084314 prefixEnd_2084314 := by exact prefixLift 2084314
  have htrace : WordTrace (prefixWord ++ tailWord_2084314) baseStart_2084314 baseEnd_2084314 := by
    simpa [prefixWord, tailWord_2084314, baseEnd_2084314] using wordTrace_append hprefix tailTrace_2084314
  have hstable : (prefixWord ++ tailWord_2084314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084314).length < 2 ^ (prefixWord ++ tailWord_2084314).sum := by decide
  have hdescent : baseEnd_2084314 < baseStart_2084314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084376 : List Nat := [2, 1, 2, 3, 4, 2, 1, 6]
def baseStart_2084376 : Nat := 118140960795 + 2084376 * 2 ^ 59
def prefixEnd_2084376 : Nat := 4983230072969 + 3 ^ 40 * 2084376 * 2
def baseEnd_2084376 : Nat := 158561000399413644890983

theorem tailTrace_2084376 : CollatzResearch.WordTrace tailWord_2084376 prefixEnd_2084376 158561000399413644890983 := by
  unfold tailWord_2084376
  simp only [CollatzResearch.WordTrace]
  refine ⟨38011719148334604962324491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50682292197779473283099321 38011719148334604962324491)
  ·
    refine ⟨57017578722501907443486737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38011719148334604962324491 57017578722501907443486737)
    ·
      refine ⟨42763184041876430582615053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57017578722501907443486737 42763184041876430582615053)
      ·
        refine ⟨16036194015703661468480645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42763184041876430582615053 16036194015703661468480645)
        ·
          refine ⟨3006786377944436525340121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16036194015703661468480645 3006786377944436525340121)
          ·
            refine ⟨2255089783458327394005091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006786377944436525340121 2255089783458327394005091)
            ·
              refine ⟨3382634675187491091007637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255089783458327394005091 3382634675187491091007637)
              ·
                refine ⟨158561000399413644890983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3382634675187491091007637 158561000399413644890983)
                ·
                  rfl

theorem cell21_2084376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_2084376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084376 prefixEnd_2084376 := by exact prefixLift 2084376
  have htrace : WordTrace (prefixWord ++ tailWord_2084376) baseStart_2084376 baseEnd_2084376 := by
    simpa [prefixWord, tailWord_2084376, baseEnd_2084376] using wordTrace_append hprefix tailTrace_2084376
  have hstable : (prefixWord ++ tailWord_2084376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084376).length < 2 ^ (prefixWord ++ tailWord_2084376).sum := by decide
  have hdescent : baseEnd_2084376 < baseStart_2084376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084407 : List Nat := [1, 1, 3, 1, 2, 5, 2, 3, 3]
def baseStart_2084407 : Nat := 118140960795 + 2084407 * 2 ^ 59
def prefixEnd_2084407 : Nat := 4983230072969 + 3 ^ 40 * 2084407 * 2
def baseEnd_2084407 : Nat := 475690075820591769656219

theorem tailTrace_2084407 : CollatzResearch.WordTrace tailWord_2084407 prefixEnd_2084407 475690075820591769656219 := by
  unfold tailWord_2084407
  simp only [CollatzResearch.WordTrace]
  refine ⟨76024568959556902219027475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50683045973037934812684983 76024568959556902219027475)
  ·
    refine ⟨114036853439335353328541213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76024568959556902219027475 114036853439335353328541213)
    ·
      refine ⟨42763820039750757498202955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114036853439335353328541213 42763820039750757498202955)
      ·
        refine ⟨64145730059626136247304433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42763820039750757498202955 64145730059626136247304433)
        ·
          refine ⟨48109297544719602185478325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64145730059626136247304433 48109297544719602185478325)
          ·
            refine ⟨4510246644817462704888593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48109297544719602185478325 4510246644817462704888593)
            ·
              refine ⟨3382684983613097028666445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510246644817462704888593 3382684983613097028666445)
              ·
                refine ⟨1268506868854911385749917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382684983613097028666445 1268506868854911385749917)
                ·
                  refine ⟨475690075820591769656219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268506868854911385749917 475690075820591769656219)
                  ·
                    rfl

theorem cell21_2084407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 3].length) (baseStart_2084407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084407 prefixEnd_2084407 := by exact prefixLift 2084407
  have htrace : WordTrace (prefixWord ++ tailWord_2084407) baseStart_2084407 baseEnd_2084407 := by
    simpa [prefixWord, tailWord_2084407, baseEnd_2084407] using wordTrace_append hprefix tailTrace_2084407
  have hstable : (prefixWord ++ tailWord_2084407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084407).length < 2 ^ (prefixWord ++ tailWord_2084407).sum := by decide
  have hdescent : baseEnd_2084407 < baseStart_2084407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084449 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_2084449 : Nat := 118140960795 + 2084449 * 2 ^ 59
def prefixEnd_2084449 : Nat := 4983230072969 + 3 ^ 40 * 2084449 * 2
def baseEnd_2084449 : Nat := 475699660792809029956133

theorem tailTrace_2084449 : CollatzResearch.WordTrace tailWord_2084449 prefixEnd_2084449 475699660792809029956133 := by
  unfold tailWord_2084449
  simp only [CollatzResearch.WordTrace]
  refine ⟨76026100825404743392056401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50684067216936495594704267 76026100825404743392056401)
  ·
    refine ⟨57019575619053557544042301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76026100825404743392056401 57019575619053557544042301)
    ·
      refine ⟨21382340857145084079015863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57019575619053557544042301 21382340857145084079015863)
      ·
        refine ⟨32073511285717626118523795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382340857145084079015863 32073511285717626118523795)
        ·
          refine ⟨48110266928576439177785693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32073511285717626118523795 48110266928576439177785693)
          ·
            refine ⟨18041350098216164691669635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48110266928576439177785693 18041350098216164691669635)
            ·
              refine ⟨27062025147324247037504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18041350098216164691669635 27062025147324247037504453)
              ·
                refine ⟨5074129715123296319532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27062025147324247037504453 5074129715123296319532085)
                ·
                  refine ⟨475699660792809029956133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5074129715123296319532085 475699660792809029956133)
                  ·
                    rfl

theorem cell21_2084449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_2084449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084449 prefixEnd_2084449 := by exact prefixLift 2084449
  have htrace : WordTrace (prefixWord ++ tailWord_2084449) baseStart_2084449 baseEnd_2084449 := by
    simpa [prefixWord, tailWord_2084449, baseEnd_2084449] using wordTrace_append hprefix tailTrace_2084449
  have hstable : (prefixWord ++ tailWord_2084449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084449).length < 2 ^ (prefixWord ++ tailWord_2084449).sum := by decide
  have hdescent : baseEnd_2084449 < baseStart_2084449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084452 : List Nat := [2, 3, 1, 1, 2, 5, 2, 5]
def baseStart_2084452 : Nat := 118140960795 + 2084452 * 2 ^ 59
def prefixEnd_2084452 : Nat := 4983230072969 + 3 ^ 40 * 2084452 * 2
def baseEnd_2084452 : Nat := 158566781811227230468709

theorem tailTrace_2084452 : CollatzResearch.WordTrace tailWord_2084452 prefixEnd_2084452 158566781811227230468709 := by
  unfold tailWord_2084452
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013105122196937452207805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50684140162929249936277073 38013105122196937452207805)
  ·
    refine ⟨14254914420823851544577927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38013105122196937452207805 14254914420823851544577927)
    ·
      refine ⟨21382371631235777316866891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14254914420823851544577927 21382371631235777316866891)
      ·
        refine ⟨32073557446853665975300337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382371631235777316866891 32073557446853665975300337)
        ·
          refine ⟨24055168085140249481475253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32073557446853665975300337 24055168085140249481475253)
          ·
            refine ⟨2255172007981898388888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24055168085140249481475253 2255172007981898388888305)
            ·
              refine ⟨1691379005986423791666229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255172007981898388888305 1691379005986423791666229)
              ·
                refine ⟨158566781811227230468709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1691379005986423791666229 158566781811227230468709)
                ·
                  rfl

theorem cell21_2084452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_2084452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084452 prefixEnd_2084452 := by exact prefixLift 2084452
  have htrace : WordTrace (prefixWord ++ tailWord_2084452) baseStart_2084452 baseEnd_2084452 := by
    simpa [prefixWord, tailWord_2084452, baseEnd_2084452] using wordTrace_append hprefix tailTrace_2084452
  have hstable : (prefixWord ++ tailWord_2084452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084452).length < 2 ^ (prefixWord ++ tailWord_2084452).sum := by decide
  have hdescent : baseEnd_2084452 < baseStart_2084452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084480 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_2084480 : Nat := 118140960795 + 2084480 * 2 ^ 59
def prefixEnd_2084480 : Nat := 4983230072969 + 3 ^ 40 * 2084480 * 2
def baseEnd_2084480 : Nat := 475706735415159864939403

theorem tailTrace_2084480 : CollatzResearch.WordTrace tailWord_2084480 prefixEnd_2084480 475706735415159864939403 := by
  unfold tailWord_2084480
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013615744146217843217447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50684820992194957124289929 38013615744146217843217447)
  ·
    refine ⟨57020423616219326764826171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38013615744146217843217447 57020423616219326764826171)
    ·
      refine ⟨85530635424328990147239257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57020423616219326764826171 85530635424328990147239257)
      ·
        refine ⟨64147976568246742610429443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85530635424328990147239257 64147976568246742610429443)
        ·
          refine ⟨96221964852370113915644165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64147976568246742610429443 96221964852370113915644165)
          ·
            refine ⟨18041618409819396359183281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96221964852370113915644165 18041618409819396359183281)
            ·
              refine ⟨13531213807364547269387461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18041618409819396359183281 13531213807364547269387461)
              ·
                refine ⟨2537102588880852613010149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13531213807364547269387461 2537102588880852613010149)
                ·
                  refine ⟨475706735415159864939403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537102588880852613010149 475706735415159864939403)
                  ·
                    rfl

theorem cell21_2084480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_2084480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084480 prefixEnd_2084480 := by exact prefixLift 2084480
  have htrace : WordTrace (prefixWord ++ tailWord_2084480) baseStart_2084480 baseEnd_2084480 := by
    simpa [prefixWord, tailWord_2084480, baseEnd_2084480] using wordTrace_append hprefix tailTrace_2084480
  have hstable : (prefixWord ++ tailWord_2084480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084480).length < 2 ^ (prefixWord ++ tailWord_2084480).sum := by decide
  have hdescent : baseEnd_2084480 < baseStart_2084480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084534 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2084534 : Nat := 118140960795 + 2084534 * 2 ^ 59
def prefixEnd_2084534 : Nat := 4983230072969 + 3 ^ 40 * 2084534 * 2
def baseEnd_2084534 : Nat := 475719058950867771039293

theorem tailTrace_2084534 : CollatzResearch.WordTrace tailWord_2084534 prefixEnd_2084534 475719058950867771039293 := by
  unfold tailWord_2084534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751825064381050181806291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50686134020064535272600437 4751825064381050181806291)
  ·
    refine ⟨7127737596571575272709437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751825064381050181806291 7127737596571575272709437)
    ·
      refine ⟨2672901598714340727266039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7127737596571575272709437 2672901598714340727266039)
      ·
        refine ⟨4009352398071511090899059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672901598714340727266039 4009352398071511090899059)
        ·
          refine ⟨6014028597107266636348589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009352398071511090899059 6014028597107266636348589)
          ·
            refine ⟨2255260723915224988630721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014028597107266636348589 2255260723915224988630721)
            ·
              refine ⟨1691445542936418741473041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255260723915224988630721 1691445542936418741473041)
              ·
                refine ⟨1268584157202314056104781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691445542936418741473041 1268584157202314056104781)
                ·
                  refine ⟨475719058950867771039293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268584157202314056104781 475719058950867771039293)
                  ·
                    rfl

theorem cell21_2084534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2084534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084534 prefixEnd_2084534 := by exact prefixLift 2084534
  have htrace : WordTrace (prefixWord ++ tailWord_2084534) baseStart_2084534 baseEnd_2084534 := by
    simpa [prefixWord, tailWord_2084534, baseEnd_2084534] using wordTrace_append hprefix tailTrace_2084534
  have hstable : (prefixWord ++ tailWord_2084534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084534).length < 2 ^ (prefixWord ++ tailWord_2084534).sum := by decide
  have hdescent : baseEnd_2084534 < baseStart_2084534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084539 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_2084539 : Nat := 118140960795 + 2084539 * 2 ^ 59
def prefixEnd_2084539 : Nat := 4983230072969 + 3 ^ 40 * 2084539 * 2
def baseEnd_2084539 : Nat := 475720200018988873455949

theorem tailTrace_2084539 : CollatzResearch.WordTrace tailWord_2084539 prefixEnd_2084539 475720200018988873455949 := by
  unfold tailWord_2084539
  simp only [CollatzResearch.WordTrace]
  refine ⟨76029383395078688762832671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50686255596719125841888447 76029383395078688762832671)
  ·
    refine ⟨114044075092618033144249007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76029383395078688762832671 114044075092618033144249007)
    ·
      refine ⟨171066112638927049716373511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114044075092618033144249007 171066112638927049716373511)
      ·
        refine ⟨256599168958390574574560267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171066112638927049716373511 256599168958390574574560267)
        ·
          refine ⟨384898753437585861861840401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256599168958390574574560267 384898753437585861861840401)
          ·
            refine ⟨288674065078189396396380301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384898753437585861861840401 288674065078189396396380301)
            ·
              refine ⟨108252774404321023648642613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288674065078189396396380301 108252774404321023648642613)
              ·
                refine ⟨10148697600405095967060245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108252774404321023648642613 10148697600405095967060245)
                ·
                  refine ⟨475720200018988873455949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10148697600405095967060245 475720200018988873455949)
                  ·
                    rfl

theorem cell21_2084539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_2084539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084539 prefixEnd_2084539 := by exact prefixLift 2084539
  have htrace : WordTrace (prefixWord ++ tailWord_2084539) baseStart_2084539 baseEnd_2084539 := by
    simpa [prefixWord, tailWord_2084539, baseEnd_2084539] using wordTrace_append hprefix tailTrace_2084539
  have hstable : (prefixWord ++ tailWord_2084539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084539).length < 2 ^ (prefixWord ++ tailWord_2084539).sum := by decide
  have hdescent : baseEnd_2084539 < baseStart_2084539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084638 : List Nat := [4, 3, 2, 2, 2, 1, 7]
def baseStart_2084638 : Nat := 118140960795 + 2084638 * 2 ^ 59
def prefixEnd_2084638 : Nat := 4983230072969 + 3 ^ 40 * 2084638 * 2
def baseEnd_2084638 : Nat := 52860310351976300145083

theorem tailTrace_2084638 : CollatzResearch.WordTrace tailWord_2084638 prefixEnd_2084638 52860310351976300145083 := by
  unfold tailWord_2084638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504124277715003583835821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50688662814480019113791045 9504124277715003583835821)
  ·
    refine ⟨3564046604143126343938433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9504124277715003583835821 3564046604143126343938433)
    ·
      refine ⟨2673034953107344757953825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564046604143126343938433 2673034953107344757953825)
      ·
        refine ⟨2004776214830508568465369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673034953107344757953825 2004776214830508568465369)
        ·
          refine ⟨1503582161122881426349027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004776214830508568465369 1503582161122881426349027)
          ·
            refine ⟨2255373241684322139523541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503582161122881426349027 2255373241684322139523541)
            ·
              refine ⟨52860310351976300145083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2255373241684322139523541 52860310351976300145083)
              ·
                rfl

theorem cell21_2084638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 7].length) (baseStart_2084638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084638 prefixEnd_2084638 := by exact prefixLift 2084638
  have htrace : WordTrace (prefixWord ++ tailWord_2084638) baseStart_2084638 baseEnd_2084638 := by
    simpa [prefixWord, tailWord_2084638, baseEnd_2084638] using wordTrace_append hprefix tailTrace_2084638
  have hstable : (prefixWord ++ tailWord_2084638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084638).length < 2 ^ (prefixWord ++ tailWord_2084638).sum := by decide
  have hdescent : baseEnd_2084638 < baseStart_2084638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084666 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_2084666 : Nat := 118140960795 + 2084666 * 2 ^ 59
def prefixEnd_2084666 : Nat := 4983230072969 + 3 ^ 40 * 2084666 * 2
def baseEnd_2084666 : Nat := 475749183149264874839023

theorem tailTrace_2084666 : CollatzResearch.WordTrace tailWord_2084666 prefixEnd_2084666 475749183149264874839023 := by
  unfold tailWord_2084666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008503866404647363176463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50689343643745726301803901 19008503866404647363176463)
  ·
    refine ⟨28512755799606971044764695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008503866404647363176463 28512755799606971044764695)
    ·
      refine ⟨42769133699410456567147043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28512755799606971044764695 42769133699410456567147043)
      ·
        refine ⟨64153700549115684850720565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42769133699410456567147043 64153700549115684850720565)
        ·
          refine ⟨6014409426479595454755053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64153700549115684850720565 6014409426479595454755053)
          ·
            refine ⟨2255403534929848295533145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014409426479595454755053 2255403534929848295533145)
            ·
              refine ⟨1691552651197386221649859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255403534929848295533145 1691552651197386221649859)
              ·
                refine ⟨2537328976796079332474789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691552651197386221649859 2537328976796079332474789)
                ·
                  refine ⟨475749183149264874839023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537328976796079332474789 475749183149264874839023)
                  ·
                    rfl

theorem cell21_2084666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_2084666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084666 prefixEnd_2084666 := by exact prefixLift 2084666
  have htrace : WordTrace (prefixWord ++ tailWord_2084666) baseStart_2084666 baseEnd_2084666 := by
    simpa [prefixWord, tailWord_2084666, baseEnd_2084666] using wordTrace_append hprefix tailTrace_2084666
  have hstable : (prefixWord ++ tailWord_2084666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084666).length < 2 ^ (prefixWord ++ tailWord_2084666).sum := by decide
  have hdescent : baseEnd_2084666 < baseStart_2084666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084739 : List Nat := [1, 1, 1, 3, 4, 3, 3, 5]
def baseStart_2084739 : Nat := 118140960795 + 2084739 * 2 ^ 59
def prefixEnd_2084739 : Nat := 4983230072969 + 3 ^ 40 * 2084739 * 2
def baseEnd_2084739 : Nat := 158588614247944323374069

theorem tailTrace_2084739 : CollatzResearch.WordTrace tailWord_2084739 prefixEnd_2084739 158588614247944323374069 := by
  unfold tailWord_2084739
  simp only [CollatzResearch.WordTrace]
  refine ⟨76036677994354122920113271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50691118662902748613408847 76036677994354122920113271)
  ·
    refine ⟨114055016991531184380169907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76036677994354122920113271 114055016991531184380169907)
    ·
      refine ⟨171082525487296776570254861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114055016991531184380169907 171082525487296776570254861)
      ·
        refine ⟨64155947057736291213845573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171082525487296776570254861 64155947057736291213845573)
        ·
          refine ⟨12029240073325554602596045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64155947057736291213845573 12029240073325554602596045)
          ·
            refine ⟨4510965027497082975973517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12029240073325554602596045 4510965027497082975973517)
            ·
              refine ⟨1691611885311406115990069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4510965027497082975973517 1691611885311406115990069)
              ·
                refine ⟨158588614247944323374069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1691611885311406115990069 158588614247944323374069)
                ·
                  rfl

theorem cell21_2084739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 5].length) (baseStart_2084739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084739 prefixEnd_2084739 := by exact prefixLift 2084739
  have htrace : WordTrace (prefixWord ++ tailWord_2084739) baseStart_2084739 baseEnd_2084739 := by
    simpa [prefixWord, tailWord_2084739, baseEnd_2084739] using wordTrace_append hprefix tailTrace_2084739
  have hstable : (prefixWord ++ tailWord_2084739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084739).length < 2 ^ (prefixWord ++ tailWord_2084739).sum := by decide
  have hdescent : baseEnd_2084739 < baseStart_2084739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084874 : List Nat := [3, 1, 2, 2, 4, 9]
def baseStart_2084874 : Nat := 118140960795 + 2084874 * 2 ^ 59
def prefixEnd_2084874 : Nat := 4983230072969 + 3 ^ 40 * 2084874 * 2
def baseEnd_2084874 : Nat := 17622098206781582791553

theorem tailTrace_2084874 : CollatzResearch.WordTrace tailWord_2084874 prefixEnd_2084874 17622098206781582791553 := by
  unfold tailWord_2084874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010400462216260244069419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50694401232576693984185117 19010400462216260244069419)
  ·
    refine ⟨28515600693324390366104129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19010400462216260244069419 28515600693324390366104129)
    ·
      refine ⟨21386700519993292774578097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28515600693324390366104129 21386700519993292774578097)
      ·
        refine ⟨16040025389994969580933573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21386700519993292774578097 16040025389994969580933573)
        ·
          refine ⟨3007504760624056796425045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16040025389994969580933573 3007504760624056796425045)
          ·
            refine ⟨17622098206781582791553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3007504760624056796425045 17622098206781582791553)
            ·
              rfl

theorem cell21_2084874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 9].length) (baseStart_2084874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084874 prefixEnd_2084874 := by exact prefixLift 2084874
  have htrace : WordTrace (prefixWord ++ tailWord_2084874) baseStart_2084874 baseEnd_2084874 := by
    simpa [prefixWord, tailWord_2084874, baseEnd_2084874] using wordTrace_append hprefix tailTrace_2084874
  have hstable : (prefixWord ++ tailWord_2084874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084874).length < 2 ^ (prefixWord ++ tailWord_2084874).sum := by decide
  have hdescent : baseEnd_2084874 < baseStart_2084874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2084995 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_2084995 : Nat := 118140960795 + 2084995 * 2 ^ 59
def prefixEnd_2084995 : Nat := 4983230072969 + 3 ^ 40 * 2084995 * 2
def baseEnd_2084995 : Nat := 475824265431633413855017

theorem tailTrace_2084995 : CollatzResearch.WordTrace tailWord_2084995 prefixEnd_2084995 475824265431633413855017 := by
  unfold tailWord_2084995
  simp only [CollatzResearch.WordTrace]
  refine ⟨76046015081426678641432439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50697343387617785760954959 76046015081426678641432439)
  ·
    refine ⟨114069022622140017962148659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76046015081426678641432439 114069022622140017962148659)
    ·
      refine ⟨171103533933210026943222989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114069022622140017962148659 171103533933210026943222989)
      ·
        refine ⟨64163825224953760103708621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171103533933210026943222989 64163825224953760103708621)
        ·
          refine ⟨24061434459357660038890733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64163825224953760103708621 24061434459357660038890733)
          ·
            refine ⟨9023037922259122514584025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24061434459357660038890733 9023037922259122514584025)
            ·
              refine ⟨6767278441694341885938019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023037922259122514584025 6767278441694341885938019)
              ·
                refine ⟨10150917662541512828907029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767278441694341885938019 10150917662541512828907029)
                ·
                  refine ⟨475824265431633413855017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10150917662541512828907029 475824265431633413855017)
                  ·
                    rfl

theorem cell21_2084995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_2084995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2084995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2084995 prefixEnd_2084995 := by exact prefixLift 2084995
  have htrace : WordTrace (prefixWord ++ tailWord_2084995) baseStart_2084995 baseEnd_2084995 := by
    simpa [prefixWord, tailWord_2084995, baseEnd_2084995] using wordTrace_append hprefix tailTrace_2084995
  have hstable : (prefixWord ++ tailWord_2084995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2084995).length < 2 ^ (prefixWord ++ tailWord_2084995).sum := by decide
  have hdescent : baseEnd_2084995 < baseStart_2084995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2084995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085071 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_2085071 : Nat := 118140960795 + 2085071 * 2 ^ 59
def prefixEnd_2085071 : Nat := 4983230072969 + 3 ^ 40 * 2085071 * 2
def baseEnd_2085071 : Nat := 475841609667074170588195

theorem tailTrace_2085071 : CollatzResearch.WordTrace tailWord_2085071 prefixEnd_2085071 475841609667074170588195 := by
  unfold tailWord_2085071
  simp only [CollatzResearch.WordTrace]
  refine ⟨76048787029151343621199067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50699191352767562414132711 76048787029151343621199067)
  ·
    refine ⟨114073180543727015431798601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76048787029151343621199067 114073180543727015431798601)
    ·
      refine ⟨85554885407795261573848951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114073180543727015431798601 85554885407795261573848951)
      ·
        refine ⟨128332328111692892360773427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85554885407795261573848951 128332328111692892360773427)
        ·
          refine ⟨192498492167539338541160141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128332328111692892360773427 192498492167539338541160141)
          ·
            refine ⟨72186934562827251952935053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192498492167539338541160141 72186934562827251952935053)
            ·
              refine ⟨27070100461060219482350645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72186934562827251952935053 27070100461060219482350645)
              ·
                refine ⟨2537821918224395576470373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27070100461060219482350645 2537821918224395576470373)
                ·
                  refine ⟨475841609667074170588195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537821918224395576470373 475841609667074170588195)
                  ·
                    rfl

theorem cell21_2085071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_2085071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085071 prefixEnd_2085071 := by exact prefixLift 2085071
  have htrace : WordTrace (prefixWord ++ tailWord_2085071) baseStart_2085071 baseEnd_2085071 := by
    simpa [prefixWord, tailWord_2085071, baseEnd_2085071] using wordTrace_append hprefix tailTrace_2085071
  have hstable : (prefixWord ++ tailWord_2085071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085071).length < 2 ^ (prefixWord ++ tailWord_2085071).sum := by decide
  have hdescent : baseEnd_2085071 < baseStart_2085071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085122 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2085122 : Nat := 118140960795 + 2085122 * 2 ^ 59
def prefixEnd_2085122 : Nat := 4983230072969 + 3 ^ 40 * 2085122 * 2
def baseEnd_2085122 : Nat := 475853248561909415238091

theorem tailTrace_2085122 : CollatzResearch.WordTrace tailWord_2085122 prefixEnd_2085122 475853248561909415238091 := by
  unfold tailWord_2085122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012661787991644832826405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50700431434644386220870413 19012661787991644832826405)
  ·
    refine ⟨3564874085248433406154951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19012661787991644832826405 3564874085248433406154951)
    ·
      refine ⟨5347311127872650109232427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564874085248433406154951 5347311127872650109232427)
      ·
        refine ⟨8020966691808975163848641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347311127872650109232427 8020966691808975163848641)
        ·
          refine ⟨6015725018856731372886481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8020966691808975163848641 6015725018856731372886481)
          ·
            refine ⟨4511793764142548529664861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6015725018856731372886481 4511793764142548529664861)
            ·
              refine ⟨1691922661553455698624323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4511793764142548529664861 1691922661553455698624323)
              ·
                refine ⟨2537883992330183547936485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691922661553455698624323 2537883992330183547936485)
                ·
                  refine ⟨475853248561909415238091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537883992330183547936485 475853248561909415238091)
                  ·
                    rfl

theorem cell21_2085122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2085122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085122 prefixEnd_2085122 := by exact prefixLift 2085122
  have htrace : WordTrace (prefixWord ++ tailWord_2085122) baseStart_2085122 baseEnd_2085122 := by
    simpa [prefixWord, tailWord_2085122, baseEnd_2085122] using wordTrace_append hprefix tailTrace_2085122
  have hstable : (prefixWord ++ tailWord_2085122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085122).length < 2 ^ (prefixWord ++ tailWord_2085122).sum := by decide
  have hdescent : baseEnd_2085122 < baseStart_2085122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085178 : List Nat := [3, 1, 1, 1, 4, 3, 2, 6]
def baseStart_2085178 : Nat := 118140960795 + 2085178 * 2 ^ 59
def prefixEnd_2085178 : Nat := 4983230072969 + 3 ^ 40 * 2085178 * 2
def baseEnd_2085178 : Nat := 158622009508288587434881

theorem tailTrace_2085178 : CollatzResearch.WordTrace tailWord_2085178 prefixEnd_2085178 158622009508288587434881 := by
  unfold tailWord_2085178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19013172409940925223836047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50701793093175800596896125 19013172409940925223836047)
  ·
    refine ⟨28519758614911387835754071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19013172409940925223836047 28519758614911387835754071)
    ·
      refine ⟨42779637922367081753631107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28519758614911387835754071 42779637922367081753631107)
      ·
        refine ⟨64169456883550622630446661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42779637922367081753631107 64169456883550622630446661)
        ·
          refine ⟨12031773165665741743208749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64169456883550622630446661 12031773165665741743208749)
          ·
            refine ⟨4511914937124653153703281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12031773165665741743208749 4511914937124653153703281)
            ·
              refine ⟨3383936202843489865277461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511914937124653153703281 3383936202843489865277461)
              ·
                refine ⟨158622009508288587434881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3383936202843489865277461 158622009508288587434881)
                ·
                  rfl

theorem cell21_2085178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_2085178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085178 prefixEnd_2085178 := by exact prefixLift 2085178
  have htrace : WordTrace (prefixWord ++ tailWord_2085178) baseStart_2085178 baseEnd_2085178 := by
    simpa [prefixWord, tailWord_2085178, baseEnd_2085178] using wordTrace_append hprefix tailTrace_2085178
  have hstable : (prefixWord ++ tailWord_2085178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085178).length < 2 ^ (prefixWord ++ tailWord_2085178).sum := by decide
  have hdescent : baseEnd_2085178 < baseStart_2085178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085192 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2085192 : Nat := 118140960795 + 2085192 * 2 ^ 59
def prefixEnd_2085192 : Nat := 4983230072969 + 3 ^ 40 * 2085192 * 2
def baseEnd_2085192 : Nat := 475869223515604849071281

theorem tailTrace_2085192 : CollatzResearch.WordTrace tailWord_2085192 prefixEnd_2085192 475869223515604849071281 := by
  unfold tailWord_2085192
  simp only [CollatzResearch.WordTrace]
  refine ⟨38026600130856490643176915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50702133507808654190902553 38026600130856490643176915)
  ·
    refine ⟨57039900196284735964765373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38026600130856490643176915 57039900196284735964765373)
    ·
      refine ⟨21389962573606775986787015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57039900196284735964765373 21389962573606775986787015)
      ·
        refine ⟨32084943860410163980180523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389962573606775986787015 32084943860410163980180523)
        ·
          refine ⟨48127415790615245970270785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32084943860410163980180523 48127415790615245970270785)
          ·
            refine ⟨36095561842961434477703089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48127415790615245970270785 36095561842961434477703089)
            ·
              refine ⟨27071671382221075858277317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36095561842961434477703089 27071671382221075858277317)
              ·
                refine ⟨5075938384166451723426997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27071671382221075858277317 5075938384166451723426997)
                ·
                  refine ⟨475869223515604849071281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075938384166451723426997 475869223515604849071281)
                  ·
                    rfl

theorem cell21_2085192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2085192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085192 prefixEnd_2085192 := by exact prefixLift 2085192
  have htrace : WordTrace (prefixWord ++ tailWord_2085192) baseStart_2085192 baseEnd_2085192 := by
    simpa [prefixWord, tailWord_2085192, baseEnd_2085192] using wordTrace_append hprefix tailTrace_2085192
  have hstable : (prefixWord ++ tailWord_2085192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085192).length < 2 ^ (prefixWord ++ tailWord_2085192).sum := by decide
  have hdescent : baseEnd_2085192 < baseStart_2085192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085209 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 3]
def baseStart_2085209 : Nat := 118140960795 + 2085209 * 2 ^ 59
def prefixEnd_2085209 : Nat := 4983230072969 + 3 ^ 40 * 2085209 * 2
def baseEnd_2085209 : Nat := 475873103147216597287913

theorem tailTrace_2085209 : CollatzResearch.WordTrace tailWord_2085209 prefixEnd_2085209 475873103147216597287913 := by
  unfold tailWord_2085209
  simp only [CollatzResearch.WordTrace]
  refine ⟨76053820302651393189722681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50702546868434262126481787 76053820302651393189722681)
  ·
    refine ⟨57040365226988544892292011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76053820302651393189722681 57040365226988544892292011)
    ·
      refine ⟨85560547840482817338438017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57040365226988544892292011 85560547840482817338438017)
      ·
        refine ⟨64170410880362113003828513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85560547840482817338438017 64170410880362113003828513)
        ·
          refine ⟨48127808160271584752871385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64170410880362113003828513 48127808160271584752871385)
          ·
            refine ⟨36095856120203688564653539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48127808160271584752871385 36095856120203688564653539)
            ·
              refine ⟨54143784180305532846980309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36095856120203688564653539 54143784180305532846980309)
              ·
                refine ⟨1268994941725910926101101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54143784180305532846980309 1268994941725910926101101)
                ·
                  refine ⟨475873103147216597287913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268994941725910926101101 475873103147216597287913)
                  ·
                    rfl

theorem cell21_2085209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_2085209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085209 prefixEnd_2085209 := by exact prefixLift 2085209
  have htrace : WordTrace (prefixWord ++ tailWord_2085209) baseStart_2085209 baseEnd_2085209 := by
    simpa [prefixWord, tailWord_2085209, baseEnd_2085209] using wordTrace_append hprefix tailTrace_2085209
  have hstable : (prefixWord ++ tailWord_2085209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085209).length < 2 ^ (prefixWord ++ tailWord_2085209).sum := by decide
  have hdescent : baseEnd_2085209 < baseStart_2085209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085285 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 3]
def baseStart_2085285 : Nat := 118140960795 + 2085285 * 2 ^ 59
def prefixEnd_2085285 : Nat := 4983230072969 + 3 ^ 40 * 2085285 * 2
def baseEnd_2085285 : Nat := 475890447382657354021091

theorem tailTrace_2085285 : CollatzResearch.WordTrace tailWord_2085285 prefixEnd_2085285 475890447382657354021091 := by
  unfold tailWord_2085285
  simp only [CollatzResearch.WordTrace]
  refine ⟨76056592250376058169489309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50704394833584038779659539 76056592250376058169489309)
  ·
    refine ⟨28521222093891021813558491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76056592250376058169489309 28521222093891021813558491)
    ·
      refine ⟨42781833140836532720337737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521222093891021813558491 42781833140836532720337737)
      ·
        refine ⟨32086374855627399540253303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781833140836532720337737 32086374855627399540253303)
        ·
          refine ⟨48129562283441099310379955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32086374855627399540253303 48129562283441099310379955)
          ·
            refine ⟨72194343425161648965569933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48129562283441099310379955 72194343425161648965569933)
            ·
              refine ⟨27072878784435618362088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72194343425161648965569933 27072878784435618362088725)
              ·
                refine ⟨1269041193020419610722909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27072878784435618362088725 1269041193020419610722909)
                ·
                  refine ⟨475890447382657354021091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269041193020419610722909 475890447382657354021091)
                  ·
                    rfl

theorem cell21_2085285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_2085285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085285 prefixEnd_2085285 := by exact prefixLift 2085285
  have htrace : WordTrace (prefixWord ++ tailWord_2085285) baseStart_2085285 baseEnd_2085285 := by
    simpa [prefixWord, tailWord_2085285, baseEnd_2085285] using wordTrace_append hprefix tailTrace_2085285
  have hstable : (prefixWord ++ tailWord_2085285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085285).length < 2 ^ (prefixWord ++ tailWord_2085285).sum := by decide
  have hdescent : baseEnd_2085285 < baseStart_2085285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085403 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_2085403 : Nat := 118140960795 + 2085403 * 2 ^ 59
def prefixEnd_2085403 : Nat := 4983230072969 + 3 ^ 40 * 2085403 * 2
def baseEnd_2085403 : Nat := 475917376590315371054183

theorem tailTrace_2085403 : CollatzResearch.WordTrace tailWord_2085403 prefixEnd_2085403 475917376590315371054183 := by
  unfold tailWord_2085403
  simp only [CollatzResearch.WordTrace]
  refine ⟨76060896063948564322284863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50707264042632376214856575 76060896063948564322284863)
  ·
    refine ⟨114091344095922846483427295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76060896063948564322284863 114091344095922846483427295)
    ·
      refine ⟨171137016143884269725140943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114091344095922846483427295 171137016143884269725140943)
      ·
        refine ⟨256705524215826404587711415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171137016143884269725140943 256705524215826404587711415)
        ·
          refine ⟨385058286323739606881567123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256705524215826404587711415 385058286323739606881567123)
          ·
            refine ⟨577587429485609410322350685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385058286323739606881567123 577587429485609410322350685)
            ·
              refine ⟨216595286057103528870881507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577587429485609410322350685 216595286057103528870881507)
              ·
                refine ⟨324892929085655293306322261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216595286057103528870881507 324892929085655293306322261)
                ·
                  refine ⟨475917376590315371054183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 324892929085655293306322261 475917376590315371054183)
                  ·
                    rfl

theorem cell21_2085403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_2085403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085403 prefixEnd_2085403 := by exact prefixLift 2085403
  have htrace : WordTrace (prefixWord ++ tailWord_2085403) baseStart_2085403 baseEnd_2085403 := by
    simpa [prefixWord, tailWord_2085403, baseEnd_2085403] using wordTrace_append hprefix tailTrace_2085403
  have hstable : (prefixWord ++ tailWord_2085403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085403).length < 2 ^ (prefixWord ++ tailWord_2085403).sum := by decide
  have hdescent : baseEnd_2085403 < baseStart_2085403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085451 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_2085451 : Nat := 118140960795 + 2085451 * 2 ^ 59
def prefixEnd_2085451 : Nat := 4983230072969 + 3 ^ 40 * 2085451 * 2
def baseEnd_2085451 : Nat := 475928330844277954254085

theorem tailTrace_2085451 : CollatzResearch.WordTrace tailWord_2085451 prefixEnd_2085451 475928330844277954254085 := by
  unfold tailWord_2085451
  simp only [CollatzResearch.WordTrace]
  refine ⟨76062646767774668520032207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50708431178516445680021471 76062646767774668520032207)
  ·
    refine ⟨114093970151662002780048311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76062646767774668520032207 114093970151662002780048311)
    ·
      refine ⟨171140955227493004170072467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114093970151662002780048311 171140955227493004170072467)
      ·
        refine ⟨256711432841239506255108701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171140955227493004170072467 256711432841239506255108701)
        ·
          refine ⟨96266787315464814845665763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256711432841239506255108701 96266787315464814845665763)
          ·
            refine ⟨144400180973197222268498645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96266787315464814845665763 144400180973197222268498645)
            ·
              refine ⟨3384379241559309896917937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144400180973197222268498645 3384379241559309896917937)
              ·
                refine ⟨2538284431169482422688453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384379241559309896917937 2538284431169482422688453)
                ·
                  refine ⟨475928330844277954254085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538284431169482422688453 475928330844277954254085)
                  ·
                    rfl

theorem cell21_2085451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_2085451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085451 prefixEnd_2085451 := by exact prefixLift 2085451
  have htrace : WordTrace (prefixWord ++ tailWord_2085451) baseStart_2085451 baseEnd_2085451 := by
    simpa [prefixWord, tailWord_2085451, baseEnd_2085451] using wordTrace_append hprefix tailTrace_2085451
  have hstable : (prefixWord ++ tailWord_2085451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085451).length < 2 ^ (prefixWord ++ tailWord_2085451).sum := by decide
  have hdescent : baseEnd_2085451 < baseStart_2085451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085527 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_2085527 : Nat := 118140960795 + 2085527 * 2 ^ 59
def prefixEnd_2085527 : Nat := 4983230072969 + 3 ^ 40 * 2085527 * 2
def baseEnd_2085527 : Nat := 475945675079718710987263

theorem tailTrace_2085527 : CollatzResearch.WordTrace tailWord_2085527 prefixEnd_2085527 475945675079718710987263 := by
  unfold tailWord_2085527
  simp only [CollatzResearch.WordTrace]
  refine ⟨76065418715499333499798835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50710279143666222333199223 76065418715499333499798835)
  ·
    refine ⟨114098128073249000249698253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76065418715499333499798835 114098128073249000249698253)
    ·
      refine ⟨42786798027468375093636845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114098128073249000249698253 42786798027468375093636845)
      ·
        refine ⟨16045049260300640660113817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42786798027468375093636845 16045049260300640660113817)
        ·
          refine ⟨12033786945225480495085363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16045049260300640660113817 12033786945225480495085363)
          ·
            refine ⟨18050680417838220742628045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12033786945225480495085363 18050680417838220742628045)
            ·
              refine ⟨6769005156689332778485517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18050680417838220742628045 6769005156689332778485517)
              ·
                refine ⟨2538376933758499791932069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6769005156689332778485517 2538376933758499791932069)
                ·
                  refine ⟨475945675079718710987263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538376933758499791932069 475945675079718710987263)
                  ·
                    rfl

theorem cell21_2085527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_2085527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085527 prefixEnd_2085527 := by exact prefixLift 2085527
  have htrace : WordTrace (prefixWord ++ tailWord_2085527) baseStart_2085527 baseEnd_2085527 := by
    simpa [prefixWord, tailWord_2085527, baseEnd_2085527] using wordTrace_append hprefix tailTrace_2085527
  have hstable : (prefixWord ++ tailWord_2085527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085527).length < 2 ^ (prefixWord ++ tailWord_2085527).sum := by decide
  have hdescent : baseEnd_2085527 < baseStart_2085527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085558 : List Nat := [5, 1, 3, 1, 11]
def baseStart_2085558 : Nat := 118140960795 + 2085558 * 2 ^ 59
def prefixEnd_2085558 : Nat := 4983230072969 + 3 ^ 40 * 2085558 * 2
def baseEnd_2085558 : Nat := 5875959872865056123093

theorem tailTrace_2085558 : CollatzResearch.WordTrace tailWord_2085558 prefixEnd_2085558 5875959872865056123093 := by
  unfold tailWord_2085558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754159336149189112136083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50711032918924683862784885 4754159336149189112136083)
  ·
    refine ⟨7131239004223783668204125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754159336149189112136083 7131239004223783668204125)
    ·
      refine ⟨2674214626583918875576547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7131239004223783668204125 2674214626583918875576547)
      ·
        refine ⟨4011321939875878313364821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674214626583918875576547 4011321939875878313364821)
        ·
          refine ⟨5875959872865056123093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 4011321939875878313364821 5875959872865056123093)
          ·
            rfl

theorem cell21_2085558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 11].length) (baseStart_2085558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085558 prefixEnd_2085558 := by exact prefixLift 2085558
  have htrace : WordTrace (prefixWord ++ tailWord_2085558) baseStart_2085558 baseEnd_2085558 := by
    simpa [prefixWord, tailWord_2085558, baseEnd_2085558] using wordTrace_append hprefix tailTrace_2085558
  have hstable : (prefixWord ++ tailWord_2085558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085558).length < 2 ^ (prefixWord ++ tailWord_2085558).sum := by decide
  have hdescent : baseEnd_2085558 < baseStart_2085558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085682 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2085682 : Nat := 118140960795 + 2085682 * 2 ^ 59
def prefixEnd_2085682 : Nat := 4983230072969 + 3 ^ 40 * 2085682 * 2
def baseEnd_2085682 : Nat := 475981048191472885903613

theorem tailTrace_2085682 : CollatzResearch.WordTrace tailWord_2085682 prefixEnd_2085682 475981048191472885903613 := by
  unfold tailWord_2085682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19017768007484448742922825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50714048019958529981127533 19017768007484448742922825)
  ·
    refine ⟨14263326005613336557192119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19017768007484448742922825 14263326005613336557192119)
    ·
      refine ⟨21394989008420004835788179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14263326005613336557192119 21394989008420004835788179)
      ·
        refine ⟨32092483512630007253682269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21394989008420004835788179 32092483512630007253682269)
        ·
          refine ⟨12034681317236252720130851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32092483512630007253682269 12034681317236252720130851)
          ·
            refine ⟨18052021975854379080196277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034681317236252720130851 18052021975854379080196277)
            ·
              refine ⟨1692377060236348038768401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18052021975854379080196277 1692377060236348038768401)
              ·
                refine ⟨1269282795177261029076301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692377060236348038768401 1269282795177261029076301)
                ·
                  refine ⟨475981048191472885903613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269282795177261029076301 475981048191472885903613)
                  ·
                    rfl

theorem cell21_2085682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2085682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085682 prefixEnd_2085682 := by exact prefixLift 2085682
  have htrace : WordTrace (prefixWord ++ tailWord_2085682) baseStart_2085682 baseEnd_2085682 := by
    simpa [prefixWord, tailWord_2085682, baseEnd_2085682] using wordTrace_append hprefix tailTrace_2085682
  have hstable : (prefixWord ++ tailWord_2085682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085682).length < 2 ^ (prefixWord ++ tailWord_2085682).sum := by decide
  have hdescent : baseEnd_2085682 < baseStart_2085682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085752 : List Nat := [2, 1, 2, 1, 1, 1, 1, 12]
def baseStart_2085752 : Nat := 118140960795 + 2085752 * 2 ^ 59
def prefixEnd_2085752 : Nat := 4983230072969 + 3 ^ 40 * 2085752 * 2
def baseEnd_2085752 : Nat := 158665674381722773245601

theorem tailTrace_2085752 : CollatzResearch.WordTrace tailWord_2085752 prefixEnd_2085752 158665674381722773245601 := by
  unfold tailWord_2085752
  simp only [CollatzResearch.WordTrace]
  refine ⟨38036812569842098463369755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50715750093122797951159673 38036812569842098463369755)
  ·
    refine ⟨57055218854763147695054633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38036812569842098463369755 57055218854763147695054633)
    ·
      refine ⟨42791414141072360771290975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57055218854763147695054633 42791414141072360771290975)
      ·
        refine ⟨64187121211608541156936463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42791414141072360771290975 64187121211608541156936463)
        ·
          refine ⟨96280681817412811735404695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64187121211608541156936463 96280681817412811735404695)
          ·
            refine ⟨144421022726119217603107043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96280681817412811735404695 144421022726119217603107043)
            ·
              refine ⟨216631534089178826404660565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144421022726119217603107043 216631534089178826404660565)
              ·
                refine ⟨158665674381722773245601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 216631534089178826404660565 158665674381722773245601)
                ·
                  rfl

theorem cell21_2085752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_2085752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085752 prefixEnd_2085752 := by exact prefixLift 2085752
  have htrace : WordTrace (prefixWord ++ tailWord_2085752) baseStart_2085752 baseEnd_2085752 := by
    simpa [prefixWord, tailWord_2085752, baseEnd_2085752] using wordTrace_append hprefix tailTrace_2085752
  have hstable : (prefixWord ++ tailWord_2085752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085752).length < 2 ^ (prefixWord ++ tailWord_2085752).sum := by decide
  have hdescent : baseEnd_2085752 < baseStart_2085752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085758 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2085758 : Nat := 118140960795 + 2085758 * 2 ^ 59
def prefixEnd_2085758 : Nat := 4983230072969 + 3 ^ 40 * 2085758 * 2
def baseEnd_2085758 : Nat := 475998392426913642636791

theorem tailTrace_2085758 : CollatzResearch.WordTrace tailWord_2085758 prefixEnd_2085758 475998392426913642636791 := by
  unfold tailWord_2085758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509230497207807493932241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50715895985108306634305285 9509230497207807493932241)
  ·
    refine ⟨7131922872905855620449181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9509230497207807493932241 7131922872905855620449181)
    ·
      refine ⟨2674471077339695857668443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7131922872905855620449181 2674471077339695857668443)
      ·
        refine ⟨4011706616009543786502665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674471077339695857668443 4011706616009543786502665)
        ·
          refine ⟨3008779962007157839876999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011706616009543786502665 3008779962007157839876999)
          ·
            refine ⟨4513169943010736759815499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008779962007157839876999 4513169943010736759815499)
            ·
              refine ⟨6769754914516105139723249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513169943010736759815499 6769754914516105139723249)
              ·
                refine ⟨5077316185887078854792437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769754914516105139723249 5077316185887078854792437)
                ·
                  refine ⟨475998392426913642636791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5077316185887078854792437 475998392426913642636791)
                  ·
                    rfl

theorem cell21_2085758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2085758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085758 prefixEnd_2085758 := by exact prefixLift 2085758
  have htrace : WordTrace (prefixWord ++ tailWord_2085758) baseStart_2085758 baseEnd_2085758 := by
    simpa [prefixWord, tailWord_2085758, baseEnd_2085758] using wordTrace_append hprefix tailTrace_2085758
  have hstable : (prefixWord ++ tailWord_2085758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085758).length < 2 ^ (prefixWord ++ tailWord_2085758).sum := by decide
  have hdescent : baseEnd_2085758 < baseStart_2085758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085783 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_2085783 : Nat := 118140960795 + 2085783 * 2 ^ 59
def prefixEnd_2085783 : Nat := 4983230072969 + 3 ^ 40 * 2085783 * 2
def baseEnd_2085783 : Nat := 476004097767519154720073

theorem tailTrace_2085783 : CollatzResearch.WordTrace tailWord_2085783 prefixEnd_2085783 476004097767519154720073 := by
  unfold tailWord_2085783
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074755802571889221118003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50716503868381259480745335 76074755802571889221118003)
  ·
    refine ⟨114112133703857833831677005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76074755802571889221118003 114112133703857833831677005)
    ·
      refine ⟨42792050138946687686878877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114112133703857833831677005 42792050138946687686878877)
      ·
        refine ⟨16047018802105007882579579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42792050138946687686878877 16047018802105007882579579)
        ·
          refine ⟨24070528203157511823869369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16047018802105007882579579 24070528203157511823869369)
          ·
            refine ⟨18052896152368133867902027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24070528203157511823869369 18052896152368133867902027)
            ·
              refine ⟨27079344228552200801853041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18052896152368133867902027 27079344228552200801853041)
              ·
                refine ⟨20309508171414150601389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27079344228552200801853041 20309508171414150601389781)
                ·
                  refine ⟨476004097767519154720073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20309508171414150601389781 476004097767519154720073)
                  ·
                    rfl

theorem cell21_2085783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_2085783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085783 prefixEnd_2085783 := by exact prefixLift 2085783
  have htrace : WordTrace (prefixWord ++ tailWord_2085783) baseStart_2085783 baseEnd_2085783 := by
    simpa [prefixWord, tailWord_2085783, baseEnd_2085783] using wordTrace_append hprefix tailTrace_2085783
  have hstable : (prefixWord ++ tailWord_2085783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085783).length < 2 ^ (prefixWord ++ tailWord_2085783).sum := by decide
  have hdescent : baseEnd_2085783 < baseStart_2085783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085837 : List Nat := [1, 6, 3, 1, 2, 1, 7]
def baseStart_2085837 : Nat := 118140960795 + 2085837 * 2 ^ 59
def prefixEnd_2085837 : Nat := 4983230072969 + 3 ^ 40 * 2085837 * 2
def baseEnd_2085837 : Nat := 52890713478136340091107

theorem tailTrace_2085837 : CollatzResearch.WordTrace tailWord_2085837 prefixEnd_2085837 52890713478136340091107 := by
  unfold tailWord_2085837
  simp only [CollatzResearch.WordTrace]
  refine ⟨76076725344376256443583765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50717816896250837629055843 76076725344376256443583765)
  ·
    refine ⟨3566096500517637020792989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76076725344376256443583765 3566096500517637020792989)
    ·
      refine ⟨1337286187694113882797371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3566096500517637020792989 1337286187694113882797371)
      ·
        refine ⟨2005929281541170824196057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337286187694113882797371 2005929281541170824196057)
        ·
          refine ⟨1504446961155878118147043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005929281541170824196057 1504446961155878118147043)
          ·
            refine ⟨2256670441733817177220565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504446961155878118147043 2256670441733817177220565)
            ·
              refine ⟨52890713478136340091107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2256670441733817177220565 52890713478136340091107)
              ·
                rfl

theorem cell21_2085837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 7].length) (baseStart_2085837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085837 prefixEnd_2085837 := by exact prefixLift 2085837
  have htrace : WordTrace (prefixWord ++ tailWord_2085837) baseStart_2085837 baseEnd_2085837 := by
    simpa [prefixWord, tailWord_2085837, baseEnd_2085837] using wordTrace_append hprefix tailTrace_2085837
  have hstable : (prefixWord ++ tailWord_2085837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085837).length < 2 ^ (prefixWord ++ tailWord_2085837).sum := by decide
  have hdescent : baseEnd_2085837 < baseStart_2085837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085921 : List Nat := [1, 2, 3, 2, 3, 1, 3, 6]
def baseStart_2085921 : Nat := 118140960795 + 2085921 * 2 ^ 59
def prefixEnd_2085921 : Nat := 4983230072969 + 3 ^ 40 * 2085921 * 2
def baseEnd_2085921 : Nat := 158678530415887193806597

theorem tailTrace_2085921 : CollatzResearch.WordTrace tailWord_2085921 prefixEnd_2085921 158678530415887193806597 := by
  unfold tailWord_2085921
  simp only [CollatzResearch.WordTrace]
  refine ⟨76079789076071938789641617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50719859384047959193094411 76079789076071938789641617)
  ·
    refine ⟨57059841807053954092231213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76079789076071938789641617 57059841807053954092231213)
    ·
      refine ⟨21397440677645232784586705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57059841807053954092231213 21397440677645232784586705)
      ·
        refine ⟨16048080508233924588440029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21397440677645232784586705 16048080508233924588440029)
        ·
          refine ⟨6018030190587721720665011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16048080508233924588440029 6018030190587721720665011)
          ·
            refine ⟨9027045285881582580997517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018030190587721720665011 9027045285881582580997517)
            ·
              refine ⟨3385141982205593467874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9027045285881582580997517 3385141982205593467874069)
              ·
                refine ⟨158678530415887193806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3385141982205593467874069 158678530415887193806597)
                ·
                  rfl

theorem cell21_2085921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_2085921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085921 prefixEnd_2085921 := by exact prefixLift 2085921
  have htrace : WordTrace (prefixWord ++ tailWord_2085921) baseStart_2085921 baseEnd_2085921 := by
    simpa [prefixWord, tailWord_2085921, baseEnd_2085921] using wordTrace_append hprefix tailTrace_2085921
  have hstable : (prefixWord ++ tailWord_2085921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085921).length < 2 ^ (prefixWord ++ tailWord_2085921).sum := by decide
  have hdescent : baseEnd_2085921 < baseStart_2085921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085966 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2085966 : Nat := 118140960795 + 2085966 * 2 ^ 59
def prefixEnd_2085966 : Nat := 4983230072969 + 3 ^ 40 * 2085966 * 2
def baseEnd_2085966 : Nat := 476045860860751503169699

theorem tailTrace_2085966 : CollatzResearch.WordTrace tailWord_2085966 prefixEnd_2085966 476045860860751503169699 := by
  unfold tailWord_2085966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510178795113613934378719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50720953573939274316686501 9510178795113613934378719)
  ·
    refine ⟨14265268192670420901568079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510178795113613934378719 14265268192670420901568079)
    ·
      refine ⟨21397902289005631352352119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14265268192670420901568079 21397902289005631352352119)
      ·
        refine ⟨32096853433508447028528179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21397902289005631352352119 32096853433508447028528179)
        ·
          refine ⟨48145280150262670542792269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32096853433508447028528179 48145280150262670542792269)
          ·
            refine ⟨18054480056348501453547101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48145280150262670542792269 18054480056348501453547101)
            ·
              refine ⟨6770430021130688045080163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18054480056348501453547101 6770430021130688045080163)
              ·
                refine ⟨10155645031696032067620245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770430021130688045080163 10155645031696032067620245)
                ·
                  refine ⟨476045860860751503169699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10155645031696032067620245 476045860860751503169699)
                  ·
                    rfl

theorem cell21_2085966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2085966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085966 prefixEnd_2085966 := by exact prefixLift 2085966
  have htrace : WordTrace (prefixWord ++ tailWord_2085966) baseStart_2085966 baseEnd_2085966 := by
    simpa [prefixWord, tailWord_2085966, baseEnd_2085966] using wordTrace_append hprefix tailTrace_2085966
  have hstable : (prefixWord ++ tailWord_2085966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085966).length < 2 ^ (prefixWord ++ tailWord_2085966).sum := by decide
  have hdescent : baseEnd_2085966 < baseStart_2085966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085983 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 4]
def baseStart_2085983 : Nat := 118140960795 + 2085983 * 2 ^ 59
def prefixEnd_2085983 : Nat := 4983230072969 + 3 ^ 40 * 2085983 * 2
def baseEnd_2085983 : Nat := 476049740492363251386331

theorem tailTrace_2085983 : CollatzResearch.WordTrace tailWord_2085983 prefixEnd_2085983 476049740492363251386331 := by
  unfold tailWord_2085983
  simp only [CollatzResearch.WordTrace]
  refine ⟨76082050401847323378398603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50721366934564882252265735 76082050401847323378398603)
  ·
    refine ⟨114123075602770985067597905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76082050401847323378398603 114123075602770985067597905)
    ·
      refine ⟨85592306702078238800698429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114123075602770985067597905 85592306702078238800698429)
      ·
        refine ⟨32097115013279339550261911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85592306702078238800698429 32097115013279339550261911)
        ·
          refine ⟨48145672519919009325392867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097115013279339550261911 48145672519919009325392867)
          ·
            refine ⟨72218508779878513988089301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48145672519919009325392867 72218508779878513988089301)
            ·
              refine ⟨1692621299528402671595843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72218508779878513988089301 1692621299528402671595843)
              ·
                refine ⟨2538931949292604007393765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692621299528402671595843 2538931949292604007393765)
                ·
                  refine ⟨476049740492363251386331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538931949292604007393765 476049740492363251386331)
                  ·
                    rfl

theorem cell21_2085983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_2085983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085983 prefixEnd_2085983 := by exact prefixLift 2085983
  have htrace : WordTrace (prefixWord ++ tailWord_2085983) baseStart_2085983 baseEnd_2085983 := by
    simpa [prefixWord, tailWord_2085983, baseEnd_2085983] using wordTrace_append hprefix tailTrace_2085983
  have hstable : (prefixWord ++ tailWord_2085983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085983).length < 2 ^ (prefixWord ++ tailWord_2085983).sum := by decide
  have hdescent : baseEnd_2085983 < baseStart_2085983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2085997 : List Nat := [1, 5, 1, 1, 2, 3, 1, 7]
def baseStart_2085997 : Nat := 118140960795 + 2085997 * 2 ^ 59
def prefixEnd_2085997 : Nat := 4983230072969 + 3 ^ 40 * 2085997 * 2
def baseEnd_2085997 : Nat := 158684311827700779384323

theorem tailTrace_2085997 : CollatzResearch.WordTrace tailWord_2085997 prefixEnd_2085997 158684311827700779384323 := by
  unfold tailWord_2085997
  simp only [CollatzResearch.WordTrace]
  refine ⟨76082561023796603769408245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50721707349197735846272163 76082561023796603769408245)
  ·
    refine ⟨7132740095980931603382023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76082561023796603769408245 7132740095980931603382023)
    ·
      refine ⟨10699110143971397405073035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132740095980931603382023 10699110143971397405073035)
      ·
        refine ⟨16048665215957096107609553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10699110143971397405073035 16048665215957096107609553)
        ·
          refine ⟨12036498911967822080707165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16048665215957096107609553 12036498911967822080707165)
          ·
            refine ⟨4513687091987933280265187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12036498911967822080707165 4513687091987933280265187)
            ·
              refine ⟨6770530637981899920397781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513687091987933280265187 6770530637981899920397781)
              ·
                refine ⟨158684311827700779384323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6770530637981899920397781 158684311827700779384323)
                ·
                  rfl

theorem cell21_2085997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_2085997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2085997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2085997 prefixEnd_2085997 := by exact prefixLift 2085997
  have htrace : WordTrace (prefixWord ++ tailWord_2085997) baseStart_2085997 baseEnd_2085997 := by
    simpa [prefixWord, tailWord_2085997, baseEnd_2085997] using wordTrace_append hprefix tailTrace_2085997
  have hstable : (prefixWord ++ tailWord_2085997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2085997).length < 2 ^ (prefixWord ++ tailWord_2085997).sum := by decide
  have hdescent : baseEnd_2085997 < baseStart_2085997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2085997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086028 : List Nat := [2, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_2086028 : Nat := 118140960795 + 2086028 * 2 ^ 59
def prefixEnd_2086028 : Nat := 4983230072969 + 3 ^ 40 * 2086028 * 2
def baseEnd_2086028 : Nat := 476060010105453173136239

theorem tailTrace_2086028 : CollatzResearch.WordTrace tailWord_2086028 prefixEnd_2086028 476060010105453173136239 := by
  unfold tailWord_2086028
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041845843342148031893369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50722461124456197375857825 38041845843342148031893369)
  ·
    refine ⟨28531384382506611023920027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38041845843342148031893369 28531384382506611023920027)
    ·
      refine ⟨42797076573759916535880041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28531384382506611023920027 42797076573759916535880041)
      ·
        refine ⟨32097807430319937401910031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42797076573759916535880041 32097807430319937401910031)
        ·
          refine ⟨48146711145479906102865047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097807430319937401910031 48146711145479906102865047)
          ·
            refine ⟨72220066718219859154297571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48146711145479906102865047 72220066718219859154297571)
            ·
              refine ⟨108330100077329788731446357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72220066718219859154297571 108330100077329788731446357)
              ·
                refine ⟨1269493360281208461696637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 108330100077329788731446357 1269493360281208461696637)
                ·
                  refine ⟨476060010105453173136239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269493360281208461696637 476060010105453173136239)
                  ·
                    rfl

theorem cell21_2086028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_2086028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086028 prefixEnd_2086028 := by exact prefixLift 2086028
  have htrace : WordTrace (prefixWord ++ tailWord_2086028) baseStart_2086028 baseEnd_2086028 := by
    simpa [prefixWord, tailWord_2086028, baseEnd_2086028] using wordTrace_append hprefix tailTrace_2086028
  have hstable : (prefixWord ++ tailWord_2086028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086028).length < 2 ^ (prefixWord ++ tailWord_2086028).sum := by decide
  have hdescent : baseEnd_2086028 < baseStart_2086028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086104 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_2086104 : Nat := 118140960795 + 2086104 * 2 ^ 59
def prefixEnd_2086104 : Nat := 4983230072969 + 3 ^ 40 * 2086104 * 2
def baseEnd_2086104 : Nat := 476077354340893929869417

theorem tailTrace_2086104 : CollatzResearch.WordTrace tailWord_2086104 prefixEnd_2086104 476077354340893929869417 := by
  unfold tailWord_2086104
  simp only [CollatzResearch.WordTrace]
  refine ⟨38043231817204480521776683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50724309089605974029035577 38043231817204480521776683)
  ·
    refine ⟨57064847725806720782665025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38043231817204480521776683 57064847725806720782665025)
    ·
      refine ⟨42798635794355040586998769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57064847725806720782665025 42798635794355040586998769)
      ·
        refine ⟨32098976845766280440249077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42798635794355040586998769 32098976845766280440249077)
        ·
          refine ⟨3009279079290588791273351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32098976845766280440249077 3009279079290588791273351)
          ·
            refine ⟨4513918618935883186910027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009279079290588791273351 4513918618935883186910027)
            ·
              refine ⟨6770877928403824780365041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513918618935883186910027 6770877928403824780365041)
              ·
                refine ⟨5078158446302868585273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6770877928403824780365041 5078158446302868585273781)
                ·
                  refine ⟨476077354340893929869417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078158446302868585273781 476077354340893929869417)
                  ·
                    rfl

theorem cell21_2086104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_2086104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086104 prefixEnd_2086104 := by exact prefixLift 2086104
  have htrace : WordTrace (prefixWord ++ tailWord_2086104) baseStart_2086104 baseEnd_2086104 := by
    simpa [prefixWord, tailWord_2086104, baseEnd_2086104] using wordTrace_append hprefix tailTrace_2086104
  have hstable : (prefixWord ++ tailWord_2086104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086104).length < 2 ^ (prefixWord ++ tailWord_2086104).sum := by decide
  have hdescent : baseEnd_2086104 < baseStart_2086104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086152 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_2086152 : Nat := 118140960795 + 2086152 * 2 ^ 59
def prefixEnd_2086152 : Nat := 4983230072969 + 3 ^ 40 * 2086152 * 2
def baseEnd_2086152 : Nat := 476088308594856513069319

theorem tailTrace_2086152 : CollatzResearch.WordTrace tailWord_2086152 prefixEnd_2086152 476088308594856513069319 := by
  unfold tailWord_2086152
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044107169117532620650355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50725476225490043494200473 38044107169117532620650355)
  ·
    refine ⟨57066160753676298930975533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044107169117532620650355 57066160753676298930975533)
    ·
      refine ⟨21399810282628612099115825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57066160753676298930975533 21399810282628612099115825)
      ·
        refine ⟨16049857711971459074336869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21399810282628612099115825 16049857711971459074336869)
        ·
          refine ⟨3009348320994648576438163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16049857711971459074336869 3009348320994648576438163)
          ·
            refine ⟨4514022481491972864657245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009348320994648576438163 4514022481491972864657245)
            ·
              refine ⟨1692758430559489824246467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4514022481491972864657245 1692758430559489824246467)
              ·
                refine ⟨2539137645839234736369701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1692758430559489824246467 2539137645839234736369701)
                ·
                  refine ⟨476088308594856513069319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539137645839234736369701 476088308594856513069319)
                  ·
                    rfl

theorem cell21_2086152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_2086152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086152 prefixEnd_2086152 := by exact prefixLift 2086152
  have htrace : WordTrace (prefixWord ++ tailWord_2086152) baseStart_2086152 baseEnd_2086152 := by
    simpa [prefixWord, tailWord_2086152, baseEnd_2086152] using wordTrace_append hprefix tailTrace_2086152
  have hstable : (prefixWord ++ tailWord_2086152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086152).length < 2 ^ (prefixWord ++ tailWord_2086152).sum := by decide
  have hdescent : baseEnd_2086152 < baseStart_2086152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086194 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2086194 : Nat := 118140960795 + 2086194 * 2 ^ 59
def prefixEnd_2086194 : Nat := 4983230072969 + 3 ^ 40 * 2086194 * 2
def baseEnd_2086194 : Nat := 476097893567073773369233

theorem tailTrace_2086194 : CollatzResearch.WordTrace tailWord_2086194 prefixEnd_2086194 476097893567073773369233 := by
  unfold tailWord_2086194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022436551020726603582409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50726497469388604276219757 19022436551020726603582409)
  ·
    refine ⟨14266827413265544952686807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19022436551020726603582409 14266827413265544952686807)
    ·
      refine ⟨21400241119898317429030211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266827413265544952686807 21400241119898317429030211)
      ·
        refine ⟨32100361679847476143545317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21400241119898317429030211 32100361679847476143545317)
        ·
          refine ⟨6018817814971401776914747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32100361679847476143545317 6018817814971401776914747)
          ·
            refine ⟨9028226722457102665372121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018817814971401776914747 9028226722457102665372121)
            ·
              refine ⟨6771170041842826999029091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028226722457102665372121 6771170041842826999029091)
              ·
                refine ⟨10156755062764240498543637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771170041842826999029091 10156755062764240498543637)
                ·
                  refine ⟨476097893567073773369233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10156755062764240498543637 476097893567073773369233)
                  ·
                    rfl

theorem cell21_2086194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2086194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086194 prefixEnd_2086194 := by exact prefixLift 2086194
  have htrace : WordTrace (prefixWord ++ tailWord_2086194) baseStart_2086194 baseEnd_2086194 := by
    simpa [prefixWord, tailWord_2086194, baseEnd_2086194] using wordTrace_append hprefix tailTrace_2086194
  have hstable : (prefixWord ++ tailWord_2086194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086194).length < 2 ^ (prefixWord ++ tailWord_2086194).sum := by decide
  have hdescent : baseEnd_2086194 < baseStart_2086194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086208 : List Nat := [2, 1, 1, 2, 2, 1, 6, 6]
def baseStart_2086208 : Nat := 118140960795 + 2086208 * 2 ^ 59
def prefixEnd_2086208 : Nat := 4983230072969 + 3 ^ 40 * 2086208 * 2
def baseEnd_2086208 : Nat := 158700362852604286711957

theorem tailTrace_2086208 : CollatzResearch.WordTrace tailWord_2086208 prefixEnd_2086208 158700362852604286711957 := by
  unfold tailWord_2086208
  simp only [CollatzResearch.WordTrace]
  refine ⟨38045128413016093402669639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50726837884021457870226185 38045128413016093402669639)
  ·
    refine ⟨57067692619524140104004459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38045128413016093402669639 57067692619524140104004459)
    ·
      refine ⟨85601538929286210156006689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57067692619524140104004459 85601538929286210156006689)
      ·
        refine ⟨64201154196964657617005017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85601538929286210156006689 64201154196964657617005017)
        ·
          refine ⟨48150865647723493212753763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64201154196964657617005017 48150865647723493212753763)
          ·
            refine ⟨72226298471585239819130645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48150865647723493212753763 72226298471585239819130645)
            ·
              refine ⟨3385607740855558116521749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72226298471585239819130645 3385607740855558116521749)
              ·
                refine ⟨158700362852604286711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3385607740855558116521749 158700362852604286711957)
                ·
                  rfl

theorem cell21_2086208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_2086208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086208 prefixEnd_2086208 := by exact prefixLift 2086208
  have htrace : WordTrace (prefixWord ++ tailWord_2086208) baseStart_2086208 baseEnd_2086208 := by
    simpa [prefixWord, tailWord_2086208, baseEnd_2086208] using wordTrace_append hprefix tailTrace_2086208
  have hstable : (prefixWord ++ tailWord_2086208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086208).length < 2 ^ (prefixWord ++ tailWord_2086208).sum := by decide
  have hdescent : baseEnd_2086208 < baseStart_2086208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086256 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_2086256 : Nat := 118140960795 + 2086256 * 2 ^ 59
def prefixEnd_2086256 : Nat := 4983230072969 + 3 ^ 40 * 2086256 * 2
def baseEnd_2086256 : Nat := 476112042811775443335773

theorem tailTrace_2086256 : CollatzResearch.WordTrace tailWord_2086256 prefixEnd_2086256 476112042811775443335773 := by
  unfold tailWord_2086256
  simp only [CollatzResearch.WordTrace]
  refine ⟨38046003764929145501543311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50728005019905527335391081 38046003764929145501543311)
  ·
    refine ⟨57069005647393718252314967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38046003764929145501543311 57069005647393718252314967)
    ·
      refine ⟨85603508471090577378472451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57069005647393718252314967 85603508471090577378472451)
      ·
        refine ⟨128405262706635866067708677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85603508471090577378472451 128405262706635866067708677)
        ·
          refine ⟨24075986757494224887695377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128405262706635866067708677 24075986757494224887695377)
          ·
            refine ⟨18056990068120668665771533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24075986757494224887695377 18056990068120668665771533)
            ·
              refine ⟨6771371275545250749664325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18056990068120668665771533 6771371275545250749664325)
              ·
                refine ⟨1269632114164734515562061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6771371275545250749664325 1269632114164734515562061)
                ·
                  refine ⟨476112042811775443335773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269632114164734515562061 476112042811775443335773)
                  ·
                    rfl

theorem cell21_2086256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_2086256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086256 prefixEnd_2086256 := by exact prefixLift 2086256
  have htrace : WordTrace (prefixWord ++ tailWord_2086256) baseStart_2086256 baseEnd_2086256 := by
    simpa [prefixWord, tailWord_2086256, baseEnd_2086256] using wordTrace_append hprefix tailTrace_2086256
  have hstable : (prefixWord ++ tailWord_2086256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086256).length < 2 ^ (prefixWord ++ tailWord_2086256).sum := by decide
  have hdescent : baseEnd_2086256 < baseStart_2086256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086419 : List Nat := [1, 1, 1, 2, 1, 15]
def baseStart_2086419 : Nat := 118140960795 + 2086419 * 2 ^ 59
def prefixEnd_2086419 : Nat := 4983230072969 + 3 ^ 40 * 2086419 * 2
def baseEnd_2086419 : Nat := 17635157097500866004399

theorem tailTrace_2086419 : CollatzResearch.WordTrace tailWord_2086419 prefixEnd_2086419 17635157097500866004399 := by
  unfold tailWord_2086419
  simp only [CollatzResearch.WordTrace]
  refine ⟨76097952628267769841270311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50731968418845179894180207 76097952628267769841270311)
  ·
    refine ⟨114146928942401654761905467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76097952628267769841270311 114146928942401654761905467)
    ·
      refine ⟨171220393413602482142858201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114146928942401654761905467 171220393413602482142858201)
      ·
        refine ⟨128415295060201861607143651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171220393413602482142858201 128415295060201861607143651)
        ·
          refine ⟨192622942590302792410715477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128415295060201861607143651 192622942590302792410715477)
          ·
            refine ⟨17635157097500866004399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 192622942590302792410715477 17635157097500866004399)
            ·
              rfl

theorem cell21_2086419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 15].length) (baseStart_2086419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086419 prefixEnd_2086419 := by exact prefixLift 2086419
  have htrace : WordTrace (prefixWord ++ tailWord_2086419) baseStart_2086419 baseEnd_2086419 := by
    simpa [prefixWord, tailWord_2086419, baseEnd_2086419] using wordTrace_append hprefix tailTrace_2086419
  have hstable : (prefixWord ++ tailWord_2086419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086419).length < 2 ^ (prefixWord ++ tailWord_2086419).sum := by decide
  have hdescent : baseEnd_2086419 < baseStart_2086419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086453 : List Nat := [1, 3, 3, 1, 1, 4, 3, 5]
def baseStart_2086453 : Nat := 118140960795 + 2086453 * 2 ^ 59
def prefixEnd_2086453 : Nat := 4983230072969 + 3 ^ 40 * 2086453 * 2
def baseEnd_2086453 : Nat := 158719000298582292850679

theorem tailTrace_2086453 : CollatzResearch.WordTrace tailWord_2086453 prefixEnd_2086453 158719000298582292850679 := by
  unfold tailWord_2086453
  simp only [CollatzResearch.WordTrace]
  refine ⟨76099192710144593648008013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50732795140096395765338675 76099192710144593648008013)
  ·
    refine ⟨28537197266304222618003005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76099192710144593648008013 28537197266304222618003005)
    ·
      refine ⟨10701448974864083481751127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28537197266304222618003005 10701448974864083481751127)
      ·
        refine ⟨16052173462296125222626691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701448974864083481751127 16052173462296125222626691)
        ·
          refine ⟨24078260193444187833940037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052173462296125222626691 24078260193444187833940037)
          ·
            refine ⟨4514673786270785218863757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24078260193444187833940037 4514673786270785218863757)
            ·
              refine ⟨1693002669851544457073909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4514673786270785218863757 1693002669851544457073909)
              ·
                refine ⟨158719000298582292850679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1693002669851544457073909 158719000298582292850679)
                ·
                  rfl

theorem cell21_2086453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].length) (baseStart_2086453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086453 prefixEnd_2086453 := by exact prefixLift 2086453
  have htrace : WordTrace (prefixWord ++ tailWord_2086453) baseStart_2086453 baseEnd_2086453 := by
    simpa [prefixWord, tailWord_2086453, baseEnd_2086453] using wordTrace_append hprefix tailTrace_2086453
  have hstable : (prefixWord ++ tailWord_2086453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086453).length < 2 ^ (prefixWord ++ tailWord_2086453).sum := by decide
  have hdescent : baseEnd_2086453 < baseStart_2086453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086470 : List Nat := [6, 1, 1, 1, 3, 1, 8]
def baseStart_2086470 : Nat := 118140960795 + 2086470 * 2 ^ 59
def prefixEnd_2086470 : Nat := 4983230072969 + 3 ^ 40 * 2086470 * 2
def baseEnd_2086470 : Nat := 52906764503039847418741

theorem tailTrace_2086470 : CollatzResearch.WordTrace tailWord_2086470 prefixEnd_2086470 52906764503039847418741 := by
  unfold tailWord_2086470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378119148471343923480527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50733208500722003700917909 2378119148471343923480527)
  ·
    refine ⟨3567178722707015885220791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378119148471343923480527 3567178722707015885220791)
    ·
      refine ⟨5350768084060523827831187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567178722707015885220791 5350768084060523827831187)
      ·
        refine ⟨8026152126090785741746781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350768084060523827831187 8026152126090785741746781)
        ·
          refine ⟨3009807047284044653155043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026152126090785741746781 3009807047284044653155043)
          ·
            refine ⟨4514710570926066979732565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009807047284044653155043 4514710570926066979732565)
            ·
              refine ⟨52906764503039847418741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4514710570926066979732565 52906764503039847418741)
              ·
                rfl

theorem cell21_2086470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 8].length) (baseStart_2086470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086470 prefixEnd_2086470 := by exact prefixLift 2086470
  have htrace : WordTrace (prefixWord ++ tailWord_2086470) baseStart_2086470 baseEnd_2086470 := by
    simpa [prefixWord, tailWord_2086470, baseEnd_2086470] using wordTrace_append hprefix tailTrace_2086470
  have hstable : (prefixWord ++ tailWord_2086470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086470).length < 2 ^ (prefixWord ++ tailWord_2086470).sum := by decide
  have hdescent : baseEnd_2086470 < baseStart_2086470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086481 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_2086481 : Nat := 118140960795 + 2086481 * 2 ^ 59
def prefixEnd_2086481 : Nat := 4983230072969 + 3 ^ 40 * 2086481 * 2
def baseEnd_2086481 : Nat := 476163390877225052085313

theorem tailTrace_2086481 : CollatzResearch.WordTrace tailWord_2086481 prefixEnd_2086481 476163390877225052085313 := by
  unfold tailWord_2086481
  simp only [CollatzResearch.WordTrace]
  refine ⟨76100213954043154430027297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50733475969362102953351531 76100213954043154430027297)
  ·
    refine ⟨57075160465532365822520473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76100213954043154430027297 57075160465532365822520473)
    ·
      refine ⟨42806370349149274366890355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57075160465532365822520473 42806370349149274366890355)
      ·
        refine ⟨64209555523723911550335533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42806370349149274366890355 64209555523723911550335533)
        ·
          refine ⟨24078583321396466831375825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64209555523723911550335533 24078583321396466831375825)
          ·
            refine ⟨18058937491047350123531869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24078583321396466831375825 18058937491047350123531869)
            ·
              refine ⟨6772101559142756296324451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18058937491047350123531869 6772101559142756296324451)
              ·
                refine ⟨10158152338714134444486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772101559142756296324451 10158152338714134444486677)
                ·
                  refine ⟨476163390877225052085313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10158152338714134444486677 476163390877225052085313)
                  ·
                    rfl

theorem cell21_2086481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_2086481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086481 prefixEnd_2086481 := by exact prefixLift 2086481
  have htrace : WordTrace (prefixWord ++ tailWord_2086481) baseStart_2086481 baseEnd_2086481 := by
    simpa [prefixWord, tailWord_2086481, baseEnd_2086481] using wordTrace_append hprefix tailTrace_2086481
  have hstable : (prefixWord ++ tailWord_2086481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086481).length < 2 ^ (prefixWord ++ tailWord_2086481).sum := by decide
  have hdescent : baseEnd_2086481 < baseStart_2086481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086484 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_2086484 : Nat := 118140960795 + 2086484 * 2 ^ 59
def prefixEnd_2086484 : Nat := 4983230072969 + 3 ^ 40 * 2086484 * 2
def baseEnd_2086484 : Nat := 476164075518097713535307

theorem tailTrace_2086484 : CollatzResearch.WordTrace tailWord_2086484 prefixEnd_2086484 476164075518097713535307 := by
  unfold tailWord_2086484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38050161686516142971193253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50733548915354857294924337 38050161686516142971193253)
  ·
    refine ⟨7134405316221776807098735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38050161686516142971193253 7134405316221776807098735)
    ·
      refine ⟨10701607974332665210648103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134405316221776807098735 10701607974332665210648103)
      ·
        refine ⟨16052411961498997815972155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701607974332665210648103 16052411961498997815972155)
        ·
          refine ⟨24078617942248496723958233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16052411961498997815972155 24078617942248496723958233)
          ·
            refine ⟨18058963456686372542968675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24078617942248496723958233 18058963456686372542968675)
            ·
              refine ⟨27088445185029558814453013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18058963456686372542968675 27088445185029558814453013)
              ·
                refine ⟨1269770868048260569427485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27088445185029558814453013 1269770868048260569427485)
                ·
                  refine ⟨476164075518097713535307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269770868048260569427485 476164075518097713535307)
                  ·
                    rfl

theorem cell21_2086484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_2086484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086484 prefixEnd_2086484 := by exact prefixLift 2086484
  have htrace : WordTrace (prefixWord ++ tailWord_2086484) baseStart_2086484 baseEnd_2086484 := by
    simpa [prefixWord, tailWord_2086484, baseEnd_2086484] using wordTrace_append hprefix tailTrace_2086484
  have hstable : (prefixWord ++ tailWord_2086484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086484).length < 2 ^ (prefixWord ++ tailWord_2086484).sum := by decide
  have hdescent : baseEnd_2086484 < baseStart_2086484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086512 : List Nat := [2, 1, 1, 1, 6, 2, 1, 7]
def baseStart_2086512 : Nat := 118140960795 + 2086512 * 2 ^ 59
def prefixEnd_2086512 : Nat := 4983230072969 + 3 ^ 40 * 2086512 * 2
def baseEnd_2086512 : Nat := 158723488499858629022861

theorem tailTrace_2086512 : CollatzResearch.WordTrace tailWord_2086512 prefixEnd_2086512 158723488499858629022861 := by
  unfold tailWord_2086512
  simp only [CollatzResearch.WordTrace]
  refine ⟨38050672308465423362202895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50734229744620564482937193 38050672308465423362202895)
  ·
    refine ⟨57076008462698135043304343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38050672308465423362202895 57076008462698135043304343)
    ·
      refine ⟨85614012694047202564956515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57076008462698135043304343 85614012694047202564956515)
      ·
        refine ⟨128421019041070803847434773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85614012694047202564956515 128421019041070803847434773)
        ·
          refine ⟨6019735267550193930348505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128421019041070803847434773 6019735267550193930348505)
          ·
            refine ⟨4514801450662645447761379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019735267550193930348505 4514801450662645447761379)
            ·
              refine ⟨6772202175993968171642069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514801450662645447761379 6772202175993968171642069)
              ·
                refine ⟨158723488499858629022861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6772202175993968171642069 158723488499858629022861)
                ·
                  rfl

theorem cell21_2086512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_2086512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086512 prefixEnd_2086512 := by exact prefixLift 2086512
  have htrace : WordTrace (prefixWord ++ tailWord_2086512) baseStart_2086512 baseEnd_2086512 := by
    simpa [prefixWord, tailWord_2086512, baseEnd_2086512] using wordTrace_append hprefix tailTrace_2086512
  have hstable : (prefixWord ++ tailWord_2086512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086512).length < 2 ^ (prefixWord ++ tailWord_2086512).sum := by decide
  have hdescent : baseEnd_2086512 < baseStart_2086512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086518 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2086518 : Nat := 118140960795 + 2086518 * 2 ^ 59
def prefixEnd_2086518 : Nat := 4983230072969 + 3 ^ 40 * 2086518 * 2
def baseEnd_2086518 : Nat := 476171834781321209968571

theorem tailTrace_2086518 : CollatzResearch.WordTrace tailWord_2086518 prefixEnd_2086518 476171834781321209968571 := by
  unfold tailWord_2086518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756347715931819359320263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50734375636606073166082805 4756347715931819359320263)
  ·
    refine ⟨7134521573897729038980395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756347715931819359320263 7134521573897729038980395)
    ·
      refine ⟨10701782360846593558470593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7134521573897729038980395 10701782360846593558470593)
      ·
        refine ⟨8026336770634945168852945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10701782360846593558470593 8026336770634945168852945)
        ·
          refine ⟨6019752577976208876639709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8026336770634945168852945 6019752577976208876639709)
          ·
            refine ⟨2257407216741078328739891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6019752577976208876639709 2257407216741078328739891)
            ·
              refine ⟨3386110825111617493109837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257407216741078328739891 3386110825111617493109837)
              ·
                refine ⟨1269791559416856559916189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3386110825111617493109837 1269791559416856559916189)
                ·
                  refine ⟨476171834781321209968571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269791559416856559916189 476171834781321209968571)
                  ·
                    rfl

theorem cell21_2086518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2086518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086518 prefixEnd_2086518 := by exact prefixLift 2086518
  have htrace : WordTrace (prefixWord ++ tailWord_2086518) baseStart_2086518 baseEnd_2086518 := by
    simpa [prefixWord, tailWord_2086518, baseEnd_2086518] using wordTrace_append hprefix tailTrace_2086518
  have hstable : (prefixWord ++ tailWord_2086518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086518).length < 2 ^ (prefixWord ++ tailWord_2086518).sum := by decide
  have hdescent : baseEnd_2086518 < baseStart_2086518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086723 : List Nat := [1, 1, 1, 3, 1, 5, 1, 8]
def baseStart_2086723 : Nat := 118140960795 + 2086723 * 2 ^ 59
def prefixEnd_2086723 : Nat := 4983230072969 + 3 ^ 40 * 2086723 * 2
def baseEnd_2086723 : Nat := 158739539524762136350495

theorem tailTrace_2086723 : CollatzResearch.WordTrace tailWord_2086723 prefixEnd_2086723 158739539524762136350495 := by
  unfold tailWord_2086723
  simp only [CollatzResearch.WordTrace]
  refine ⟨76109040419166429760336823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50739360279444286506891215 76109040419166429760336823)
  ·
    refine ⟨114163560628749644640505235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76109040419166429760336823 114163560628749644640505235)
    ·
      refine ⟨171245340943124466960757853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114163560628749644640505235 171245340943124466960757853)
      ·
        refine ⟨64217002853671675110284195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171245340943124466960757853 64217002853671675110284195)
        ·
          refine ⟨96325504280507512665426293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64217002853671675110284195 96325504280507512665426293)
          ·
            refine ⟨9030516026297579312383715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96325504280507512665426293 9030516026297579312383715)
            ·
              refine ⟨13545774039446368968575573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030516026297579312383715 13545774039446368968575573)
              ·
                refine ⟨158739539524762136350495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13545774039446368968575573 158739539524762136350495)
                ·
                  rfl

theorem cell21_2086723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_2086723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086723 prefixEnd_2086723 := by exact prefixLift 2086723
  have htrace : WordTrace (prefixWord ++ tailWord_2086723) baseStart_2086723 baseEnd_2086723 := by
    simpa [prefixWord, tailWord_2086723, baseEnd_2086723] using wordTrace_append hprefix tailTrace_2086723
  have hstable : (prefixWord ++ tailWord_2086723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086723).length < 2 ^ (prefixWord ++ tailWord_2086723).sum := by decide
  have hdescent : baseEnd_2086723 < baseStart_2086723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086740 : List Nat := [2, 4, 1, 1, 3, 1, 2, 7]
def baseStart_2086740 : Nat := 118140960795 + 2086740 * 2 ^ 59
def prefixEnd_2086740 : Nat := 4983230072969 + 3 ^ 40 * 2086740 * 2
def baseEnd_2086740 : Nat := 158740832735299385756039

theorem tailTrace_2086740 : CollatzResearch.WordTrace tailWord_2086740 prefixEnd_2086740 158740832735299385756039 := by
  unfold tailWord_2086740
  simp only [CollatzResearch.WordTrace]
  refine ⟨38054830230052420831852837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50739773640069894442470449 38054830230052420831852837)
  ·
    refine ⟨7135280668134828905972407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38054830230052420831852837 7135280668134828905972407)
    ·
      refine ⟨10702921002202243358958611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135280668134828905972407 10702921002202243358958611)
      ·
        refine ⟨16054381503303365038437917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10702921002202243358958611 16054381503303365038437917)
        ·
          refine ⟨6020393063738761889414219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16054381503303365038437917 6020393063738761889414219)
          ·
            refine ⟨9030589595608142834121329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020393063738761889414219 9030589595608142834121329)
            ·
              refine ⟨6772942196706107125590997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030589595608142834121329 6772942196706107125590997)
              ·
                refine ⟨158740832735299385756039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6772942196706107125590997 158740832735299385756039)
                ·
                  rfl

theorem cell21_2086740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_2086740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086740 prefixEnd_2086740 := by exact prefixLift 2086740
  have htrace : WordTrace (prefixWord ++ tailWord_2086740) baseStart_2086740 baseEnd_2086740 := by
    simpa [prefixWord, tailWord_2086740, baseEnd_2086740] using wordTrace_append hprefix tailTrace_2086740
  have hstable : (prefixWord ++ tailWord_2086740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086740).length < 2 ^ (prefixWord ++ tailWord_2086740).sum := by decide
  have hdescent : baseEnd_2086740 < baseStart_2086740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086774 : List Nat := [5, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2086774 : Nat := 118140960795 + 2086774 * 2 ^ 59
def prefixEnd_2086774 : Nat := 4983230072969 + 3 ^ 40 * 2086774 * 2
def baseEnd_2086774 : Nat := 158743419156373884567127

theorem tailTrace_2086774 : CollatzResearch.WordTrace tailWord_2086774 prefixEnd_2086774 158743419156373884567127 := by
  unfold tailWord_2086774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756931283873854091902711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50740600361321110313628917 4756931283873854091902711)
  ·
    refine ⟨7135396925810781137854067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4756931283873854091902711 7135396925810781137854067)
    ·
      refine ⟨10703095388716171706781101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7135396925810781137854067 10703095388716171706781101)
      ·
        refine ⟨4013660770768564390042913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10703095388716171706781101 4013660770768564390042913)
        ·
          refine ⟨3010245578076423292532185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4013660770768564390042913 3010245578076423292532185)
          ·
            refine ⟨2257684183557317469399139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010245578076423292532185 2257684183557317469399139)
            ·
              refine ⟨3386526275335976204098709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257684183557317469399139 3386526275335976204098709)
              ·
                refine ⟨158743419156373884567127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3386526275335976204098709 158743419156373884567127)
                ·
                  rfl

theorem cell21_2086774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2086774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086774 prefixEnd_2086774 := by exact prefixLift 2086774
  have htrace : WordTrace (prefixWord ++ tailWord_2086774) baseStart_2086774 baseEnd_2086774 := by
    simpa [prefixWord, tailWord_2086774, baseEnd_2086774] using wordTrace_append hprefix tailTrace_2086774
  have hstable : (prefixWord ++ tailWord_2086774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086774).length < 2 ^ (prefixWord ++ tailWord_2086774).sum := by decide
  have hdescent : baseEnd_2086774 < baseStart_2086774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086923 : List Nat := [1, 1, 1, 1, 6, 1, 2, 5, 3]
def baseStart_2086923 : Nat := 118140960795 + 2086923 * 2 ^ 59
def prefixEnd_2086923 : Nat := 4983230072969 + 3 ^ 40 * 2086923 * 2
def baseEnd_2086923 : Nat := 476264261299130505717743

theorem tailTrace_2086923 : CollatzResearch.WordTrace tailWord_2086923 prefixEnd_2086923 476264261299130505717743 := by
  unfold tailWord_2086923
  simp only [CollatzResearch.WordTrace]
  refine ⟨76116335018441863917617423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50744223345627909278411615 76116335018441863917617423)
  ·
    refine ⟨114174502527662795876426135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76116335018441863917617423 114174502527662795876426135)
    ·
      refine ⟨171261753791494193814639203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114174502527662795876426135 171261753791494193814639203)
      ·
        refine ⟨256892630687241290721958805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171261753791494193814639203 256892630687241290721958805)
        ·
          refine ⟨12041842063464435502591819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256892630687241290721958805 12041842063464435502591819)
          ·
            refine ⟨18062763095196653253887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041842063464435502591819 18062763095196653253887729)
            ·
              refine ⟨13547072321397489940415797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18062763095196653253887729 13547072321397489940415797)
              ·
                refine ⟨1270038030131014681913981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13547072321397489940415797 1270038030131014681913981)
                ·
                  refine ⟨476264261299130505717743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270038030131014681913981 476264261299130505717743)
                  ·
                    rfl

theorem cell21_2086923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].length) (baseStart_2086923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086923 prefixEnd_2086923 := by exact prefixLift 2086923
  have htrace : WordTrace (prefixWord ++ tailWord_2086923) baseStart_2086923 baseEnd_2086923 := by
    simpa [prefixWord, tailWord_2086923, baseEnd_2086923] using wordTrace_append hprefix tailTrace_2086923
  have hstable : (prefixWord ++ tailWord_2086923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086923).length < 2 ^ (prefixWord ++ tailWord_2086923).sum := by decide
  have hdescent : baseEnd_2086923 < baseStart_2086923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086932 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2086932 : Nat := 118140960795 + 2086932 * 2 ^ 59
def prefixEnd_2086932 : Nat := 4983230072969 + 3 ^ 40 * 2086932 * 2
def baseEnd_2086932 : Nat := 476266315221748490067725

theorem tailTrace_2086932 : CollatzResearch.WordTrace tailWord_2086932 prefixEnd_2086932 476266315221748490067725 := by
  unfold tailWord_2086932
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058331637704629227347525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50744442183606172303130033 38058331637704629227347525)
  ·
    refine ⟨7135937182069617980127661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38058331637704629227347525 7135937182069617980127661)
    ·
      refine ⟨2675976443276106742547873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7135937182069617980127661 2675976443276106742547873)
      ·
        refine ⟨2006982332457080056910905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675976443276106742547873 2006982332457080056910905)
        ·
          refine ⟨1505236749342810042683179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2006982332457080056910905 1505236749342810042683179)
          ·
            refine ⟨2257855124014215064024769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505236749342810042683179 2257855124014215064024769)
            ·
              refine ⟨1693391343010661298018577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257855124014215064024769 1693391343010661298018577)
              ·
                refine ⟨1270043507257995973513933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693391343010661298018577 1270043507257995973513933)
                ·
                  refine ⟨476266315221748490067725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270043507257995973513933 476266315221748490067725)
                  ·
                    rfl

theorem cell21_2086932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2086932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086932 prefixEnd_2086932 := by exact prefixLift 2086932
  have htrace : WordTrace (prefixWord ++ tailWord_2086932) baseStart_2086932 baseEnd_2086932 := by
    simpa [prefixWord, tailWord_2086932, baseEnd_2086932] using wordTrace_append hprefix tailTrace_2086932
  have hstable : (prefixWord ++ tailWord_2086932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086932).length < 2 ^ (prefixWord ++ tailWord_2086932).sum := by decide
  have hdescent : baseEnd_2086932 < baseStart_2086932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086940 : List Nat := [2, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_2086940 : Nat := 118140960795 + 2086940 * 2 ^ 59
def prefixEnd_2086940 : Nat := 4983230072969 + 3 ^ 40 * 2086940 * 2
def baseEnd_2086940 : Nat := 476268140930742253934375

theorem tailTrace_2086940 : CollatzResearch.WordTrace tailWord_2086940 prefixEnd_2086940 476268140930742253934375 := by
  unfold tailWord_2086940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058477529690137910493137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50744636706253517213990849 38058477529690137910493137)
  ·
    refine ⟨28543858147267603432869853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38058477529690137910493137 28543858147267603432869853)
    ·
      refine ⟨10703946805225351287326195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28543858147267603432869853 10703946805225351287326195)
      ·
        refine ⟨16055920207838026930989293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703946805225351287326195 16055920207838026930989293)
        ·
          refine ⟨6020970077939260099120985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16055920207838026930989293 6020970077939260099120985)
          ·
            refine ⟨4515727558454445074340739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6020970077939260099120985 4515727558454445074340739)
            ·
              refine ⟨6773591337681667611511109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515727558454445074340739 6773591337681667611511109)
              ·
                refine ⟨1270048375815312677158333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6773591337681667611511109 1270048375815312677158333)
                ·
                  refine ⟨476268140930742253934375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270048375815312677158333 476268140930742253934375)
                  ·
                    rfl

theorem cell21_2086940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_2086940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086940 prefixEnd_2086940 := by exact prefixLift 2086940
  have htrace : WordTrace (prefixWord ++ tailWord_2086940) baseStart_2086940 baseEnd_2086940 := by
    simpa [prefixWord, tailWord_2086940, baseEnd_2086940] using wordTrace_append hprefix tailTrace_2086940
  have hstable : (prefixWord ++ tailWord_2086940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086940).length < 2 ^ (prefixWord ++ tailWord_2086940).sum := by decide
  have hdescent : baseEnd_2086940 < baseStart_2086940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086954 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_2086954 : Nat := 118140960795 + 2086954 * 2 ^ 59
def prefixEnd_2086954 : Nat := 4983230072969 + 3 ^ 40 * 2086954 * 2
def baseEnd_2086954 : Nat := 476271335921481340701013

theorem tailTrace_2086954 : CollatzResearch.WordTrace tailWord_2086954 prefixEnd_2086954 476271335921481340701013 := by
  unfold tailWord_2086954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029366420332389052998979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50744977120886370807997277 19029366420332389052998979)
  ·
    refine ⟨28544049630498583579498469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19029366420332389052998979 28544049630498583579498469)
    ·
      refine ⟨5352009305718484421155963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28544049630498583579498469 5352009305718484421155963)
      ·
        refine ⟨8028013958577726631733945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352009305718484421155963 8028013958577726631733945)
        ·
          refine ⟨6021010468933294973800459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8028013958577726631733945 6021010468933294973800459)
          ·
            refine ⟨9031515703399942460700689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021010468933294973800459 9031515703399942460700689)
            ·
              refine ⟨6773636777549956845525517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9031515703399942460700689 6773636777549956845525517)
              ·
                refine ⟨2540113791581233817072069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6773636777549956845525517 2540113791581233817072069)
                ·
                  refine ⟨476271335921481340701013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540113791581233817072069 476271335921481340701013)
                  ·
                    rfl

theorem cell21_2086954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_2086954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086954 prefixEnd_2086954 := by exact prefixLift 2086954
  have htrace : WordTrace (prefixWord ++ tailWord_2086954) baseStart_2086954 baseEnd_2086954 := by
    simpa [prefixWord, tailWord_2086954, baseEnd_2086954] using wordTrace_append hprefix tailTrace_2086954
  have hstable : (prefixWord ++ tailWord_2086954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086954).length < 2 ^ (prefixWord ++ tailWord_2086954).sum := by decide
  have hdescent : baseEnd_2086954 < baseStart_2086954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2086999 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 3]
def baseStart_2086999 : Nat := 118140960795 + 2086999 * 2 ^ 59
def prefixEnd_2086999 : Nat := 4983230072969 + 3 ^ 40 * 2086999 * 2
def baseEnd_2086999 : Nat := 476281605534571262450921

theorem tailTrace_2086999 : CollatzResearch.WordTrace tailWord_2086999 prefixEnd_2086999 476281605534571262450921 := by
  unfold tailWord_2086999
  simp only [CollatzResearch.WordTrace]
  refine ⟨76119106966166528897384051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50746071310777685931589367 76119106966166528897384051)
  ·
    refine ⟨114178660449249793346076077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76119106966166528897384051 114178660449249793346076077)
    ·
      refine ⟨42816997668468672504778529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114178660449249793346076077 42816997668468672504778529)
      ·
        refine ⟨32112748251351504378583897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42816997668468672504778529 32112748251351504378583897)
        ·
          refine ⟨24084561188513628283937923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32112748251351504378583897 24084561188513628283937923)
          ·
            refine ⟨36126841782770442425906885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24084561188513628283937923 36126841782770442425906885)
            ·
              refine ⟨6773782834269457954857541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36126841782770442425906885 6773782834269457954857541)
              ·
                refine ⟨1270084281425523366535789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6773782834269457954857541 1270084281425523366535789)
                ·
                  refine ⟨476281605534571262450921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270084281425523366535789 476281605534571262450921)
                  ·
                    rfl

theorem cell21_2086999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 3].length) (baseStart_2086999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2086999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2086999 prefixEnd_2086999 := by exact prefixLift 2086999
  have htrace : WordTrace (prefixWord ++ tailWord_2086999) baseStart_2086999 baseEnd_2086999 := by
    simpa [prefixWord, tailWord_2086999, baseEnd_2086999] using wordTrace_append hprefix tailTrace_2086999
  have hstable : (prefixWord ++ tailWord_2086999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2086999).length < 2 ^ (prefixWord ++ tailWord_2086999).sum := by decide
  have hdescent : baseEnd_2086999 < baseStart_2086999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2086999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087064 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_2087064 : Nat := 118140960795 + 2087064 * 2 ^ 59
def prefixEnd_2087064 : Nat := 4983230072969 + 3 ^ 40 * 2087064 * 2
def baseEnd_2087064 : Nat := 476296439420145593867455

theorem tailTrace_2087064 : CollatzResearch.WordTrace tailWord_2087064 prefixEnd_2087064 476296439420145593867455 := by
  unfold tailWord_2087064
  simp only [CollatzResearch.WordTrace]
  refine ⟨38060738855465522499250123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50747651807287363332333497 38060738855465522499250123)
  ·
    refine ⟨57091108283198283748875185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38060738855465522499250123 57091108283198283748875185)
    ·
      refine ⟨42818331212398712811656389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57091108283198283748875185 42818331212398712811656389)
      ·
        refine ⟨8028437102324758652185573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42818331212398712811656389 8028437102324758652185573)
        ·
          refine ⟨1505331956685892247284795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8028437102324758652185573 1505331956685892247284795)
          ·
            refine ⟨2257997935028838370927193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505331956685892247284795 2257997935028838370927193)
            ·
              refine ⟨1693498451271628778195395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257997935028838370927193 1693498451271628778195395)
              ·
                refine ⟨2540247676907443167293093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693498451271628778195395 2540247676907443167293093)
                ·
                  refine ⟨476296439420145593867455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540247676907443167293093 476296439420145593867455)
                  ·
                    rfl

theorem cell21_2087064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_2087064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087064 prefixEnd_2087064 := by exact prefixLift 2087064
  have htrace : WordTrace (prefixWord ++ tailWord_2087064) baseStart_2087064 baseEnd_2087064 := by
    simpa [prefixWord, tailWord_2087064, baseEnd_2087064] using wordTrace_append hprefix tailTrace_2087064
  have hstable : (prefixWord ++ tailWord_2087064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087064).length < 2 ^ (prefixWord ++ tailWord_2087064).sum := by decide
  have hdescent : baseEnd_2087064 < baseStart_2087064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087148 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2087148 : Nat := 118140960795 + 2087148 * 2 ^ 59
def prefixEnd_2087148 : Nat := 4983230072969 + 3 ^ 40 * 2087148 * 2
def baseEnd_2087148 : Nat := 476315609364580114467283

theorem tailTrace_2087148 : CollatzResearch.WordTrace tailWord_2087148 prefixEnd_2087148 476315609364580114467283 := by
  unfold tailWord_2087148
  simp only [CollatzResearch.WordTrace]
  refine ⟨38062270721313363672279049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50749694295084484896372065 38062270721313363672279049)
  ·
    refine ⟨28546703040985022754209287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38062270721313363672279049 28546703040985022754209287)
    ·
      refine ⟨42820054561477534131313931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28546703040985022754209287 42820054561477534131313931)
      ·
        refine ⟨64230081842216301196970897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42820054561477534131313931 64230081842216301196970897)
        ·
          refine ⟨48172561381662225897728173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64230081842216301196970897 48172561381662225897728173)
          ·
            refine ⟨18064710518123334711648065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48172561381662225897728173 18064710518123334711648065)
            ·
              refine ⟨13548532888592501033736049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18064710518123334711648065 13548532888592501033736049)
              ·
                refine ⟨10161399666444375775302037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13548532888592501033736049 10161399666444375775302037)
                ·
                  refine ⟨476315609364580114467283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10161399666444375775302037 476315609364580114467283)
                  ·
                    rfl

theorem cell21_2087148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2087148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087148 prefixEnd_2087148 := by exact prefixLift 2087148
  have htrace : WordTrace (prefixWord ++ tailWord_2087148) baseStart_2087148 baseEnd_2087148 := by
    simpa [prefixWord, tailWord_2087148, baseEnd_2087148] using wordTrace_append hprefix tailTrace_2087148
  have hstable : (prefixWord ++ tailWord_2087148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087148).length < 2 ^ (prefixWord ++ tailWord_2087148).sum := by decide
  have hdescent : baseEnd_2087148 < baseStart_2087148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087151 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 3]
def baseStart_2087151 : Nat := 118140960795 + 2087151 * 2 ^ 59
def prefixEnd_2087151 : Nat := 4983230072969 + 3 ^ 40 * 2087151 * 2
def baseEnd_2087151 : Nat := 476316294005452775917277

theorem tailTrace_2087151 : CollatzResearch.WordTrace tailWord_2087151 prefixEnd_2087151 476316294005452775917277 := by
  unfold tailWord_2087151
  simp only [CollatzResearch.WordTrace]
  refine ⟨76124650861615858856917307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50749767241077239237944871 76124650861615858856917307)
  ·
    refine ⟨114186976292423788285375961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76124650861615858856917307 114186976292423788285375961)
    ·
      refine ⟨85640232219317841214031971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114186976292423788285375961 85640232219317841214031971)
      ·
        refine ⟨128460348328976761821047957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85640232219317841214031971 128460348328976761821047957)
        ·
          refine ⟨6021578827920785710361623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128460348328976761821047957 6021578827920785710361623)
          ·
            refine ⟨9032368241881178565542435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021578827920785710361623 9032368241881178565542435)
            ·
              refine ⟨13548552362821767848313653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032368241881178565542435 13548552362821767848313653)
              ·
                refine ⟨1270176784014540735779405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13548552362821767848313653 1270176784014540735779405)
                ·
                  refine ⟨476316294005452775917277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270176784014540735779405 476316294005452775917277)
                  ·
                    rfl

theorem cell21_2087151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 3].length) (baseStart_2087151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087151 prefixEnd_2087151 := by exact prefixLift 2087151
  have htrace : WordTrace (prefixWord ++ tailWord_2087151) baseStart_2087151 baseEnd_2087151 := by
    simpa [prefixWord, tailWord_2087151, baseEnd_2087151] using wordTrace_append hprefix tailTrace_2087151
  have hstable : (prefixWord ++ tailWord_2087151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087151).length < 2 ^ (prefixWord ++ tailWord_2087151).sum := by decide
  have hdescent : baseEnd_2087151 < baseStart_2087151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087182 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2087182 : Nat := 118140960795 + 2087182 * 2 ^ 59
def prefixEnd_2087182 : Nat := 4983230072969 + 3 ^ 40 * 2087182 * 2
def baseEnd_2087182 : Nat := 476323368627803610900547

theorem tailTrace_2087182 : CollatzResearch.WordTrace tailWord_2087182 prefixEnd_2087182 476323368627803610900547 := by
  unfold tailWord_2087182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515722690562943893911975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50750521016335700767530533 9515722690562943893911975)
  ·
    refine ⟨14273584035844415840867963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515722690562943893911975 14273584035844415840867963)
    ·
      refine ⟨21410376053766623761301945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273584035844415840867963 21410376053766623761301945)
      ·
        refine ⟨16057782040324967820976459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21410376053766623761301945 16057782040324967820976459)
        ·
          refine ⟨24086673060487451731464689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057782040324967820976459 24086673060487451731464689)
          ·
            refine ⟨18065004795365588798598517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24086673060487451731464689 18065004795365588798598517)
            ·
              refine ⟨1693594199565523949868611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18065004795365588798598517 1693594199565523949868611)
              ·
                refine ⟨2540391299348285924802917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693594199565523949868611 2540391299348285924802917)
                ·
                  refine ⟨476323368627803610900547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540391299348285924802917 476323368627803610900547)
                  ·
                    rfl

theorem cell21_2087182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2087182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087182 prefixEnd_2087182 := by exact prefixLift 2087182
  have htrace : WordTrace (prefixWord ++ tailWord_2087182) baseStart_2087182 baseEnd_2087182 := by
    simpa [prefixWord, tailWord_2087182, baseEnd_2087182] using wordTrace_append hprefix tailTrace_2087182
  have hstable : (prefixWord ++ tailWord_2087182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087182).length < 2 ^ (prefixWord ++ tailWord_2087182).sum := by decide
  have hdescent : baseEnd_2087182 < baseStart_2087182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087213 : List Nat := [1, 5, 3, 1, 2, 2, 7]
def baseStart_2087213 : Nat := 118140960795 + 2087213 * 2 ^ 59
def prefixEnd_2087213 : Nat := 4983230072969 + 3 ^ 40 * 2087213 * 2
def baseEnd_2087213 : Nat := 52925604805572716209313

theorem tailTrace_2087213 : CollatzResearch.WordTrace tailWord_2087213 prefixEnd_2087213 52925604805572716209313 := by
  unfold tailWord_2087213
  simp only [CollatzResearch.WordTrace]
  refine ⟨76126912187391243445674293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50751274791594162297116195 76126912187391243445674293)
  ·
    refine ⟨7136898017567929073031965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76126912187391243445674293 7136898017567929073031965)
    ·
      refine ⟨2676336756587973402386987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7136898017567929073031965 2676336756587973402386987)
      ·
        refine ⟨4014505134881960103580481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676336756587973402386987 4014505134881960103580481)
        ·
          refine ⟨3010878851161470077685361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014505134881960103580481 3010878851161470077685361)
          ·
            refine ⟨2258159138371102558264021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010878851161470077685361 2258159138371102558264021)
            ·
              refine ⟨52925604805572716209313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2258159138371102558264021 52925604805572716209313)
              ·
                rfl

theorem cell21_2087213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 7].length) (baseStart_2087213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087213 prefixEnd_2087213 := by exact prefixLift 2087213
  have htrace : WordTrace (prefixWord ++ tailWord_2087213) baseStart_2087213 baseEnd_2087213 := by
    simpa [prefixWord, tailWord_2087213, baseEnd_2087213] using wordTrace_append hprefix tailTrace_2087213
  have hstable : (prefixWord ++ tailWord_2087213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087213).length < 2 ^ (prefixWord ++ tailWord_2087213).sum := by decide
  have hdescent : baseEnd_2087213 < baseStart_2087213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087224 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_2087224 : Nat := 118140960795 + 2087224 * 2 ^ 59
def prefixEnd_2087224 : Nat := 4983230072969 + 3 ^ 40 * 2087224 * 2
def baseEnd_2087224 : Nat := 476332953600020871200461

theorem tailTrace_2087224 : CollatzResearch.WordTrace tailWord_2087224 prefixEnd_2087224 476332953600020871200461 := by
  unfold tailWord_2087224
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063656695175696162162363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50751542260234261549549817 38063656695175696162162363)
  ·
    refine ⟨57095485042763544243243545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38063656695175696162162363 57095485042763544243243545)
    ·
      refine ⟨42821613782072658182432659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57095485042763544243243545 42821613782072658182432659)
      ·
        refine ⟨64232420673108987273648989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42821613782072658182432659 64232420673108987273648989)
        ·
          refine ⟨24087157752415870227618371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64232420673108987273648989 24087157752415870227618371)
          ·
            refine ⟨36130736628623805341427557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087157752415870227618371 36130736628623805341427557)
            ·
              refine ⟨6774513117866963501517667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36130736628623805341427557 6774513117866963501517667)
              ·
                refine ⟨10161769676800445252276501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6774513117866963501517667 10161769676800445252276501)
                ·
                  refine ⟨476332953600020871200461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10161769676800445252276501 476332953600020871200461)
                  ·
                    rfl

theorem cell21_2087224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_2087224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087224 prefixEnd_2087224 := by exact prefixLift 2087224
  have htrace : WordTrace (prefixWord ++ tailWord_2087224) baseStart_2087224 baseEnd_2087224 := by
    simpa [prefixWord, tailWord_2087224, baseEnd_2087224] using wordTrace_append hprefix tailTrace_2087224
  have hstable : (prefixWord ++ tailWord_2087224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087224).length < 2 ^ (prefixWord ++ tailWord_2087224).sum := by decide
  have hdescent : baseEnd_2087224 < baseStart_2087224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087320 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_2087320 : Nat := 118140960795 + 2087320 * 2 ^ 59
def prefixEnd_2087320 : Nat := 4983230072969 + 3 ^ 40 * 2087320 * 2
def baseEnd_2087320 : Nat := 476354862107946037600265

theorem tailTrace_2087320 : CollatzResearch.WordTrace tailWord_2087320 prefixEnd_2087320 476354862107946037600265 := by
  unfold tailWord_2087320
  simp only [CollatzResearch.WordTrace]
  refine ⟨38065407399001800359909707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50753876532002400479879609 38065407399001800359909707)
  ·
    refine ⟨57098111098502700539864561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38065407399001800359909707 57098111098502700539864561)
    ·
      refine ⟨42823583323877025404898421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57098111098502700539864561 42823583323877025404898421)
      ·
        refine ⟨4014710936613471131709227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42823583323877025404898421 4014710936613471131709227)
        ·
          refine ⟨6022066404920206697563841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014710936613471131709227 6022066404920206697563841)
          ·
            refine ⟨4516549803690155023172881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6022066404920206697563841 4516549803690155023172881)
            ·
              refine ⟨3387412352767616267379661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4516549803690155023172881 3387412352767616267379661)
              ·
                refine ⟨1270279632287856100267373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3387412352767616267379661 1270279632287856100267373)
                ·
                  refine ⟨476354862107946037600265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270279632287856100267373 476354862107946037600265)
                  ·
                    rfl

theorem cell21_2087320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_2087320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087320 prefixEnd_2087320 := by exact prefixLift 2087320
  have htrace : WordTrace (prefixWord ++ tailWord_2087320) baseStart_2087320 baseEnd_2087320 := by
    simpa [prefixWord, tailWord_2087320, baseEnd_2087320] using wordTrace_append hprefix tailTrace_2087320
  have hstable : (prefixWord ++ tailWord_2087320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087320).length < 2 ^ (prefixWord ++ tailWord_2087320).sum := by decide
  have hdescent : baseEnd_2087320 < baseStart_2087320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087410 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2087410 : Nat := 118140960795 + 2087410 * 2 ^ 59
def prefixEnd_2087410 : Nat := 4983230072969 + 3 ^ 40 * 2087410 * 2
def baseEnd_2087410 : Nat := 476375401334125881100081

theorem tailTrace_2087410 : CollatzResearch.WordTrace tailWord_2087410 prefixEnd_2087410 476375401334125881100081 := by
  unfold tailWord_2087410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19033524341919386522648921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50756064911785030727063789 19033524341919386522648921)
  ·
    refine ⟨14275143256439539891986691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19033524341919386522648921 14275143256439539891986691)
    ·
      refine ⟨21412714884659309837980037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275143256439539891986691 21412714884659309837980037)
      ·
        refine ⟨4014884040873620594621257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21412714884659309837980037 4014884040873620594621257)
        ·
          refine ⟨3011163030655215445965943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4014884040873620594621257 3011163030655215445965943)
          ·
            refine ⟨4516744545982823168948915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011163030655215445965943 4516744545982823168948915)
            ·
              refine ⟨6775116818974234753423373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4516744545982823168948915 6775116818974234753423373)
              ·
                refine ⟨2540668807115338032533765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6775116818974234753423373 2540668807115338032533765)
                ·
                  refine ⟨476375401334125881100081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540668807115338032533765 476375401334125881100081)
                  ·
                    rfl

theorem cell21_2087410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2087410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087410 prefixEnd_2087410 := by exact prefixLift 2087410
  have htrace : WordTrace (prefixWord ++ tailWord_2087410) baseStart_2087410 baseEnd_2087410 := by
    simpa [prefixWord, tailWord_2087410, baseEnd_2087410] using wordTrace_append hprefix tailTrace_2087410
  have hstable : (prefixWord ++ tailWord_2087410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087410).length < 2 ^ (prefixWord ++ tailWord_2087410).sum := by decide
  have hdescent : baseEnd_2087410 < baseStart_2087410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087421 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2087421 : Nat := 118140960795 + 2087421 * 2 ^ 59
def prefixEnd_2087421 : Nat := 4983230072969 + 3 ^ 40 * 2087421 * 2
def baseEnd_2087421 : Nat := 476377911683992306416725

theorem tailTrace_2087421 : CollatzResearch.WordTrace tailWord_2087421 prefixEnd_2087421 476377911683992306416725 := by
  unfold tailWord_2087421
  simp only [CollatzResearch.WordTrace]
  refine ⟨76134498570637694969246117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50756332380425129979497411 76134498570637694969246117)
  ·
    refine ⟨14275218481994567806733647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76134498570637694969246117 14275218481994567806733647)
    ·
      refine ⟨21412827722991851710100471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14275218481994567806733647 21412827722991851710100471)
      ·
        refine ⟨32119241584487777565150707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21412827722991851710100471 32119241584487777565150707)
        ·
          refine ⟨48178862376731666347726061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32119241584487777565150707 48178862376731666347726061)
          ·
            refine ⟨18067073391274374880397273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48178862376731666347726061 18067073391274374880397273)
            ·
              refine ⟨13550305043455781160297955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18067073391274374880397273 13550305043455781160297955)
              ·
                refine ⟨20325457565183671740446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13550305043455781160297955 20325457565183671740446933)
                ·
                  refine ⟨476377911683992306416725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20325457565183671740446933 476377911683992306416725)
                  ·
                    rfl

theorem cell21_2087421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2087421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087421 prefixEnd_2087421 := by exact prefixLift 2087421
  have htrace : WordTrace (prefixWord ++ tailWord_2087421) baseStart_2087421 baseEnd_2087421 := by
    simpa [prefixWord, tailWord_2087421, baseEnd_2087421] using wordTrace_append hprefix tailTrace_2087421
  have hstable : (prefixWord ++ tailWord_2087421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087421).length < 2 ^ (prefixWord ++ tailWord_2087421).sum := by decide
  have hdescent : baseEnd_2087421 < baseStart_2087421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087587 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_2087587 : Nat := 118140960795 + 2087587 * 2 ^ 59
def prefixEnd_2087587 : Nat := 4983230072969 + 3 ^ 40 * 2087587 * 2
def baseEnd_2087587 : Nat := 476415795145612906649719

theorem tailTrace_2087587 : CollatzResearch.WordTrace tailWord_2087587 prefixEnd_2087587 476415795145612906649719 := by
  unfold tailWord_2087587
  simp only [CollatzResearch.WordTrace]
  refine ⟨76140553088036305319789015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50760368725357536879859343 76140553088036305319789015)
  ·
    refine ⟨114210829632054457979683523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76140553088036305319789015 114210829632054457979683523)
    ·
      refine ⟨171316244448081686969525285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114210829632054457979683523 171316244448081686969525285)
      ·
        refine ⟨32121795834015316306785991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171316244448081686969525285 32121795834015316306785991)
        ·
          refine ⟨48182693751022974460178987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32121795834015316306785991 48182693751022974460178987)
          ·
            refine ⟨72274040626534461690268481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48182693751022974460178987 72274040626534461690268481)
            ·
              refine ⟨54205530469900846267701361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72274040626534461690268481 54205530469900846267701361)
              ·
                refine ⟨40654147852425634700776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54205530469900846267701361 40654147852425634700776021)
                ·
                  refine ⟨476415795145612906649719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40654147852425634700776021 476415795145612906649719)
                  ·
                    rfl

theorem cell21_2087587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_2087587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087587 prefixEnd_2087587 := by exact prefixLift 2087587
  have htrace : WordTrace (prefixWord ++ tailWord_2087587) baseStart_2087587 baseEnd_2087587 := by
    simpa [prefixWord, tailWord_2087587, baseEnd_2087587] using wordTrace_append hprefix tailTrace_2087587
  have hstable : (prefixWord ++ tailWord_2087587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087587).length < 2 ^ (prefixWord ++ tailWord_2087587).sum := by decide
  have hdescent : baseEnd_2087587 < baseStart_2087587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087624 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_2087624 : Nat := 118140960795 + 2087624 * 2 ^ 59
def prefixEnd_2087624 : Nat := 4983230072969 + 3 ^ 40 * 2087624 * 2
def baseEnd_2087624 : Nat := 476424239049709064532977

theorem tailTrace_2087624 : CollatzResearch.WordTrace tailWord_2087624 prefixEnd_2087624 476424239049709064532977 := by
  unfold tailWord_2087624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38070951294451130319442963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50761268392601507092590617 38070951294451130319442963)
  ·
    refine ⟨57106426941676695479164445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38070951294451130319442963 57106426941676695479164445)
    ·
      refine ⟨21414910103128760804686667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57106426941676695479164445 21414910103128760804686667)
      ·
        refine ⟨32122365154693141207030001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21414910103128760804686667 32122365154693141207030001)
        ·
          refine ⟨24091773866019855905272501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32122365154693141207030001 24091773866019855905272501)
          ·
            refine ⟨2258603799939361491119297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24091773866019855905272501 2258603799939361491119297)
            ·
              refine ⟨1693952849954521118339473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258603799939361491119297 1693952849954521118339473)
              ·
                refine ⟨1270464637465890838754605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693952849954521118339473 1270464637465890838754605)
                ·
                  refine ⟨476424239049709064532977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270464637465890838754605 476424239049709064532977)
                  ·
                    rfl

theorem cell21_2087624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_2087624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087624 prefixEnd_2087624 := by exact prefixLift 2087624
  have htrace : WordTrace (prefixWord ++ tailWord_2087624) baseStart_2087624 baseEnd_2087624 := by
    simpa [prefixWord, tailWord_2087624, baseEnd_2087624] using wordTrace_append hprefix tailTrace_2087624
  have hstable : (prefixWord ++ tailWord_2087624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087624).length < 2 ^ (prefixWord ++ tailWord_2087624).sum := by decide
  have hdescent : baseEnd_2087624 < baseStart_2087624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087649 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_2087649 : Nat := 118140960795 + 2087649 * 2 ^ 59
def prefixEnd_2087649 : Nat := 4983230072969 + 3 ^ 40 * 2087649 * 2
def baseEnd_2087649 : Nat := 476429944390314576616259

theorem tailTrace_2087649 : CollatzResearch.WordTrace tailWord_2087649 prefixEnd_2087649 476429944390314576616259 := by
  unfold tailWord_2087649
  simp only [CollatzResearch.WordTrace]
  refine ⟨76142814413811689908546001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50761876275874459939030667 76142814413811689908546001)
  ·
    refine ⟨57107110810358767431409501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76142814413811689908546001 57107110810358767431409501)
    ·
      refine ⟨21415166553884537786778563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57107110810358767431409501 21415166553884537786778563)
      ·
        refine ⟨32122749830826806680167845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21415166553884537786778563 32122749830826806680167845)
        ·
          refine ⟨6023015593280026252531471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32122749830826806680167845 6023015593280026252531471)
          ·
            refine ⟨9034523389920039378797207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023015593280026252531471 9034523389920039378797207)
            ·
              refine ⟨13551785084880059068195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034523389920039378797207 13551785084880059068195811)
              ·
                refine ⟨20327677627320088602293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13551785084880059068195811 20327677627320088602293717)
                ·
                  refine ⟨476429944390314576616259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20327677627320088602293717 476429944390314576616259)
                  ·
                    rfl

theorem cell21_2087649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_2087649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087649 prefixEnd_2087649 := by exact prefixLift 2087649
  have htrace : WordTrace (prefixWord ++ tailWord_2087649) baseStart_2087649 baseEnd_2087649 := by
    simpa [prefixWord, tailWord_2087649, baseEnd_2087649] using wordTrace_append hprefix tailTrace_2087649
  have hstable : (prefixWord ++ tailWord_2087649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087649).length < 2 ^ (prefixWord ++ tailWord_2087649).sum := by decide
  have hdescent : baseEnd_2087649 < baseStart_2087649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087669 : List Nat := [1, 3, 6, 1, 1, 1, 8]
def baseStart_2087669 : Nat := 118140960795 + 2087669 * 2 ^ 59
def prefixEnd_2087669 : Nat := 4983230072969 + 3 ^ 40 * 2087669 * 2
def baseEnd_2087669 : Nat := 52937167629199887364765

theorem tailTrace_2087669 : CollatzResearch.WordTrace tailWord_2087669 prefixEnd_2087669 52937167629199887364765 := by
  unfold tailWord_2087669
  simp only [CollatzResearch.WordTrace]
  refine ⟨76143543873739233324274061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50762362582492822216182707 76143543873739233324274061)
  ·
    refine ⟨28553828952652212496602773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76143543873739233324274061 28553828952652212496602773)
    ·
      refine ⟨1338460732155572460778255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28553828952652212496602773 1338460732155572460778255)
      ·
        refine ⟨2007691098233358691167383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338460732155572460778255 2007691098233358691167383)
        ·
          refine ⟨3011536647350038036751075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007691098233358691167383 3011536647350038036751075)
          ·
            refine ⟨4517304971025057055126613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011536647350038036751075 4517304971025057055126613)
            ·
              refine ⟨52937167629199887364765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4517304971025057055126613 52937167629199887364765)
              ·
                rfl

theorem cell21_2087669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 8].length) (baseStart_2087669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087669 prefixEnd_2087669 := by exact prefixLift 2087669
  have htrace : WordTrace (prefixWord ++ tailWord_2087669) baseStart_2087669 baseEnd_2087669 := by
    simpa [prefixWord, tailWord_2087669, baseEnd_2087669] using wordTrace_append hprefix tailTrace_2087669
  have hstable : (prefixWord ++ tailWord_2087669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087669).length < 2 ^ (prefixWord ++ tailWord_2087669).sum := by decide
  have hdescent : baseEnd_2087669 < baseStart_2087669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087694 : List Nat := [4, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2087694 : Nat := 118140960795 + 2087694 * 2 ^ 59
def prefixEnd_2087694 : Nat := 4983230072969 + 3 ^ 40 * 2087694 * 2
def baseEnd_2087694 : Nat := 158813404667801499455389

theorem tailTrace_2087694 : CollatzResearch.WordTrace tailWord_2087694 prefixEnd_2087694 158813404667801499455389 := by
  unfold tailWord_2087694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518056962331082824241767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50762970465765775062622757 9518056962331082824241767)
  ·
    refine ⟨14277085443496624236362651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518056962331082824241767 14277085443496624236362651)
    ·
      refine ⟨21415628165244936354543977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14277085443496624236362651 21415628165244936354543977)
      ·
        refine ⟨16061721123933702265907983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21415628165244936354543977 16061721123933702265907983)
        ·
          refine ⟨24092581685900553398861975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16061721123933702265907983 24092581685900553398861975)
          ·
            refine ⟨36138872528850830098292963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24092581685900553398861975 36138872528850830098292963)
            ·
              refine ⟨54208308793276245147439445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36138872528850830098292963 54208308793276245147439445)
              ·
                refine ⟨158813404667801499455389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54208308793276245147439445 158813404667801499455389)
                ·
                  rfl

theorem cell21_2087694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2087694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087694 prefixEnd_2087694 := by exact prefixLift 2087694
  have htrace : WordTrace (prefixWord ++ tailWord_2087694) baseStart_2087694 baseEnd_2087694 := by
    simpa [prefixWord, tailWord_2087694, baseEnd_2087694] using wordTrace_append hprefix tailTrace_2087694
  have hstable : (prefixWord ++ tailWord_2087694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087694).length < 2 ^ (prefixWord ++ tailWord_2087694).sum := by decide
  have hdescent : baseEnd_2087694 < baseStart_2087694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087711 : List Nat := [1, 1, 2, 4, 2, 2, 4, 5]
def baseStart_2087711 : Nat := 118140960795 + 2087711 * 2 ^ 59
def prefixEnd_2087711 : Nat := 4983230072969 + 3 ^ 40 * 2087711 * 2
def baseEnd_2087711 : Nat := 158814697878338748860933

theorem tailTrace_2087711 : CollatzResearch.WordTrace tailWord_2087711 prefixEnd_2087711 158814697878338748860933 := by
  unfold tailWord_2087711
  simp only [CollatzResearch.WordTrace]
  refine ⟨76145075739587074497302987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50763383826391382998201991 76145075739587074497302987)
  ·
    refine ⟨114217613609380611745954481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76145075739587074497302987 114217613609380611745954481)
    ·
      refine ⟨85663210207035458809465861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114217613609380611745954481 85663210207035458809465861)
      ·
        refine ⟨16061851913819148526774849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85663210207035458809465861 16061851913819148526774849)
        ·
          refine ⟨12046388935364361395081137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16061851913819148526774849 12046388935364361395081137)
          ·
            refine ⟨9034791701523271046310853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12046388935364361395081137 9034791701523271046310853)
            ·
              refine ⟨1694023444035613321183285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9034791701523271046310853 1694023444035613321183285)
              ·
                refine ⟨158814697878338748860933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694023444035613321183285 158814697878338748860933)
                ·
                  rfl

theorem cell21_2087711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].length) (baseStart_2087711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087711 prefixEnd_2087711 := by exact prefixLift 2087711
  have htrace : WordTrace (prefixWord ++ tailWord_2087711) baseStart_2087711 baseEnd_2087711 := by
    simpa [prefixWord, tailWord_2087711, baseEnd_2087711] using wordTrace_append hprefix tailTrace_2087711
  have hstable : (prefixWord ++ tailWord_2087711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087711).length < 2 ^ (prefixWord ++ tailWord_2087711).sum := by decide
  have hdescent : baseEnd_2087711 < baseStart_2087711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087748 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2087748 : Nat := 118140960795 + 2087748 * 2 ^ 59
def prefixEnd_2087748 : Nat := 4983230072969 + 3 ^ 40 * 2087748 * 2
def baseEnd_2087748 : Nat := 476452537539112404466057

theorem tailTrace_2087748 : CollatzResearch.WordTrace tailWord_2087748 prefixEnd_2087748 476452537539112404466057 := by
  unfold tailWord_2087748
  simp only [CollatzResearch.WordTrace]
  refine ⟨38073212620226514908199949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50764283493635353210933265 38073212620226514908199949)
  ·
    refine ⟨14277454732584943090574981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38073212620226514908199949 14277454732584943090574981)
    ·
      refine ⟨2677022762359676829482809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14277454732584943090574981 2677022762359676829482809)
      ·
        refine ⟨2007767071769757622112107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2677022762359676829482809 2007767071769757622112107)
        ·
          refine ⟨3011650607654636433168161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007767071769757622112107 3011650607654636433168161)
          ·
            refine ⟨2258737955740977324876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011650607654636433168161 2258737955740977324876121)
            ·
              refine ⟨1694053466805732993657091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258737955740977324876121 1694053466805732993657091)
              ·
                refine ⟨2541080200208599490485637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694053466805732993657091 2541080200208599490485637)
                ·
                  refine ⟨476452537539112404466057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541080200208599490485637 476452537539112404466057)
                  ·
                    rfl

theorem cell21_2087748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2087748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087748 prefixEnd_2087748 := by exact prefixLift 2087748
  have htrace : WordTrace (prefixWord ++ tailWord_2087748) baseStart_2087748 baseEnd_2087748 := by
    simpa [prefixWord, tailWord_2087748, baseEnd_2087748] using wordTrace_append hprefix tailTrace_2087748
  have hstable : (prefixWord ++ tailWord_2087748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087748).length < 2 ^ (prefixWord ++ tailWord_2087748).sum := by decide
  have hdescent : baseEnd_2087748 < baseStart_2087748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087770 : List Nat := [3, 1, 1, 2, 1, 4, 2, 7]
def baseStart_2087770 : Nat := 118140960795 + 2087770 * 2 ^ 59
def prefixEnd_2087770 : Nat := 4983230072969 + 3 ^ 40 * 2087770 * 2
def baseEnd_2087770 : Nat := 158819186079615085033115

theorem tailTrace_2087770 : CollatzResearch.WordTrace tailWord_2087770 prefixEnd_2087770 158819186079615085033115 := by
  unfold tailWord_2087770
  simp only [CollatzResearch.WordTrace]
  refine ⟨19036806911593331893425191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50764818430915551715800509 19036806911593331893425191)
  ·
    refine ⟨28555210367389997840137787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19036806911593331893425191 28555210367389997840137787)
    ·
      refine ⟨42832815551084996760206681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28555210367389997840137787 42832815551084996760206681)
      ·
        refine ⟨32124611663313747570155011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42832815551084996760206681 32124611663313747570155011)
        ·
          refine ⟨48186917494970621355232517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32124611663313747570155011 48186917494970621355232517)
          ·
            refine ⟨9035047030306991504106097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48186917494970621355232517 9035047030306991504106097)
            ·
              refine ⟨6776285272730243628079573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9035047030306991504106097 6776285272730243628079573)
              ·
                refine ⟨158819186079615085033115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6776285272730243628079573 158819186079615085033115)
                ·
                  rfl

theorem cell21_2087770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_2087770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087770 prefixEnd_2087770 := by exact prefixLift 2087770
  have htrace : WordTrace (prefixWord ++ tailWord_2087770) baseStart_2087770 baseEnd_2087770 := by
    simpa [prefixWord, tailWord_2087770, baseEnd_2087770] using wordTrace_append hprefix tailTrace_2087770
  have hstable : (prefixWord ++ tailWord_2087770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087770).length < 2 ^ (prefixWord ++ tailWord_2087770).sum := by decide
  have hdescent : baseEnd_2087770 < baseStart_2087770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087790 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2087790 : Nat := 118140960795 + 2087790 * 2 ^ 59
def prefixEnd_2087790 : Nat := 4983230072969 + 3 ^ 40 * 2087790 * 2
def baseEnd_2087790 : Nat := 476462122511329664765971

theorem tailTrace_2087790 : CollatzResearch.WordTrace tailWord_2087790 prefixEnd_2087790 476462122511329664765971 := by
  unfold tailWord_2087790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518494638287608873678603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50765304737533913992952549 9518494638287608873678603)
  ·
    refine ⟨14277741957431413310517905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518494638287608873678603 14277741957431413310517905)
    ·
      refine ⟨10708306468073559982888429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14277741957431413310517905 10708306468073559982888429)
      ·
        refine ⟨4015614925527584993583161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10708306468073559982888429 4015614925527584993583161)
        ·
          refine ⟨3011711194145688745187371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4015614925527584993583161 3011711194145688745187371)
          ·
            refine ⟨4517566791218533117781057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011711194145688745187371 4517566791218533117781057)
            ·
              refine ⟨3388175093413899838335793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517566791218533117781057 3388175093413899838335793)
              ·
                refine ⟨2541131320060424878751845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388175093413899838335793 2541131320060424878751845)
                ·
                  refine ⟨476462122511329664765971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541131320060424878751845 476462122511329664765971)
                  ·
                    rfl

theorem cell21_2087790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2087790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087790 prefixEnd_2087790 := by exact prefixLift 2087790
  have htrace : WordTrace (prefixWord ++ tailWord_2087790) baseStart_2087790 baseEnd_2087790 := by
    simpa [prefixWord, tailWord_2087790, baseEnd_2087790] using wordTrace_append hprefix tailTrace_2087790
  have hstable : (prefixWord ++ tailWord_2087790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087790).length < 2 ^ (prefixWord ++ tailWord_2087790).sum := by decide
  have hdescent : baseEnd_2087790 < baseStart_2087790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087818 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_2087818 : Nat := 118140960795 + 2087818 * 2 ^ 59
def prefixEnd_2087818 : Nat := 4983230072969 + 3 ^ 40 * 2087818 * 2
def baseEnd_2087818 : Nat := 476468512492807838299247

theorem tailTrace_2087818 : CollatzResearch.WordTrace tailWord_2087818 prefixEnd_2087818 476468512492807838299247 := by
  unfold tailWord_2087818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037244587549857942862027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50765985566799621180965405 19037244587549857942862027)
  ·
    refine ⟨28555866881324786914293041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19037244587549857942862027 28555866881324786914293041)
    ·
      refine ⟨21416900160993590185719781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28555866881324786914293041 21416900160993590185719781)
      ·
        refine ⟨4015668780186298159822459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21416900160993590185719781 4015668780186298159822459)
        ·
          refine ⟨6023503170279447239733689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015668780186298159822459 6023503170279447239733689)
          ·
            refine ⟨4517627377709585429800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023503170279447239733689 4517627377709585429800267)
            ·
              refine ⟨6776441066564378144700401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517627377709585429800267 6776441066564378144700401)
              ·
                refine ⟨5082330799923283608525301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6776441066564378144700401 5082330799923283608525301)
                ·
                  refine ⟨476468512492807838299247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5082330799923283608525301 476468512492807838299247)
                  ·
                    rfl

theorem cell21_2087818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_2087818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087818 prefixEnd_2087818 := by exact prefixLift 2087818
  have htrace : WordTrace (prefixWord ++ tailWord_2087818) baseStart_2087818 baseEnd_2087818 := by
    simpa [prefixWord, tailWord_2087818, baseEnd_2087818] using wordTrace_append hprefix tailTrace_2087818
  have hstable : (prefixWord ++ tailWord_2087818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087818).length < 2 ^ (prefixWord ++ tailWord_2087818).sum := by decide
  have hdescent : baseEnd_2087818 < baseStart_2087818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2087880 : List Nat := [2, 1, 3, 1, 5, 2, 2, 5]
def baseStart_2087880 : Nat := 118140960795 + 2087880 * 2 ^ 59
def prefixEnd_2087880 : Nat := 4983230072969 + 3 ^ 40 * 2087880 * 2
def baseEnd_2087880 : Nat := 158827553912503169421929

theorem tailTrace_2087880 : CollatzResearch.WordTrace tailWord_2087880 prefixEnd_2087880 158827553912503169421929 := by
  unfold tailWord_2087880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075619837987408180102547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50767493117316544240136729 38075619837987408180102547)
  ·
    refine ⟨57113429756981112270153821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38075619837987408180102547 57113429756981112270153821)
    ·
      refine ⟨21417536158867917101307683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57113429756981112270153821 21417536158867917101307683)
      ·
        refine ⟨32126304238301875651961525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21417536158867917101307683 32126304238301875651961525)
        ·
          refine ⟨3011841022340800842371393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32126304238301875651961525 3011841022340800842371393)
          ·
            refine ⟨2258880766755600631778545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3011841022340800842371393 2258880766755600631778545)
            ·
              refine ⟨1694160575066700473833909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258880766755600631778545 1694160575066700473833909)
              ·
                refine ⟨158827553912503169421929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694160575066700473833909 158827553912503169421929)
                ·
                  rfl

theorem cell21_2087880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_2087880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2087880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2087880 prefixEnd_2087880 := by exact prefixLift 2087880
  have htrace : WordTrace (prefixWord ++ tailWord_2087880) baseStart_2087880 baseEnd_2087880 := by
    simpa [prefixWord, tailWord_2087880, baseEnd_2087880] using wordTrace_append hprefix tailTrace_2087880
  have hstable : (prefixWord ++ tailWord_2087880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2087880).length < 2 ^ (prefixWord ++ tailWord_2087880).sum := by decide
  have hdescent : baseEnd_2087880 < baseStart_2087880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2087880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088012 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2088012 : Nat := 118140960795 + 2088012 * 2 ^ 59
def prefixEnd_2088012 : Nat := 4983230072969 + 3 ^ 40 * 2088012 * 2
def baseEnd_2088012 : Nat := 476512785935906612065517

theorem tailTrace_2088012 : CollatzResearch.WordTrace tailWord_2088012 prefixEnd_2088012 476512785935906612065517 := by
  unfold tailWord_2088012
  simp only [CollatzResearch.WordTrace]
  refine ⟨38078027055748301452005145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50770702740997735269340193 38078027055748301452005145)
  ·
    refine ⟨28558520291811226089003859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38078027055748301452005145 28558520291811226089003859)
    ·
      refine ⟨42837780437716839133505789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28558520291811226089003859 42837780437716839133505789)
      ·
        refine ⟨16064167664143814675064671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42837780437716839133505789 16064167664143814675064671)
        ·
          refine ⟨24096251496215722012597007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16064167664143814675064671 24096251496215722012597007)
          ·
            refine ⟨36144377244323583018895511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24096251496215722012597007 36144377244323583018895511)
            ·
              refine ⟨54216565866485374528343267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36144377244323583018895511 54216565866485374528343267)
              ·
                refine ⟨81324848799728061792514901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54216565866485374528343267 81324848799728061792514901)
                ·
                  refine ⟨476512785935906612065517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81324848799728061792514901 476512785935906612065517)
                  ·
                    rfl

theorem cell21_2088012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2088012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088012 prefixEnd_2088012 := by exact prefixLift 2088012
  have htrace : WordTrace (prefixWord ++ tailWord_2088012) baseStart_2088012 baseEnd_2088012 := by
    simpa [prefixWord, tailWord_2088012, baseEnd_2088012] using wordTrace_append hprefix tailTrace_2088012
  have hstable : (prefixWord ++ tailWord_2088012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088012).length < 2 ^ (prefixWord ++ tailWord_2088012).sum := by decide
  have hdescent : baseEnd_2088012 < baseStart_2088012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088094 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2088094 : Nat := 118140960795 + 2088094 * 2 ^ 59
def prefixEnd_2088094 : Nat := 4983230072969 + 3 ^ 40 * 2088094 * 2
def baseEnd_2088094 : Nat := 476531499453092691698683

theorem tailTrace_2088094 : CollatzResearch.WordTrace tailWord_2088094 prefixEnd_2088094 476531499453092691698683 := by
  unfold tailWord_2088094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519880612149941363561917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50772696598133020605663557 9519880612149941363561917)
  ·
    refine ⟨3569955229556228011335719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9519880612149941363561917 3569955229556228011335719)
    ·
      refine ⟨5354932844334342017003579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569955229556228011335719 5354932844334342017003579)
      ·
        refine ⟨8032399266501513025505369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354932844334342017003579 8032399266501513025505369)
        ·
          refine ⟨6024299449876134769129027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8032399266501513025505369 6024299449876134769129027)
          ·
            refine ⟨9036449174814202153693541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024299449876134769129027 9036449174814202153693541)
            ·
              refine ⟨1694334220277662903817539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9036449174814202153693541 1694334220277662903817539)
              ·
                refine ⟨2541501330416494355726309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694334220277662903817539 2541501330416494355726309)
                ·
                  refine ⟨476531499453092691698683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541501330416494355726309 476531499453092691698683)
                  ·
                    rfl

theorem cell21_2088094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2088094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088094 prefixEnd_2088094 := by exact prefixLift 2088094
  have htrace : WordTrace (prefixWord ++ tailWord_2088094) baseStart_2088094 baseEnd_2088094 := by
    simpa [prefixWord, tailWord_2088094, baseEnd_2088094] using wordTrace_append hprefix tailTrace_2088094
  have hstable : (prefixWord ++ tailWord_2088094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088094).length < 2 ^ (prefixWord ++ tailWord_2088094).sum := by decide
  have hdescent : baseEnd_2088094 < baseStart_2088094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088164 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2088164 : Nat := 118140960795 + 2088164 * 2 ^ 59
def prefixEnd_2088164 : Nat := 4983230072969 + 3 ^ 40 * 2088164 * 2
def baseEnd_2088164 : Nat := 476547474406788125531873

theorem tailTrace_2088164 : CollatzResearch.WordTrace tailWord_2088164 prefixEnd_2088164 476547474406788125531873 := by
  unfold tailWord_2088164
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080799003472966431771773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50774398671297288575695697 38080799003472966431771773)
  ·
    refine ⟨14280299626302362411914415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38080799003472966431771773 14280299626302362411914415)
    ·
      refine ⟨21420449439453543617871623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14280299626302362411914415 21420449439453543617871623)
      ·
        refine ⟨32130674159180315426807435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21420449439453543617871623 32130674159180315426807435)
        ·
          refine ⟨48196011238770473140211153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32130674159180315426807435 48196011238770473140211153)
          ·
            refine ⟨36147008429077854855158365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48196011238770473140211153 36147008429077854855158365)
            ·
              refine ⟨13555128160904195570684387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36147008429077854855158365 13555128160904195570684387)
              ·
                refine ⟨20332692241356293356026581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555128160904195570684387 20332692241356293356026581)
                ·
                  refine ⟨476547474406788125531873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20332692241356293356026581 476547474406788125531873)
                  ·
                    rfl

theorem cell21_2088164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2088164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088164 prefixEnd_2088164 := by exact prefixLift 2088164
  have htrace : WordTrace (prefixWord ++ tailWord_2088164) baseStart_2088164 baseEnd_2088164 := by
    simpa [prefixWord, tailWord_2088164, baseEnd_2088164] using wordTrace_append hprefix tailTrace_2088164
  have hstable : (prefixWord ++ tailWord_2088164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088164).length < 2 ^ (prefixWord ++ tailWord_2088164).sum := by decide
  have hdescent : baseEnd_2088164 < baseStart_2088164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088195 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_2088195 : Nat := 118140960795 + 2088195 * 2 ^ 59
def prefixEnd_2088195 : Nat := 4983230072969 + 3 ^ 40 * 2088195 * 2
def baseEnd_2088195 : Nat := 476554549029138960515143

theorem tailTrace_2088195 : CollatzResearch.WordTrace tailWord_2088195 prefixEnd_2088195 476554549029138960515143 := by
  unfold tailWord_2088195
  simp only [CollatzResearch.WordTrace]
  refine ⟨76162728669833625157922039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50775152446555750105281359 76162728669833625157922039)
  ·
    refine ⟨114244093004750437736883059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76162728669833625157922039 114244093004750437736883059)
    ·
      refine ⟨171366139507125656605324589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114244093004750437736883059 171366139507125656605324589)
      ·
        refine ⟨64262302315172121226996721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171366139507125656605324589 64262302315172121226996721)
        ·
          refine ⟨48196726736379090920247541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64262302315172121226996721 48196726736379090920247541)
          ·
            refine ⟨4518443131535539773773207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48196726736379090920247541 4518443131535539773773207)
            ·
              refine ⟨6777664697303309660659811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518443131535539773773207 6777664697303309660659811)
              ·
                refine ⟨10166497045954964490989717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777664697303309660659811 10166497045954964490989717)
                ·
                  refine ⟨476554549029138960515143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10166497045954964490989717 476554549029138960515143)
                  ·
                    rfl

theorem cell21_2088195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_2088195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088195 prefixEnd_2088195 := by exact prefixLift 2088195
  have htrace : WordTrace (prefixWord ++ tailWord_2088195) baseStart_2088195 baseEnd_2088195 := by
    simpa [prefixWord, tailWord_2088195, baseEnd_2088195] using wordTrace_append hprefix tailTrace_2088195
  have hstable : (prefixWord ++ tailWord_2088195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088195).length < 2 ^ (prefixWord ++ tailWord_2088195).sum := by decide
  have hdescent : baseEnd_2088195 < baseStart_2088195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088209 : List Nat := [1, 2, 2, 1, 1, 4, 2, 8]
def baseStart_2088209 : Nat := 118140960795 + 2088209 * 2 ^ 59
def prefixEnd_2088209 : Nat := 4983230072969 + 3 ^ 40 * 2088209 * 2
def baseEnd_2088209 : Nat := 158852581339959349093927

theorem tailTrace_2088209 : CollatzResearch.WordTrace tailWord_2088209 prefixEnd_2088209 158852581339959349093927 := by
  unfold tailWord_2088209
  simp only [CollatzResearch.WordTrace]
  refine ⟨76163239291782905548931681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50775492861188603699287787 76163239291782905548931681)
  ·
    refine ⟨57122429468837179161698761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76163239291782905548931681 57122429468837179161698761)
    ·
      refine ⟨42841822101627884371274071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57122429468837179161698761 42841822101627884371274071)
      ·
        refine ⟨64262733152441826556911107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42841822101627884371274071 64262733152441826556911107)
        ·
          refine ⟨96394099728662739835366661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64262733152441826556911107 96394099728662739835366661)
          ·
            refine ⟨18073893699124263719131249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96394099728662739835366661 18073893699124263719131249)
            ·
              refine ⟨13555420274343197789348437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073893699124263719131249 13555420274343197789348437)
              ·
                refine ⟨158852581339959349093927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13555420274343197789348437 158852581339959349093927)
                ·
                  rfl

theorem cell21_2088209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_2088209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088209 prefixEnd_2088209 := by exact prefixLift 2088209
  have htrace : WordTrace (prefixWord ++ tailWord_2088209) baseStart_2088209 baseEnd_2088209 := by
    simpa [prefixWord, tailWord_2088209, baseEnd_2088209] using wordTrace_append hprefix tailTrace_2088209
  have hstable : (prefixWord ++ tailWord_2088209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088209).length < 2 ^ (prefixWord ++ tailWord_2088209).sum := by decide
  have hdescent : baseEnd_2088209 < baseStart_2088209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088302 : List Nat := [4, 1, 2, 4, 10]
def baseStart_2088302 : Nat := 118140960795 + 2088302 * 2 ^ 59
def prefixEnd_2088302 : Nat := 4983230072969 + 3 ^ 40 * 2088302 * 2
def baseEnd_2088302 : Nat := 5883690961567043854711

theorem tailTrace_2088302 : CollatzResearch.WordTrace tailWord_2088302 prefixEnd_2088302 5883690961567043854711 := by
  unfold tailWord_2088302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520828910055747804008395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50777754186963988288044773 9520828910055747804008395)
  ·
    refine ⟨14281243365083621706012593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520828910055747804008395 14281243365083621706012593)
    ·
      refine ⟨10710932523812716279509445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14281243365083621706012593 10710932523812716279509445)
      ·
        refine ⟨2008299848214884302408021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10710932523812716279509445 2008299848214884302408021)
        ·
          refine ⟨5883690961567043854711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 2008299848214884302408021 5883690961567043854711)
          ·
            rfl

theorem cell21_2088302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 10].length) (baseStart_2088302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088302 prefixEnd_2088302 := by exact prefixLift 2088302
  have htrace : WordTrace (prefixWord ++ tailWord_2088302) baseStart_2088302 baseEnd_2088302 := by
    simpa [prefixWord, tailWord_2088302, baseEnd_2088302] using wordTrace_append hprefix tailTrace_2088302
  have hstable : (prefixWord ++ tailWord_2088302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088302).length < 2 ^ (prefixWord ++ tailWord_2088302).sum := by decide
  have hdescent : baseEnd_2088302 < baseStart_2088302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088316 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_2088316 : Nat := 118140960795 + 2088316 * 2 ^ 59
def prefixEnd_2088316 : Nat := 4983230072969 + 3 ^ 40 * 2088316 * 2
def baseEnd_2088316 : Nat := 476582162877669638998229

theorem tailTrace_2088316 : CollatzResearch.WordTrace tailWord_2088316 prefixEnd_2088316 476582162877669638998229 := by
  unfold tailWord_2088316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083570951197631411538401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50778094601596841882051201 38083570951197631411538401)
  ·
    refine ⟨28562678213398223558653801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38083570951197631411538401 28562678213398223558653801)
    ·
      refine ⟨21422008660048667668990351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28562678213398223558653801 21422008660048667668990351)
      ·
        refine ⟨32133012990073001503485527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422008660048667668990351 32133012990073001503485527)
        ·
          refine ⟨48199519485109502255228291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32133012990073001503485527 48199519485109502255228291)
          ·
            refine ⟨72299279227664253382842437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48199519485109502255228291 72299279227664253382842437)
            ·
              refine ⟨13556114855187047509282957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72299279227664253382842437 13556114855187047509282957)
              ·
                refine ⟨5083543070695142815981109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13556114855187047509282957 5083543070695142815981109)
                ·
                  refine ⟨476582162877669638998229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083543070695142815981109 476582162877669638998229)
                  ·
                    rfl

theorem cell21_2088316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_2088316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088316 prefixEnd_2088316 := by exact prefixLift 2088316
  have htrace : WordTrace (prefixWord ++ tailWord_2088316) baseStart_2088316 baseEnd_2088316 := by
    simpa [prefixWord, tailWord_2088316, baseEnd_2088316] using wordTrace_append hprefix tailTrace_2088316
  have hstable : (prefixWord ++ tailWord_2088316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088316).length < 2 ^ (prefixWord ++ tailWord_2088316).sum := by decide
  have hdescent : baseEnd_2088316 < baseStart_2088316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088392 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_2088392 : Nat := 118140960795 + 2088392 * 2 ^ 59
def prefixEnd_2088392 : Nat := 4983230072969 + 3 ^ 40 * 2088392 * 2
def baseEnd_2088392 : Nat := 476599507113110395731407

theorem tailTrace_2088392 : CollatzResearch.WordTrace tailWord_2088392 prefixEnd_2088392 476599507113110395731407 := by
  unfold tailWord_2088392
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084956925059963901421715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50779942566746618535228953 38084956925059963901421715)
  ·
    refine ⟨57127435387589945852132573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38084956925059963901421715 57127435387589945852132573)
    ·
      refine ⟨21422788270346229694549715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57127435387589945852132573 21422788270346229694549715)
      ·
        refine ⟨32134182405519344541824573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422788270346229694549715 32134182405519344541824573)
        ·
          refine ⟨12050318402069754203184215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32134182405519344541824573 12050318402069754203184215)
          ·
            refine ⟨18075477603104631304776323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050318402069754203184215 18075477603104631304776323)
            ·
              refine ⟨27113216404656946957164485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075477603104631304776323 27113216404656946957164485)
              ·
                refine ⟨5083728075873177554468341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27113216404656946957164485 5083728075873177554468341)
                ·
                  refine ⟨476599507113110395731407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083728075873177554468341 476599507113110395731407)
                  ·
                    rfl

theorem cell21_2088392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_2088392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088392 prefixEnd_2088392 := by exact prefixLift 2088392
  have htrace : WordTrace (prefixWord ++ tailWord_2088392) baseStart_2088392 baseEnd_2088392 := by
    simpa [prefixWord, tailWord_2088392, baseEnd_2088392] using wordTrace_append hprefix tailTrace_2088392
  have hstable : (prefixWord ++ tailWord_2088392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088392).length < 2 ^ (prefixWord ++ tailWord_2088392).sum := by decide
  have hdescent : baseEnd_2088392 < baseStart_2088392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088423 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_2088423 : Nat := 118140960795 + 2088423 * 2 ^ 59
def prefixEnd_2088423 : Nat := 4983230072969 + 3 ^ 40 * 2088423 * 2
def baseEnd_2088423 : Nat := 476606581735461230714677

theorem tailTrace_2088423 : CollatzResearch.WordTrace tailWord_2088423 prefixEnd_2088423 476606581735461230714677 := by
  unfold tailWord_2088423
  simp only [CollatzResearch.WordTrace]
  refine ⟨76171044513007620097221923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50780696342005080064814615 76171044513007620097221923)
  ·
    refine ⟨114256566769511430145832885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76171044513007620097221923 114256566769511430145832885)
    ·
      refine ⟨10711553134641696576171833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114256566769511430145832885 10711553134641696576171833)
      ·
        refine ⟨8033664850981272432128875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711553134641696576171833 8033664850981272432128875)
        ·
          refine ⟨12050497276471908648193313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033664850981272432128875 12050497276471908648193313)
          ·
            refine ⟨9037872957353931486144985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12050497276471908648193313 9037872957353931486144985)
            ·
              refine ⟨6778404718015448614608739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9037872957353931486144985 6778404718015448614608739)
              ·
                refine ⟨10167607077023172921913109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778404718015448614608739 10167607077023172921913109)
                ·
                  refine ⟨476606581735461230714677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10167607077023172921913109 476606581735461230714677)
                  ·
                    rfl

theorem cell21_2088423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_2088423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088423 prefixEnd_2088423 := by exact prefixLift 2088423
  have htrace : WordTrace (prefixWord ++ tailWord_2088423) baseStart_2088423 baseEnd_2088423 := by
    simpa [prefixWord, tailWord_2088423, baseEnd_2088423] using wordTrace_append hprefix tailTrace_2088423
  have hstable : (prefixWord ++ tailWord_2088423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088423).length < 2 ^ (prefixWord ++ tailWord_2088423).sum := by decide
  have hdescent : baseEnd_2088423 < baseStart_2088423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088426 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2088426 : Nat := 118140960795 + 2088426 * 2 ^ 59
def prefixEnd_2088426 : Nat := 4983230072969 + 3 ^ 40 * 2088426 * 2
def baseEnd_2088426 : Nat := 476607266376333892164671

theorem tailTrace_2088426 : CollatzResearch.WordTrace tailWord_2088426 prefixEnd_2088426 476607266376333892164671 := by
  unfold tailWord_2088426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042788482999187902395283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50780769287997834406387421 19042788482999187902395283)
  ·
    refine ⟨28564182724498781853592925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19042788482999187902395283 28564182724498781853592925)
    ·
      refine ⟨10711568521687043195097347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28564182724498781853592925 10711568521687043195097347)
      ·
        refine ⟨16067352782530564792646021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711568521687043195097347 16067352782530564792646021)
        ·
          refine ⟨3012628646724480898621129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16067352782530564792646021 3012628646724480898621129)
          ·
            refine ⟨2259471485043360673965847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012628646724480898621129 2259471485043360673965847)
            ·
              refine ⟨3389207227565041010948771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259471485043360673965847 3389207227565041010948771)
              ·
                refine ⟨5083810841347561516423157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389207227565041010948771 5083810841347561516423157)
                ·
                  refine ⟨476607266376333892164671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083810841347561516423157 476607266376333892164671)
                  ·
                    rfl

theorem cell21_2088426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2088426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088426 prefixEnd_2088426 := by exact prefixLift 2088426
  have htrace : WordTrace (prefixWord ++ tailWord_2088426) baseStart_2088426 baseEnd_2088426 := by
    simpa [prefixWord, tailWord_2088426, baseEnd_2088426] using wordTrace_append hprefix tailTrace_2088426
  have hstable : (prefixWord ++ tailWord_2088426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088426).length < 2 ^ (prefixWord ++ tailWord_2088426).sum := by decide
  have hdescent : baseEnd_2088426 < baseStart_2088426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088440 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_2088440 : Nat := 118140960795 + 2088440 * 2 ^ 59
def prefixEnd_2088440 : Nat := 4983230072969 + 3 ^ 40 * 2088440 * 2
def baseEnd_2088440 : Nat := 476610461367072978931309

theorem tailTrace_2088440 : CollatzResearch.WordTrace tailWord_2088440 prefixEnd_2088440 476610461367072978931309 := by
  unfold tailWord_2088440
  simp only [CollatzResearch.WordTrace]
  refine ⟨38085832276973016000295387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50781109702630688000393849 38085832276973016000295387)
  ·
    refine ⟨57128748415459524000443081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38085832276973016000295387 57128748415459524000443081)
    ·
      refine ⟨42846561311594643000332311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57128748415459524000443081 42846561311594643000332311)
      ·
        refine ⟨64269841967391964500498467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42846561311594643000332311 64269841967391964500498467)
        ·
          refine ⟨96404762951087946750747701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64269841967391964500498467 96404762951087946750747701)
          ·
            refine ⟨9037946526664495007882597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96404762951087946750747701 9037946526664495007882597)
            ·
              refine ⟨1694614973749592813977987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9037946526664495007882597 1694614973749592813977987)
              ·
                refine ⟨2541922460624389220966981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694614973749592813977987 2541922460624389220966981)
                ·
                  refine ⟨476610461367072978931309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541922460624389220966981 476610461367072978931309)
                  ·
                    rfl

theorem cell21_2088440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_2088440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088440 prefixEnd_2088440 := by exact prefixLift 2088440
  have htrace : WordTrace (prefixWord ++ tailWord_2088440) baseStart_2088440 baseEnd_2088440 := by
    simpa [prefixWord, tailWord_2088440, baseEnd_2088440] using wordTrace_append hprefix tailTrace_2088440
  have hstable : (prefixWord ++ tailWord_2088440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088440).length < 2 ^ (prefixWord ++ tailWord_2088440).sum := by decide
  have hdescent : baseEnd_2088440 < baseStart_2088440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088488 : List Nat := [2, 1, 5, 2, 3, 1, 1, 6]
def baseStart_2088488 : Nat := 118140960795 + 2088488 * 2 ^ 59
def prefixEnd_2088488 : Nat := 4983230072969 + 3 ^ 40 * 2088488 * 2
def baseEnd_2088488 : Nat := 158873805207011854043737

theorem tailTrace_2088488 : CollatzResearch.WordTrace tailWord_2088488 prefixEnd_2088488 158873805207011854043737 := by
  unfold tailWord_2088488
  simp only [CollatzResearch.WordTrace]
  refine ⟨38086707628886068099169059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50782276838514757465558745 38086707628886068099169059)
  ·
    refine ⟨57130061443329102148753589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38086707628886068099169059 57130061443329102148753589)
    ·
      refine ⟨5355943260312103326445649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57130061443329102148753589 5355943260312103326445649)
      ·
        refine ⟨4016957445234077494834237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5355943260312103326445649 4016957445234077494834237)
        ·
          refine ⟨1506359041962779060562839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4016957445234077494834237 1506359041962779060562839)
          ·
            refine ⟨2259538562944168590844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506359041962779060562839 2259538562944168590844259)
            ·
              refine ⟨3389307844416252886266389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259538562944168590844259 3389307844416252886266389)
              ·
                refine ⟨158873805207011854043737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3389307844416252886266389 158873805207011854043737)
                ·
                  rfl

theorem cell21_2088488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_2088488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088488 prefixEnd_2088488 := by exact prefixLift 2088488
  have htrace : WordTrace (prefixWord ++ tailWord_2088488) baseStart_2088488 baseEnd_2088488 := by
    simpa [prefixWord, tailWord_2088488, baseEnd_2088488] using wordTrace_append hprefix tailTrace_2088488
  have hstable : (prefixWord ++ tailWord_2088488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088488).length < 2 ^ (prefixWord ++ tailWord_2088488).sum := by decide
  have hdescent : baseEnd_2088488 < baseStart_2088488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088499 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_2088499 : Nat := 118140960795 + 2088499 * 2 ^ 59
def prefixEnd_2088499 : Nat := 4983230072969 + 3 ^ 40 * 2088499 * 2
def baseEnd_2088499 : Nat := 476623925970901987447855

theorem tailTrace_2088499 : CollatzResearch.WordTrace tailWord_2088499 prefixEnd_2088499 476623925970901987447855 := by
  unfold tailWord_2088499
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173816460732285076988551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50782544307154856717992367 76173816460732285076988551)
  ·
    refine ⟨114260724691098427615482827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76173816460732285076988551 114260724691098427615482827)
    ·
      refine ⟨171391087036647641423224241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114260724691098427615482827 171391087036647641423224241)
      ·
        refine ⟨128543315277485731067418181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171391087036647641423224241 128543315277485731067418181)
        ·
          refine ⟨24101871614528574575140909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128543315277485731067418181 24101871614528574575140909)
          ·
            refine ⟨9038201855448215465677841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24101871614528574575140909 9038201855448215465677841)
            ·
              refine ⟨6778651391586161599258381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9038201855448215465677841 6778651391586161599258381)
              ·
                refine ⟨2541994271844810599721893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6778651391586161599258381 2541994271844810599721893)
                ·
                  refine ⟨476623925970901987447855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541994271844810599721893 476623925970901987447855)
                  ·
                    rfl

theorem cell21_2088499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_2088499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088499 prefixEnd_2088499 := by exact prefixLift 2088499
  have htrace : WordTrace (prefixWord ++ tailWord_2088499) baseStart_2088499 baseEnd_2088499 := by
    simpa [prefixWord, tailWord_2088499, baseEnd_2088499] using wordTrace_append hprefix tailTrace_2088499
  have hstable : (prefixWord ++ tailWord_2088499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088499).length < 2 ^ (prefixWord ++ tailWord_2088499).sum := by decide
  have hdescent : baseEnd_2088499 < baseStart_2088499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088502 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2088502 : Nat := 118140960795 + 2088502 * 2 ^ 59
def prefixEnd_2088502 : Nat := 4983230072969 + 3 ^ 40 * 2088502 * 2
def baseEnd_2088502 : Nat := 476624610611774648897849

theorem tailTrace_2088502 : CollatzResearch.WordTrace tailWord_2088502 prefixEnd_2088502 476624610611774648897849 := by
  unfold tailWord_2088502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760870367482588536834235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50782617253147611059565173 4760870367482588536834235)
  ·
    refine ⟨7141305551223882805251353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4760870367482588536834235 7141305551223882805251353)
    ·
      refine ⟨5355979163417912103938515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7141305551223882805251353 5355979163417912103938515)
      ·
        refine ⟨8033968745126868155907773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355979163417912103938515 8033968745126868155907773)
        ·
          refine ⟨3012738279422575558465415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8033968745126868155907773 3012738279422575558465415)
          ·
            refine ⟨4519107419133863337698123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012738279422575558465415 4519107419133863337698123)
            ·
              refine ⟨6778661128700795006547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519107419133863337698123 6778661128700795006547185)
              ·
                refine ⟨5083995846525596254910389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6778661128700795006547185 5083995846525596254910389)
                ·
                  refine ⟨476624610611774648897849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083995846525596254910389 476624610611774648897849)
                  ·
                    rfl

theorem cell21_2088502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2088502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088502 prefixEnd_2088502 := by exact prefixLift 2088502
  have htrace : WordTrace (prefixWord ++ tailWord_2088502) baseStart_2088502 baseEnd_2088502 := by
    simpa [prefixWord, tailWord_2088502, baseEnd_2088502] using wordTrace_append hprefix tailTrace_2088502
  have hstable : (prefixWord ++ tailWord_2088502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088502).length < 2 ^ (prefixWord ++ tailWord_2088502).sum := by decide
  have hdescent : baseEnd_2088502 < baseStart_2088502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088527 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_2088527 : Nat := 118140960795 + 2088527 * 2 ^ 59
def prefixEnd_2088527 : Nat := 4983230072969 + 3 ^ 40 * 2088527 * 2
def baseEnd_2088527 : Nat := 476630315952380160981131

theorem tailTrace_2088527 : CollatzResearch.WordTrace tailWord_2088527 prefixEnd_2088527 476630315952380160981131 := by
  unfold tailWord_2088527
  simp only [CollatzResearch.WordTrace]
  refine ⟨76174837704630845859007835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50783225136420563906005223 76174837704630845859007835)
  ·
    refine ⟨114262256556946268788511753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76174837704630845859007835 114262256556946268788511753)
    ·
      refine ⟨85696692417709701591383815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114262256556946268788511753 85696692417709701591383815)
      ·
        refine ⟨128545038626564552387075723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85696692417709701591383815 128545038626564552387075723)
        ·
          refine ⟨192817557939846828580613585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128545038626564552387075723 192817557939846828580613585)
          ·
            refine ⟨144613168454885121435460189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192817557939846828580613585 144613168454885121435460189)
            ·
              refine ⟨54229938170581920538297571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144613168454885121435460189 54229938170581920538297571)
              ·
                refine ⟨81344907255872880807446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54229938170581920538297571 81344907255872880807446357)
                ·
                  refine ⟨476630315952380160981131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81344907255872880807446357 476630315952380160981131)
                  ·
                    rfl

theorem cell21_2088527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_2088527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088527 prefixEnd_2088527 := by exact prefixLift 2088527
  have htrace : WordTrace (prefixWord ++ tailWord_2088527) baseStart_2088527 baseEnd_2088527 := by
    simpa [prefixWord, tailWord_2088527, baseEnd_2088527] using wordTrace_append hprefix tailTrace_2088527
  have hstable : (prefixWord ++ tailWord_2088527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088527).length < 2 ^ (prefixWord ++ tailWord_2088527).sum := by decide
  have hdescent : baseEnd_2088527 < baseStart_2088527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088606 : List Nat := [4, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2088606 : Nat := 118140960795 + 2088606 * 2 ^ 59
def prefixEnd_2088606 : Nat := 4983230072969 + 3 ^ 40 * 2088606 * 2
def baseEnd_2088606 : Nat := 158882781609564526388101

theorem tailTrace_2088606 : CollatzResearch.WordTrace tailWord_2088606 prefixEnd_2088606 158882781609564526388101 := by
  unfold tailWord_2088606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522214883918080293891709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50785146047563094900755781 9522214883918080293891709)
  ·
    refine ⟨3570830581469280110209391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9522214883918080293891709 3570830581469280110209391)
    ·
      refine ⟨5356245872203920165314087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570830581469280110209391 5356245872203920165314087)
      ·
        refine ⟨8034368808305880247971131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356245872203920165314087 8034368808305880247971131)
        ·
          refine ⟨12051553212458820371956697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034368808305880247971131 12051553212458820371956697)
          ·
            refine ⟨9038664909344115278967523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12051553212458820371956697 9038664909344115278967523)
            ·
              refine ⟨13557997364016172918451285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038664909344115278967523 13557997364016172918451285)
              ·
                refine ⟨158882781609564526388101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13557997364016172918451285 158882781609564526388101)
                ·
                  rfl

theorem cell21_2088606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2088606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088606 prefixEnd_2088606 := by exact prefixLift 2088606
  have htrace : WordTrace (prefixWord ++ tailWord_2088606) baseStart_2088606 baseEnd_2088606 := by
    simpa [prefixWord, tailWord_2088606, baseEnd_2088606] using wordTrace_append hprefix tailTrace_2088606
  have hstable : (prefixWord ++ tailWord_2088606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088606).length < 2 ^ (prefixWord ++ tailWord_2088606).sum := by decide
  have hdescent : baseEnd_2088606 < baseStart_2088606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088609 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2088609 : Nat := 118140960795 + 2088609 * 2 ^ 59
def prefixEnd_2088609 : Nat := 4983230072969 + 3 ^ 40 * 2088609 * 2
def baseEnd_2088609 : Nat := 476649029469566240614297

theorem tailTrace_2088609 : CollatzResearch.WordTrace tailWord_2088609 prefixEnd_2088609 476649029469566240614297 := by
  unfold tailWord_2088609
  simp only [CollatzResearch.WordTrace]
  refine ⟨76177828490333773863492881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50785218993555849242328587 76177828490333773863492881)
  ·
    refine ⟨57133371367750330397619661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76177828490333773863492881 57133371367750330397619661)
    ·
      refine ⟨21425014262906373899107373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57133371367750330397619661 21425014262906373899107373)
      ·
        refine ⟨8034380348589890212165265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21425014262906373899107373 8034380348589890212165265)
        ·
          refine ⟨6025785261442417659123949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8034380348589890212165265 6025785261442417659123949)
          ·
            refine ⟨2259669473040906622171481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6025785261442417659123949 2259669473040906622171481)
            ·
              refine ⟨1694752104780679966628611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259669473040906622171481 1694752104780679966628611)
              ·
                refine ⟨2542128157171019949942917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694752104780679966628611 2542128157171019949942917)
                ·
                  refine ⟨476649029469566240614297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542128157171019949942917 476649029469566240614297)
                  ·
                    rfl

theorem cell21_2088609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2088609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088609 prefixEnd_2088609 := by exact prefixLift 2088609
  have htrace : WordTrace (prefixWord ++ tailWord_2088609) baseStart_2088609 baseEnd_2088609 := by
    simpa [prefixWord, tailWord_2088609, baseEnd_2088609] using wordTrace_append hprefix tailTrace_2088609
  have hstable : (prefixWord ++ tailWord_2088609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088609).length < 2 ^ (prefixWord ++ tailWord_2088609).sum := by decide
  have hdescent : baseEnd_2088609 < baseStart_2088609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088637 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2088637 : Nat := 118140960795 + 2088637 * 2 ^ 59
def prefixEnd_2088637 : Nat := 4983230072969 + 3 ^ 40 * 2088637 * 2
def baseEnd_2088637 : Nat := 476655419451044414147573

theorem tailTrace_2088637 : CollatzResearch.WordTrace tailWord_2088637 prefixEnd_2088637 476655419451044414147573 := by
  unfold tailWord_2088637
  simp only [CollatzResearch.WordTrace]
  refine ⟨76178849734232334645512165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50785899822821556430341443 76178849734232334645512165)
  ·
    refine ⟨14283534325168562746033531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76178849734232334645512165 14283534325168562746033531)
    ·
      refine ⟨21425301487752844119050297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283534325168562746033531 21425301487752844119050297)
      ·
        refine ⟨16068976115814633089287723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21425301487752844119050297 16068976115814633089287723)
        ·
          refine ⟨24103464173721949633931585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068976115814633089287723 24103464173721949633931585)
          ·
            refine ⟨18077598130291462225448689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24103464173721949633931585 18077598130291462225448689)
            ·
              refine ⟨13558198597718596669086517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18077598130291462225448689 13558198597718596669086517)
              ·
                refine ⟨1271081118536118437726861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13558198597718596669086517 1271081118536118437726861)
                ·
                  refine ⟨476655419451044414147573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271081118536118437726861 476655419451044414147573)
                  ·
                    rfl

theorem cell21_2088637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2088637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088637 prefixEnd_2088637 := by exact prefixLift 2088637
  have htrace : WordTrace (prefixWord ++ tailWord_2088637) baseStart_2088637 baseEnd_2088637 := by
    simpa [prefixWord, tailWord_2088637, baseEnd_2088637] using wordTrace_append hprefix tailTrace_2088637
  have hstable : (prefixWord ++ tailWord_2088637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088637).length < 2 ^ (prefixWord ++ tailWord_2088637).sum := by decide
  have hdescent : baseEnd_2088637 < baseStart_2088637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088665 : List Nat := [1, 2, 1, 2, 3, 3, 3, 6]
def baseStart_2088665 : Nat := 118140960795 + 2088665 * 2 ^ 59
def prefixEnd_2088665 : Nat := 4983230072969 + 3 ^ 40 * 2088665 * 2
def baseEnd_2088665 : Nat := 158887269810840862560283

theorem tailTrace_2088665 : CollatzResearch.WordTrace tailWord_2088665 prefixEnd_2088665 158887269810840862560283 := by
  unfold tailWord_2088665
  simp only [CollatzResearch.WordTrace]
  refine ⟨76179870978130895427531449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50786580652087263618354299 76179870978130895427531449)
  ·
    refine ⟨57134903233598171570648587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76179870978130895427531449 57134903233598171570648587)
    ·
      refine ⟨85702354850397257355972881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57134903233598171570648587 85702354850397257355972881)
      ·
        refine ⟨64276766137797943016979661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85702354850397257355972881 64276766137797943016979661)
        ·
          refine ⟨24103787301674228631367373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64276766137797943016979661 24103787301674228631367373)
          ·
            refine ⟨9038920238127835736762765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24103787301674228631367373 9038920238127835736762765)
            ·
              refine ⟨3389595089297938401286037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9038920238127835736762765 3389595089297938401286037)
              ·
                refine ⟨158887269810840862560283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3389595089297938401286037 158887269810840862560283)
                ·
                  rfl

theorem cell21_2088665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_2088665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088665 prefixEnd_2088665 := by exact prefixLift 2088665
  have htrace : WordTrace (prefixWord ++ tailWord_2088665) baseStart_2088665 baseEnd_2088665 := by
    simpa [prefixWord, tailWord_2088665, baseEnd_2088665] using wordTrace_append hprefix tailTrace_2088665
  have hstable : (prefixWord ++ tailWord_2088665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088665).length < 2 ^ (prefixWord ++ tailWord_2088665).sum := by decide
  have hdescent : baseEnd_2088665 < baseStart_2088665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088702 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2088702 : Nat := 118140960795 + 2088702 * 2 ^ 59
def prefixEnd_2088702 : Nat := 4983230072969 + 3 ^ 40 * 2088702 * 2
def baseEnd_2088702 : Nat := 476670253336618745564107

theorem tailTrace_2088702 : CollatzResearch.WordTrace tailWord_2088702 prefixEnd_2088702 476670253336618745564107 := by
  unfold tailWord_2088702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522652559874606343328545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50787480319331233831085573 9522652559874606343328545)
  ·
    refine ⟨7141989419905954757496409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9522652559874606343328545 7141989419905954757496409)
    ·
      refine ⟨5356492064929466068122307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7141989419905954757496409 5356492064929466068122307)
      ·
        refine ⟨8034738097394199102183461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356492064929466068122307 8034738097394199102183461)
        ·
          refine ⟨1506513393261412331659399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8034738097394199102183461 1506513393261412331659399)
          ·
            refine ⟨2259770089892118497489099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506513393261412331659399 2259770089892118497489099)
            ·
              refine ⟨3389655134838177746233649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259770089892118497489099 3389655134838177746233649)
              ·
                refine ⟨2542241351128633309675237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3389655134838177746233649 2542241351128633309675237)
                ·
                  refine ⟨476670253336618745564107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542241351128633309675237 476670253336618745564107)
                  ·
                    rfl

theorem cell21_2088702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2088702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088702 prefixEnd_2088702 := by exact prefixLift 2088702
  have htrace : WordTrace (prefixWord ++ tailWord_2088702) baseStart_2088702 baseEnd_2088702 := by
    simpa [prefixWord, tailWord_2088702, baseEnd_2088702] using wordTrace_append hprefix tailTrace_2088702
  have hstable : (prefixWord ++ tailWord_2088702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088702).length < 2 ^ (prefixWord ++ tailWord_2088702).sum := by decide
  have hdescent : baseEnd_2088702 < baseStart_2088702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088741 : List Nat := [1, 3, 1, 2, 3, 3, 1, 7]
def baseStart_2088741 : Nat := 118140960795 + 2088741 * 2 ^ 59
def prefixEnd_2088741 : Nat := 4983230072969 + 3 ^ 40 * 2088741 * 2
def baseEnd_2088741 : Nat := 158893051222654448138009

theorem tailTrace_2088741 : CollatzResearch.WordTrace tailWord_2088741 prefixEnd_2088741 158893051222654448138009 := by
  unfold tailWord_2088741
  simp only [CollatzResearch.WordTrace]
  refine ⟨76182642925855560407298077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50788428617237040271532051 76182642925855560407298077)
  ·
    refine ⟨28568491097195835152736779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76182642925855560407298077 28568491097195835152736779)
    ·
      refine ⟨42852736645793752729105169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28568491097195835152736779 42852736645793752729105169)
      ·
        refine ⟨32139552484345314546828877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42852736645793752729105169 32139552484345314546828877)
        ·
          refine ⟨12052332181629492955060829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32139552484345314546828877 12052332181629492955060829)
          ·
            refine ⟨4519624568111059858147811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12052332181629492955060829 4519624568111059858147811)
            ·
              refine ⟨6779436852166589787221717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519624568111059858147811 6779436852166589787221717)
              ·
                refine ⟨158893051222654448138009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6779436852166589787221717 158893051222654448138009)
                ·
                  rfl

theorem cell21_2088741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_2088741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088741 prefixEnd_2088741 := by exact prefixLift 2088741
  have htrace : WordTrace (prefixWord ++ tailWord_2088741) baseStart_2088741 baseEnd_2088741 := by
    simpa [prefixWord, tailWord_2088741, baseEnd_2088741] using wordTrace_append hprefix tailTrace_2088741
  have hstable : (prefixWord ++ tailWord_2088741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088741).length < 2 ^ (prefixWord ++ tailWord_2088741).sum := by decide
  have hdescent : baseEnd_2088741 < baseStart_2088741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088758 : List Nat := [5, 1, 2, 2, 1, 1, 9]
def baseStart_2088758 : Nat := 118140960795 + 2088758 * 2 ^ 59
def prefixEnd_2088758 : Nat := 4983230072969 + 3 ^ 40 * 2088758 * 2
def baseEnd_2088758 : Nat := 52964781477730565847851

theorem tailTrace_2088758 : CollatzResearch.WordTrace tailWord_2088758 prefixEnd_2088758 52964781477730565847851 := by
  unfold tailWord_2088758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761453935424623269416683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50788841977862648207111285 4761453935424623269416683)
  ·
    refine ⟨7142180903136934904125025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4761453935424623269416683 7142180903136934904125025)
    ·
      refine ⟨5356635677352701178093769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7142180903136934904125025 5356635677352701178093769)
      ·
        refine ⟨4017476758014525883570327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5356635677352701178093769 4017476758014525883570327)
        ·
          refine ⟨6026215137021788825355491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017476758014525883570327 6026215137021788825355491)
          ·
            refine ⟨9039322705532683238033237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026215137021788825355491 9039322705532683238033237)
            ·
              refine ⟨52964781477730565847851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9039322705532683238033237 52964781477730565847851)
              ·
                rfl

theorem cell21_2088758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 9].length) (baseStart_2088758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088758 prefixEnd_2088758 := by exact prefixLift 2088758
  have htrace : WordTrace (prefixWord ++ tailWord_2088758) baseStart_2088758 baseEnd_2088758 := by
    simpa [prefixWord, tailWord_2088758, baseEnd_2088758] using wordTrace_append hprefix tailTrace_2088758
  have hstable : (prefixWord ++ tailWord_2088758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088758).length < 2 ^ (prefixWord ++ tailWord_2088758).sum := by decide
  have hdescent : baseEnd_2088758 < baseStart_2088758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088831 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_2088831 : Nat := 118140960795 + 2088831 * 2 ^ 59
def prefixEnd_2088831 : Nat := 4983230072969 + 3 ^ 40 * 2088831 * 2
def baseEnd_2088831 : Nat := 476699692894143187913843

theorem tailTrace_2088831 : CollatzResearch.WordTrace tailWord_2088831 prefixEnd_2088831 476699692894143187913843 := by
  unfold tailWord_2088831
  simp only [CollatzResearch.WordTrace]
  refine ⟨76185925495529505778074347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50790616997019670518716231 76185925495529505778074347)
  ·
    refine ⟨114278888243294258667111521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76185925495529505778074347 114278888243294258667111521)
    ·
      refine ⟨85709166182470694000333641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114278888243294258667111521 85709166182470694000333641)
      ·
        refine ⟨64281874636853020500250231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85709166182470694000333641 64281874636853020500250231)
        ·
          refine ⟨96422811955279530750375347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64281874636853020500250231 96422811955279530750375347)
          ·
            refine ⟨144634217932919296125563021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96422811955279530750375347 144634217932919296125563021)
            ·
              refine ⟨54237831724844736047086133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144634217932919296125563021 54237831724844736047086133)
              ·
                refine ⟨5084796724204194004414325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54237831724844736047086133 5084796724204194004414325)
                ·
                  refine ⟨476699692894143187913843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5084796724204194004414325 476699692894143187913843)
                  ·
                    rfl

theorem cell21_2088831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_2088831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088831 prefixEnd_2088831 := by exact prefixLift 2088831
  have htrace : WordTrace (prefixWord ++ tailWord_2088831) baseStart_2088831 baseEnd_2088831 := by
    simpa [prefixWord, tailWord_2088831, baseEnd_2088831] using wordTrace_append hprefix tailTrace_2088831
  have hstable : (prefixWord ++ tailWord_2088831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088831).length < 2 ^ (prefixWord ++ tailWord_2088831).sum := by decide
  have hdescent : baseEnd_2088831 < baseStart_2088831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088907 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_2088907 : Nat := 118140960795 + 2088907 * 2 ^ 59
def prefixEnd_2088907 : Nat := 4983230072969 + 3 ^ 40 * 2088907 * 2
def baseEnd_2088907 : Nat := 476717037129583944647021

theorem tailTrace_2088907 : CollatzResearch.WordTrace tailWord_2088907 prefixEnd_2088907 476717037129583944647021 := by
  unfold tailWord_2088907
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188697443254170757840975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50792464962169447171893983 76188697443254170757840975)
  ·
    refine ⟨114283046164881256136761463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76188697443254170757840975 114283046164881256136761463)
    ·
      refine ⟨171424569247321884205142195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114283046164881256136761463 171424569247321884205142195)
      ·
        refine ⟨257136853870982826307713293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171424569247321884205142195 257136853870982826307713293)
        ·
          refine ⟨96426320201618559865392485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257136853870982826307713293 96426320201618559865392485)
          ·
            refine ⟨18079935037803479974761091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96426320201618559865392485 18079935037803479974761091)
            ·
              refine ⟨27119902556705219962141637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079935037803479974761091 27119902556705219962141637)
              ·
                refine ⟨5084981729382228742901557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27119902556705219962141637 5084981729382228742901557)
                ·
                  refine ⟨476717037129583944647021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5084981729382228742901557 476717037129583944647021)
                  ·
                    rfl

theorem cell21_2088907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_2088907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088907 prefixEnd_2088907 := by exact prefixLift 2088907
  have htrace : WordTrace (prefixWord ++ tailWord_2088907) baseStart_2088907 baseEnd_2088907 := by
    simpa [prefixWord, tailWord_2088907, baseEnd_2088907] using wordTrace_append hprefix tailTrace_2088907
  have hstable : (prefixWord ++ tailWord_2088907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088907).length < 2 ^ (prefixWord ++ tailWord_2088907).sum := by decide
  have hdescent : baseEnd_2088907 < baseStart_2088907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088938 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_2088938 : Nat := 118140960795 + 2088938 * 2 ^ 59
def prefixEnd_2088938 : Nat := 4983230072969 + 3 ^ 40 * 2088938 * 2
def baseEnd_2088938 : Nat := 476724111751934779630291

theorem tailTrace_2088938 : CollatzResearch.WordTrace tailWord_2088938 prefixEnd_2088938 476724111751934779630291 := by
  unfold tailWord_2088938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19047457026535465763054867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50793218737427908701479645 19047457026535465763054867)
  ·
    refine ⟨28571185539803198644582301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19047457026535465763054867 28571185539803198644582301)
    ·
      refine ⟨10714194577426199491718363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28571185539803198644582301 10714194577426199491718363)
      ·
        refine ⟨16071291866139299237577545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714194577426199491718363 16071291866139299237577545)
        ·
          refine ⟨12053468899604474428183159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16071291866139299237577545 12053468899604474428183159)
          ·
            refine ⟨18080203349406711642274739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12053468899604474428183159 18080203349406711642274739)
            ·
              refine ⟨27120305024110067463412109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18080203349406711642274739 27120305024110067463412109)
              ·
                refine ⟨10170114384041275298779541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27120305024110067463412109 10170114384041275298779541)
                ·
                  refine ⟨476724111751934779630291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10170114384041275298779541 476724111751934779630291)
                  ·
                    rfl

theorem cell21_2088938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_2088938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088938 prefixEnd_2088938 := by exact prefixLift 2088938
  have htrace : WordTrace (prefixWord ++ tailWord_2088938) baseStart_2088938 baseEnd_2088938 := by
    simpa [prefixWord, tailWord_2088938, baseEnd_2088938] using wordTrace_append hprefix tailTrace_2088938
  have hstable : (prefixWord ++ tailWord_2088938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088938).length < 2 ^ (prefixWord ++ tailWord_2088938).sum := by decide
  have hdescent : baseEnd_2088938 < baseStart_2088938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088952 : List Nat := [2, 1, 2, 1, 1, 3, 3, 8]
def baseStart_2088952 : Nat := 118140960795 + 2088952 * 2 ^ 59
def prefixEnd_2088952 : Nat := 4983230072969 + 3 ^ 40 * 2088952 * 2
def baseEnd_2088952 : Nat := 158909102247557955465643

theorem tailTrace_2088952 : CollatzResearch.WordTrace tailWord_2088952 prefixEnd_2088952 158909102247557955465643 := by
  unfold tailWord_2088952
  simp only [CollatzResearch.WordTrace]
  refine ⟨38095169364045571721614555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50793559152060762295486073 38095169364045571721614555)
  ·
    refine ⟨57142754046068357582421833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38095169364045571721614555 57142754046068357582421833)
    ·
      refine ⟨42857065534551268186816375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57142754046068357582421833 42857065534551268186816375)
      ·
        refine ⟨64285598301826902280224563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42857065534551268186816375 64285598301826902280224563)
        ·
          refine ⟨96428397452740353420336845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64285598301826902280224563 96428397452740353420336845)
          ·
            refine ⟨36160649044777632532626317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96428397452740353420336845 36160649044777632532626317)
            ·
              refine ⟨13560243391791612199734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36160649044777632532626317 13560243391791612199734869)
              ·
                refine ⟨158909102247557955465643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13560243391791612199734869 158909102247557955465643)
                ·
                  rfl

theorem cell21_2088952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_2088952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088952 prefixEnd_2088952 := by exact prefixLift 2088952
  have htrace : WordTrace (prefixWord ++ tailWord_2088952) baseStart_2088952 baseEnd_2088952 := by
    simpa [prefixWord, tailWord_2088952, baseEnd_2088952] using wordTrace_append hprefix tailTrace_2088952
  have hstable : (prefixWord ++ tailWord_2088952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088952).length < 2 ^ (prefixWord ++ tailWord_2088952).sum := by decide
  have hdescent : baseEnd_2088952 < baseStart_2088952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2088955 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 4]
def baseStart_2088955 : Nat := 118140960795 + 2088955 * 2 ^ 59
def prefixEnd_2088955 : Nat := 4983230072969 + 3 ^ 40 * 2088955 * 2
def baseEnd_2088955 : Nat := 476727991383546527846923

theorem tailTrace_2088955 : CollatzResearch.WordTrace tailWord_2088955 prefixEnd_2088955 476727991383546527846923 := by
  unfold tailWord_2088955
  simp only [CollatzResearch.WordTrace]
  refine ⟨76190448147080274955588319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50793632098053516637058879 76190448147080274955588319)
  ·
    refine ⟨114285672220620412433382479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76190448147080274955588319 114285672220620412433382479)
    ·
      refine ⟨171428508330930618650073719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114285672220620412433382479 171428508330930618650073719)
      ·
        refine ⟨257142762496395927975110579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171428508330930618650073719 257142762496395927975110579)
        ·
          refine ⟨385714143744593891962665869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257142762496395927975110579 385714143744593891962665869)
          ·
            refine ⟨144642803904222709485999701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385714143744593891962665869 144642803904222709485999701)
            ·
              refine ⟨1695032858252609876789059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 144642803904222709485999701 1695032858252609876789059)
              ·
                refine ⟨2542549287378914815183589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695032858252609876789059 2542549287378914815183589)
                ·
                  refine ⟨476727991383546527846923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542549287378914815183589 476727991383546527846923)
                  ·
                    rfl

theorem cell21_2088955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_2088955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2088955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2088955 prefixEnd_2088955 := by exact prefixLift 2088955
  have htrace : WordTrace (prefixWord ++ tailWord_2088955) baseStart_2088955 baseEnd_2088955 := by
    simpa [prefixWord, tailWord_2088955, baseEnd_2088955] using wordTrace_append hprefix tailTrace_2088955
  have hstable : (prefixWord ++ tailWord_2088955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2088955).length < 2 ^ (prefixWord ++ tailWord_2088955).sum := by decide
  have hdescent : baseEnd_2088955 < baseStart_2088955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2088955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089059 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_2089059 : Nat := 118140960795 + 2089059 * 2 ^ 59
def prefixEnd_2089059 : Nat := 4983230072969 + 3 ^ 40 * 2089059 * 2
def baseEnd_2089059 : Nat := 476751725600465458113377

theorem tailTrace_2089059 : CollatzResearch.WordTrace tailWord_2089059 prefixEnd_2089059 476751725600465458113377 := by
  unfold tailWord_2089059
  simp only [CollatzResearch.WordTrace]
  refine ⟨76194241338703500717374231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50796160892469000478249487 76194241338703500717374231)
  ·
    refine ⟨114291362008055251076061347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76194241338703500717374231 114291362008055251076061347)
    ·
      refine ⟨171437043012082876614092021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114291362008055251076061347 171437043012082876614092021)
      ·
        refine ⟨16072222782382769682571127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171437043012082876614092021 16072222782382769682571127)
        ·
          refine ⟨24108334173574154523856691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072222782382769682571127 24108334173574154523856691)
          ·
            refine ⟨36162501260361231785785037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108334173574154523856691 36162501260361231785785037)
            ·
              refine ⟨13560937972635461919669389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36162501260361231785785037 13560937972635461919669389)
              ·
                refine ⟨5085351739738298219876021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13560937972635461919669389 5085351739738298219876021)
                ·
                  refine ⟨476751725600465458113377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085351739738298219876021 476751725600465458113377)
                  ·
                    rfl

theorem cell21_2089059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_2089059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089059 prefixEnd_2089059 := by exact prefixLift 2089059
  have htrace : WordTrace (prefixWord ++ tailWord_2089059) baseStart_2089059 baseEnd_2089059 := by
    simpa [prefixWord, tailWord_2089059, baseEnd_2089059] using wordTrace_append hprefix tailTrace_2089059
  have hstable : (prefixWord ++ tailWord_2089059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089059).length < 2 ^ (prefixWord ++ tailWord_2089059).sum := by decide
  have hdescent : baseEnd_2089059 < baseStart_2089059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089093 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 3]
def baseStart_2089093 : Nat := 118140960795 + 2089093 * 2 ^ 59
def prefixEnd_2089093 : Nat := 4983230072969 + 3 ^ 40 * 2089093 * 2
def baseEnd_2089093 : Nat := 476759484863688954546641

theorem tailTrace_2089093 : CollatzResearch.WordTrace tailWord_2089093 prefixEnd_2089093 476759484863688954546641 := by
  unfold tailWord_2089093
  simp only [CollatzResearch.WordTrace]
  refine ⟨76195481420580324524111933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50796987613720216349407955 76195481420580324524111933)
  ·
    refine ⟨28573305532717621696541975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76195481420580324524111933 28573305532717621696541975)
    ·
      refine ⟨42859958299076432544812963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28573305532717621696541975 42859958299076432544812963)
      ·
        refine ⟨64289937448614648817219445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42859958299076432544812963 64289937448614648817219445)
        ·
          refine ⟨6027181635807623326614323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64289937448614648817219445 6027181635807623326614323)
          ·
            refine ⟨9040772453711434989921485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027181635807623326614323 9040772453711434989921485)
            ·
              refine ⟨3390289670141788121220557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9040772453711434989921485 3390289670141788121220557)
              ·
                refine ⟨1271358626303170545457709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3390289670141788121220557 1271358626303170545457709)
                ·
                  refine ⟨476759484863688954546641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271358626303170545457709 476759484863688954546641)
                  ·
                    rfl

theorem cell21_2089093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_2089093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089093 prefixEnd_2089093 := by exact prefixLift 2089093
  have htrace : WordTrace (prefixWord ++ tailWord_2089093) baseStart_2089093 baseEnd_2089093 := by
    simpa [prefixWord, tailWord_2089093, baseEnd_2089093] using wordTrace_append hprefix tailTrace_2089093
  have hstable : (prefixWord ++ tailWord_2089093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089093).length < 2 ^ (prefixWord ++ tailWord_2089093).sum := by decide
  have hdescent : baseEnd_2089093 < baseStart_2089093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089121 : List Nat := [1, 2, 3, 3, 1, 3, 2, 6]
def baseStart_2089121 : Nat := 118140960795 + 2089121 * 2 ^ 59
def prefixEnd_2089121 : Nat := 4983230072969 + 3 ^ 40 * 2089121 * 2
def baseEnd_2089121 : Nat := 158921958281722376026639

theorem tailTrace_2089121 : CollatzResearch.WordTrace tailWord_2089121 prefixEnd_2089121 158921958281722376026639 := by
  unfold tailWord_2089121
  simp only [CollatzResearch.WordTrace]
  refine ⟨76196502664478885306131217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50797668442985923537420811 76196502664478885306131217)
  ·
    refine ⟨57147376998359163979598413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76196502664478885306131217 57147376998359163979598413)
    ·
      refine ⟨21430266374384686492349405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57147376998359163979598413 21430266374384686492349405)
      ·
        refine ⟨8036349890394257434631027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21430266374384686492349405 8036349890394257434631027)
        ·
          refine ⟨12054524835591386151946541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036349890394257434631027 12054524835591386151946541)
          ·
            refine ⟨4520446813346769806979953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12054524835591386151946541 4520446813346769806979953)
            ·
              refine ⟨3390335110010077355234965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4520446813346769806979953 3390335110010077355234965)
              ·
                refine ⟨158921958281722376026639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3390335110010077355234965 158921958281722376026639)
                ·
                  rfl

theorem cell21_2089121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_2089121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089121 prefixEnd_2089121 := by exact prefixLift 2089121
  have htrace : WordTrace (prefixWord ++ tailWord_2089121) baseStart_2089121 baseEnd_2089121 := by
    simpa [prefixWord, tailWord_2089121, baseEnd_2089121] using wordTrace_append hprefix tailTrace_2089121
  have hstable : (prefixWord ++ tailWord_2089121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089121).length < 2 ^ (prefixWord ++ tailWord_2089121).sum := by decide
  have hdescent : baseEnd_2089121 < baseStart_2089121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089169 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 3]
def baseStart_2089169 : Nat := 118140960795 + 2089169 * 2 ^ 59
def prefixEnd_2089169 : Nat := 4983230072969 + 3 ^ 40 * 2089169 * 2
def baseEnd_2089169 : Nat := 476776829099129711279819

theorem tailTrace_2089169 : CollatzResearch.WordTrace tailWord_2089169 prefixEnd_2089169 476776829099129711279819 := by
  unfold tailWord_2089169
  simp only [CollatzResearch.WordTrace]
  refine ⟨76198253368304989503878561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50798835578869993002585707 76198253368304989503878561)
  ·
    refine ⟨57148690026228742127908921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76198253368304989503878561 57148690026228742127908921)
    ·
      refine ⟨42861517519671556595931691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57148690026228742127908921 42861517519671556595931691)
      ·
        refine ⟨64292276279507334893897537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42861517519671556595931691 64292276279507334893897537)
        ·
          refine ⟨48219207209630501170423153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64292276279507334893897537 48219207209630501170423153)
          ·
            refine ⟨36164405407222875877817365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48219207209630501170423153 36164405407222875877817365)
            ·
              refine ⟨1695206503463572306772689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36164405407222875877817365 1695206503463572306772689)
              ·
                refine ⟨1271404877597679230079517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695206503463572306772689 1271404877597679230079517)
                ·
                  refine ⟨476776829099129711279819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271404877597679230079517 476776829099129711279819)
                  ·
                    rfl

theorem cell21_2089169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_2089169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089169 prefixEnd_2089169 := by exact prefixLift 2089169
  have htrace : WordTrace (prefixWord ++ tailWord_2089169) baseStart_2089169 baseEnd_2089169 := by
    simpa [prefixWord, tailWord_2089169, baseEnd_2089169] using wordTrace_append hprefix tailTrace_2089169
  have hstable : (prefixWord ++ tailWord_2089169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089169).length < 2 ^ (prefixWord ++ tailWord_2089169).sum := by decide
  have hdescent : baseEnd_2089169 < baseStart_2089169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089228 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_2089228 : Nat := 118140960795 + 2089228 * 2 ^ 59
def prefixEnd_2089228 : Nat := 4983230072969 + 3 ^ 40 * 2089228 * 2
def baseEnd_2089228 : Nat := 476790293702958719796365

theorem tailTrace_2089228 : CollatzResearch.WordTrace tailWord_2089228 prefixEnd_2089228 476790293702958719796365 := by
  unfold tailWord_2089228
  simp only [CollatzResearch.WordTrace]
  refine ⟨38100202637545621290138169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50800270183394161720184225 38100202637545621290138169)
  ·
    refine ⟨28575151978159215967603627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38100202637545621290138169 28575151978159215967603627)
    ·
      refine ⟨42862727967238823951405441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28575151978159215967603627 42862727967238823951405441)
      ·
        refine ⟨32147045975429117963554081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42862727967238823951405441 32147045975429117963554081)
        ·
          refine ⟨24110284481571838472665561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32147045975429117963554081 24110284481571838472665561)
          ·
            refine ⟨18082713361178878854499171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24110284481571838472665561 18082713361178878854499171)
            ·
              refine ⟨27124070041768318281748757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18082713361178878854499171 27124070041768318281748757)
              ·
                refine ⟨1271440783207889919456973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27124070041768318281748757 1271440783207889919456973)
                ·
                  refine ⟨476790293702958719796365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271440783207889919456973 476790293702958719796365)
                  ·
                    rfl

theorem cell21_2089228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_2089228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089228 prefixEnd_2089228 := by exact prefixLift 2089228
  have htrace : WordTrace (prefixWord ++ tailWord_2089228) baseStart_2089228 baseEnd_2089228 := by
    simpa [prefixWord, tailWord_2089228, baseEnd_2089228] using wordTrace_append hprefix tailTrace_2089228
  have hstable : (prefixWord ++ tailWord_2089228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089228).length < 2 ^ (prefixWord ++ tailWord_2089228).sum := by decide
  have hdescent : baseEnd_2089228 < baseStart_2089228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089273 : List Nat := [1, 2, 1, 6, 1, 3, 7]
def baseStart_2089273 : Nat := 118140960795 + 2089273 * 2 ^ 59
def prefixEnd_2089273 : Nat := 4983230072969 + 3 ^ 40 * 2089273 * 2
def baseEnd_2089273 : Nat := 52977840368449849060697

theorem tailTrace_2089273 : CollatzResearch.WordTrace tailWord_2089273 prefixEnd_2089273 52977840368449849060697 := by
  unfold tailWord_2089273
  simp only [CollatzResearch.WordTrace]
  refine ⟨76202046559928215265664473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50801364373285476843776315 76202046559928215265664473)
  ·
    refine ⟨57151534919946161449248355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76202046559928215265664473 57151534919946161449248355)
    ·
      refine ⟨85727302379919242173872533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57151534919946161449248355 85727302379919242173872533)
      ·
        refine ⟨4018467299058714476900275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85727302379919242173872533 4018467299058714476900275)
        ·
          refine ⟨6027700948588071715350413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018467299058714476900275 6027700948588071715350413)
          ·
            refine ⟨2260387855720526893256405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6027700948588071715350413 2260387855720526893256405)
            ·
              refine ⟨52977840368449849060697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2260387855720526893256405 52977840368449849060697)
              ·
                rfl

theorem cell21_2089273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 7].length) (baseStart_2089273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089273 prefixEnd_2089273 := by exact prefixLift 2089273
  have htrace : WordTrace (prefixWord ++ tailWord_2089273) baseStart_2089273 baseEnd_2089273 := by
    simpa [prefixWord, tailWord_2089273, baseEnd_2089273] using wordTrace_append hprefix tailTrace_2089273
  have hstable : (prefixWord ++ tailWord_2089273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089273).length < 2 ^ (prefixWord ++ tailWord_2089273).sum := by decide
  have hdescent : baseEnd_2089273 < baseStart_2089273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089380 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2089380 : Nat := 118140960795 + 2089380 * 2 ^ 59
def prefixEnd_2089380 : Nat := 4983230072969 + 3 ^ 40 * 2089380 * 2
def baseEnd_2089380 : Nat := 476824982173840233262721

theorem tailTrace_2089380 : CollatzResearch.WordTrace tailWord_2089380 prefixEnd_2089380 476824982173840233262721 := by
  unfold tailWord_2089380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102974585270286269904797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50803966113693715026539729 38102974585270286269904797)
  ·
    refine ⟨14288615469476357351214299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38102974585270286269904797 14288615469476357351214299)
    ·
      refine ⟨21432923204214536026821449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14288615469476357351214299 21432923204214536026821449)
      ·
        refine ⟨16074692403160902020116087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21432923204214536026821449 16074692403160902020116087)
        ·
          refine ⟨24112038604741353030174131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074692403160902020116087 24112038604741353030174131)
          ·
            refine ⟨36168057907112029545261197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112038604741353030174131 36168057907112029545261197)
            ·
              refine ⟨13563021715167011079472949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36168057907112029545261197 13563021715167011079472949)
              ·
                refine ⟨1271533285796907288700589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13563021715167011079472949 1271533285796907288700589)
                ·
                  refine ⟨476824982173840233262721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271533285796907288700589 476824982173840233262721)
                  ·
                    rfl

theorem cell21_2089380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2089380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089380 prefixEnd_2089380 := by exact prefixLift 2089380
  have htrace : WordTrace (prefixWord ++ tailWord_2089380) baseStart_2089380 baseEnd_2089380 := by
    simpa [prefixWord, tailWord_2089380, baseEnd_2089380] using wordTrace_append hprefix tailTrace_2089380
  have hstable : (prefixWord ++ tailWord_2089380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089380).length < 2 ^ (prefixWord ++ tailWord_2089380).sum := by decide
  have hdescent : baseEnd_2089380 < baseStart_2089380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089386 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2089386 : Nat := 118140960795 + 2089386 * 2 ^ 59
def prefixEnd_2089386 : Nat := 4983230072969 + 3 ^ 40 * 2089386 * 2
def baseEnd_2089386 : Nat := 476826351455585556162709

theorem tailTrace_2089386 : CollatzResearch.WordTrace tailWord_2089386 prefixEnd_2089386 476826351455585556162709 := by
  unfold tailWord_2089386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19051542002129708891132003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50804112005679223709685341 19051542002129708891132003)
  ·
    refine ⟨28577313003194563336698005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19051542002129708891132003 28577313003194563336698005)
    ·
      refine ⟨1339561547024745156407719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28577313003194563336698005 1339561547024745156407719)
      ·
        refine ⟨2009342320537117734611579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339561547024745156407719 2009342320537117734611579)
        ·
          refine ⟨3014013480805676601917369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009342320537117734611579 3014013480805676601917369)
          ·
            refine ⟨2260510110604257451438027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014013480805676601917369 2260510110604257451438027)
            ·
              refine ⟨3390765165906386177157041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260510110604257451438027 3390765165906386177157041)
              ·
                refine ⟨2543073874429789632867781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390765165906386177157041 2543073874429789632867781)
                ·
                  refine ⟨476826351455585556162709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543073874429789632867781 476826351455585556162709)
                  ·
                    rfl

theorem cell21_2089386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2089386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089386 prefixEnd_2089386 := by exact prefixLift 2089386
  have htrace : WordTrace (prefixWord ++ tailWord_2089386) baseStart_2089386 baseEnd_2089386 := by
    simpa [prefixWord, tailWord_2089386, baseEnd_2089386] using wordTrace_append hprefix tailTrace_2089386
  have hstable : (prefixWord ++ tailWord_2089386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089386).length < 2 ^ (prefixWord ++ tailWord_2089386).sum := by decide
  have hdescent : baseEnd_2089386 < baseStart_2089386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089484 : List Nat := [2, 2, 1, 2, 4, 1, 2, 7]
def baseStart_2089484 : Nat := 118140960795 + 2089484 * 2 ^ 59
def prefixEnd_2089484 : Nat := 4983230072969 + 3 ^ 40 * 2089484 * 2
def baseEnd_2089484 : Nat := 158949572130253054509725

theorem tailTrace_2089484 : CollatzResearch.WordTrace tailWord_2089484 prefixEnd_2089484 158949572130253054509725 := by
  unfold tailWord_2089484
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104871181081899150797753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50806494908109198867730337 38104871181081899150797753)
  ·
    refine ⟨28578653385811424363098315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38104871181081899150797753 28578653385811424363098315)
    ·
      refine ⟨42867980078717136544647473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28578653385811424363098315 42867980078717136544647473)
      ·
        refine ⟨32150985059037852408485605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42867980078717136544647473 32150985059037852408485605)
        ·
          refine ⟨6028309698569597326591051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32150985059037852408485605 6028309698569597326591051)
          ·
            refine ⟨9042464547854395989886577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028309698569597326591051 9042464547854395989886577)
            ·
              refine ⟨6781848410890796992414933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9042464547854395989886577 6781848410890796992414933)
              ·
                refine ⟨158949572130253054509725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6781848410890796992414933 158949572130253054509725)
                ·
                  rfl

theorem cell21_2089484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_2089484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089484 prefixEnd_2089484 := by exact prefixLift 2089484
  have htrace : WordTrace (prefixWord ++ tailWord_2089484) baseStart_2089484 baseEnd_2089484 := by
    simpa [prefixWord, tailWord_2089484, baseEnd_2089484] using wordTrace_append hprefix tailTrace_2089484
  have hstable : (prefixWord ++ tailWord_2089484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089484).length < 2 ^ (prefixWord ++ tailWord_2089484).sum := by decide
  have hdescent : baseEnd_2089484 < baseStart_2089484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089518 : List Nat := [4, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2089518 : Nat := 118140960795 + 2089518 * 2 ^ 59
def prefixEnd_2089518 : Nat := 4983230072969 + 3 ^ 40 * 2089518 * 2
def baseEnd_2089518 : Nat := 158952158551327553320813

theorem tailTrace_2089518 : CollatzResearch.WordTrace tailWord_2089518 prefixEnd_2089518 158952158551327553320813 := by
  unfold tailWord_2089518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526372805505077763541651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50807321629360414738888805 9526372805505077763541651)
  ·
    refine ⟨14289559208257616645312477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526372805505077763541651 14289559208257616645312477)
    ·
      refine ⟨5358584703096606241992179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14289559208257616645312477 5358584703096606241992179)
      ·
        refine ⟨8037877054644909362988269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358584703096606241992179 8037877054644909362988269)
        ·
          refine ⟨3014203895491841011120601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8037877054644909362988269 3014203895491841011120601)
          ·
            refine ⟨2260652921618880758340451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014203895491841011120601 2260652921618880758340451)
            ·
              refine ⟨3390979382428321137510677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260652921618880758340451 3390979382428321137510677)
              ·
                refine ⟨158952158551327553320813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3390979382428321137510677 158952158551327553320813)
                ·
                  rfl

theorem cell21_2089518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2089518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089518 prefixEnd_2089518 := by exact prefixLift 2089518
  have htrace : WordTrace (prefixWord ++ tailWord_2089518) baseStart_2089518 baseEnd_2089518 := by
    simpa [prefixWord, tailWord_2089518, baseEnd_2089518] using wordTrace_append hprefix tailTrace_2089518
  have hstable : (prefixWord ++ tailWord_2089518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089518).length < 2 ^ (prefixWord ++ tailWord_2089518).sum := by decide
  have hdescent : baseEnd_2089518 < baseStart_2089518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089549 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2089549 : Nat := 118140960795 + 2089549 * 2 ^ 59
def prefixEnd_2089549 : Nat := 4983230072969 + 3 ^ 40 * 2089549 * 2
def baseEnd_2089549 : Nat := 476863550276333494945709

theorem tailTrace_2089549 : CollatzResearch.WordTrace tailWord_2089549 prefixEnd_2089549 476863550276333494945709 := by
  unfold tailWord_2089549
  simp only [CollatzResearch.WordTrace]
  refine ⟨76212113106928314402711701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50808075404618876268474467 76212113106928314402711701)
  ·
    refine ⟨3572442801887264737627111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76212113106928314402711701 3572442801887264737627111)
    ·
      refine ⟨5358664202830897106440667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572442801887264737627111 5358664202830897106440667)
      ·
        refine ⟨8037996304246345659661001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358664202830897106440667 8037996304246345659661001)
        ·
          refine ⟨6028497228184759244745751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037996304246345659661001 6028497228184759244745751)
          ·
            refine ⟨9042745842277138867118627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028497228184759244745751 9042745842277138867118627)
            ·
              refine ⟨13564118763415708300677941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042745842277138867118627 13564118763415708300677941)
              ·
                refine ⟨1271636134070222653188557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13564118763415708300677941 1271636134070222653188557)
                ·
                  refine ⟨476863550276333494945709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271636134070222653188557 476863550276333494945709)
                  ·
                    rfl

theorem cell21_2089549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2089549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089549 prefixEnd_2089549 := by exact prefixLift 2089549
  have htrace : WordTrace (prefixWord ++ tailWord_2089549) baseStart_2089549 baseEnd_2089549 := by
    simpa [prefixWord, tailWord_2089549, baseEnd_2089549] using wordTrace_append hprefix tailTrace_2089549
  have hstable : (prefixWord ++ tailWord_2089549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089549).length < 2 ^ (prefixWord ++ tailWord_2089549).sum := by decide
  have hdescent : baseEnd_2089549 < baseStart_2089549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089605 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2089605 : Nat := 118140960795 + 2089605 * 2 ^ 59
def prefixEnd_2089605 : Nat := 4983230072969 + 3 ^ 40 * 2089605 * 2
def baseEnd_2089605 : Nat := 476876330239289842012261

theorem tailTrace_2089605 : CollatzResearch.WordTrace tailWord_2089605 prefixEnd_2089605 476876330239289842012261 := by
  unfold tailWord_2089605
  simp only [CollatzResearch.WordTrace]
  refine ⟨76214155594725435966750269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50809437063150290644500179 76214155594725435966750269)
  ·
    refine ⟨28580308348022038487531351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76214155594725435966750269 28580308348022038487531351)
    ·
      refine ⟨42870462522033057731297027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28580308348022038487531351 42870462522033057731297027)
      ·
        refine ⟨64305693783049586596945541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42870462522033057731297027 64305693783049586596945541)
        ·
          refine ⟨12057317584321797486927289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64305693783049586596945541 12057317584321797486927289)
          ·
            refine ⟨9042988188241348115195467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12057317584321797486927289 9042988188241348115195467)
            ·
              refine ⟨13564482282362022172793201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042988188241348115195467 13564482282362022172793201)
              ·
                refine ⟨10173361711771516629594901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564482282362022172793201 10173361711771516629594901)
                ·
                  refine ⟨476876330239289842012261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10173361711771516629594901 476876330239289842012261)
                  ·
                    rfl

theorem cell21_2089605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2089605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089605 prefixEnd_2089605 := by exact prefixLift 2089605
  have htrace : WordTrace (prefixWord ++ tailWord_2089605) baseStart_2089605 baseEnd_2089605 := by
    simpa [prefixWord, tailWord_2089605, baseEnd_2089605] using wordTrace_append hprefix tailTrace_2089605
  have hstable : (prefixWord ++ tailWord_2089605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089605).length < 2 ^ (prefixWord ++ tailWord_2089605).sum := by decide
  have hdescent : baseEnd_2089605 < baseStart_2089605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089636 : List Nat := [2, 3, 1, 2, 2, 1, 4, 6]
def baseStart_2089636 : Nat := 118140960795 + 2089636 * 2 ^ 59
def prefixEnd_2089636 : Nat := 4983230072969 + 3 ^ 40 * 2089636 * 2
def baseEnd_2089636 : Nat := 158961134953880225665177

theorem tailTrace_2089636 : CollatzResearch.WordTrace tailWord_2089636 prefixEnd_2089636 158961134953880225665177 := by
  unfold tailWord_2089636
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107643128806564130564381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50810190838408752174085841 38107643128806564130564381)
  ·
    refine ⟨14290366173302461548961643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38107643128806564130564381 14290366173302461548961643)
    ·
      refine ⟨21435549259953692323442465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290366173302461548961643 21435549259953692323442465)
      ·
        refine ⟨16076661944965269242581849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21435549259953692323442465 16076661944965269242581849)
        ·
          refine ⟨12057496458723951931936387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16076661944965269242581849 12057496458723951931936387)
          ·
            refine ⟨18086244688085927897904581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057496458723951931936387 18086244688085927897904581)
            ·
              refine ⟨3391170879016111480857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18086244688085927897904581 3391170879016111480857109)
              ·
                refine ⟨158961134953880225665177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3391170879016111480857109 158961134953880225665177)
                ·
                  rfl

theorem cell21_2089636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_2089636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089636 prefixEnd_2089636 := by exact prefixLift 2089636
  have htrace : WordTrace (prefixWord ++ tailWord_2089636) baseStart_2089636 baseEnd_2089636 := by
    simpa [prefixWord, tailWord_2089636, baseEnd_2089636] using wordTrace_append hprefix tailTrace_2089636
  have hstable : (prefixWord ++ tailWord_2089636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089636).length < 2 ^ (prefixWord ++ tailWord_2089636).sum := by decide
  have hdescent : baseEnd_2089636 < baseStart_2089636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089650 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2089650 : Nat := 118140960795 + 2089650 * 2 ^ 59
def prefixEnd_2089650 : Nat := 4983230072969 + 3 ^ 40 * 2089650 * 2
def baseEnd_2089650 : Nat := 476886599852379763762169

theorem tailTrace_2089650 : CollatzResearch.WordTrace tailWord_2089650 prefixEnd_2089650 476886599852379763762169 := by
  unfold tailWord_2089650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053949219890602163034601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50810531253041605768092269 19053949219890602163034601)
  ·
    refine ⟨14290461914917951622275951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19053949219890602163034601 14290461914917951622275951)
    ·
      refine ⟨21435692872376927433413927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290461914917951622275951 21435692872376927433413927)
      ·
        refine ⟨32153539308565391150120891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21435692872376927433413927 32153539308565391150120891)
        ·
          refine ⟨48230308962848086725181337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32153539308565391150120891 48230308962848086725181337)
          ·
            refine ⟨36172731722136065043886003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48230308962848086725181337 36172731722136065043886003)
            ·
              refine ⟨54259097583204097565829005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36172731722136065043886003 54259097583204097565829005)
              ·
                refine ⟨20347161593701536587185877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54259097583204097565829005 20347161593701536587185877)
                ·
                  refine ⟨476886599852379763762169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20347161593701536587185877 476886599852379763762169)
                  ·
                    rfl

theorem cell21_2089650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2089650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089650 prefixEnd_2089650 := by exact prefixLift 2089650
  have htrace : WordTrace (prefixWord ++ tailWord_2089650) baseStart_2089650 baseEnd_2089650 := by
    simpa [prefixWord, tailWord_2089650, baseEnd_2089650] using wordTrace_append hprefix tailTrace_2089650
  have hstable : (prefixWord ++ tailWord_2089650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089650).length < 2 ^ (prefixWord ++ tailWord_2089650).sum := by decide
  have hdescent : baseEnd_2089650 < baseStart_2089650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089670 : List Nat := [6, 1, 2, 1, 2, 9]
def baseStart_2089670 : Nat := 118140960795 + 2089670 * 2 ^ 59
def prefixEnd_2089670 : Nat := 4983230072969 + 3 ^ 40 * 2089670 * 2
def baseEnd_2089670 : Nat := 17662635708328302719585

theorem tailTrace_2089670 : CollatzResearch.WordTrace tailWord_2089670 prefixEnd_2089670 17662635708328302719585 := by
  unfold tailWord_2089670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381766448109061002120827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50811017559659968045244309 2381766448109061002120827)
  ·
    refine ⟨3572649672163591503181241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381766448109061002120827 3572649672163591503181241)
    ·
      refine ⟨2679487254122693627385931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3572649672163591503181241 2679487254122693627385931)
      ·
        refine ⟨4019230881184040441078897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679487254122693627385931 4019230881184040441078897)
        ·
          refine ⟨3014423160888030330809173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4019230881184040441078897 3014423160888030330809173)
          ·
            refine ⟨17662635708328302719585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3014423160888030330809173 17662635708328302719585)
            ·
              rfl

theorem cell21_2089670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 9].length) (baseStart_2089670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089670 prefixEnd_2089670 := by exact prefixLift 2089670
  have htrace : WordTrace (prefixWord ++ tailWord_2089670) baseStart_2089670 baseEnd_2089670 := by
    simpa [prefixWord, tailWord_2089670, baseEnd_2089670] using wordTrace_append hprefix tailTrace_2089670
  have hstable : (prefixWord ++ tailWord_2089670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089670).length < 2 ^ (prefixWord ++ tailWord_2089670).sum := by decide
  have hdescent : baseEnd_2089670 < baseStart_2089670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089712 : List Nat := [2, 1, 1, 1, 3, 1, 7, 5]
def baseStart_2089712 : Nat := 118140960795 + 2089712 * 2 ^ 59
def prefixEnd_2089712 : Nat := 4983230072969 + 3 ^ 40 * 2089712 * 2
def baseEnd_2089712 : Nat := 158966916365693811242903

theorem tailTrace_2089712 : CollatzResearch.WordTrace tailWord_2089712 prefixEnd_2089712 158966916365693811242903 := by
  unfold tailWord_2089712
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109029102668896620447695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50812038803558528827263593 38109029102668896620447695)
  ·
    refine ⟨57163543654003344930671543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109029102668896620447695 57163543654003344930671543)
    ·
      refine ⟨85745315481005017396007315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57163543654003344930671543 85745315481005017396007315)
      ·
        refine ⟨128617973221507526094010973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85745315481005017396007315 128617973221507526094010973)
        ·
          refine ⟨48231739958065322285254115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128617973221507526094010973 48231739958065322285254115)
          ·
            refine ⟨72347609937097983427881173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48231739958065322285254115 72347609937097983427881173)
            ·
              refine ⟨1695647107900733986590965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72347609937097983427881173 1695647107900733986590965)
              ·
                refine ⟨158966916365693811242903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1695647107900733986590965 158966916365693811242903)
                ·
                  rfl

theorem cell21_2089712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_2089712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089712 prefixEnd_2089712 := by exact prefixLift 2089712
  have htrace : WordTrace (prefixWord ++ tailWord_2089712) baseStart_2089712 baseEnd_2089712 := by
    simpa [prefixWord, tailWord_2089712, baseEnd_2089712] using wordTrace_append hprefix tailTrace_2089712
  have hstable : (prefixWord ++ tailWord_2089712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089712).length < 2 ^ (prefixWord ++ tailWord_2089712).sum := by decide
  have hdescent : baseEnd_2089712 < baseStart_2089712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089743 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 3]
def baseStart_2089743 : Nat := 118140960795 + 2089743 * 2 ^ 59
def prefixEnd_2089743 : Nat := 4983230072969 + 3 ^ 40 * 2089743 * 2
def baseEnd_2089743 : Nat := 476907823719432268711979

theorem tailTrace_2089743 : CollatzResearch.WordTrace tailWord_2089743 prefixEnd_2089743 476907823719432268711979 := by
  unfold tailWord_2089743
  simp only [CollatzResearch.WordTrace]
  refine ⟨76219188868225485535273883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50812792578816990356849255 76219188868225485535273883)
  ·
    refine ⟨114328783302338228302910825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76219188868225485535273883 114328783302338228302910825)
    ·
      refine ⟨85746587476753671227183119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114328783302338228302910825 85746587476753671227183119)
      ·
        refine ⟨128619881215130506840774679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85746587476753671227183119 128619881215130506840774679)
        ·
          refine ⟨192929821822695760261162019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128619881215130506840774679 192929821822695760261162019)
          ·
            refine ⟨289394732734043640391743029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192929821822695760261162019 289394732734043640391743029)
            ·
              refine ⟨27130756193816591286725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289394732734043640391743029 27130756193816591286725909)
              ·
                refine ⟨1271754196585152716565277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27130756193816591286725909 1271754196585152716565277)
                ·
                  refine ⟨476907823719432268711979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271754196585152716565277 476907823719432268711979)
                  ·
                    rfl

theorem cell21_2089743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].length) (baseStart_2089743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089743 prefixEnd_2089743 := by exact prefixLift 2089743
  have htrace : WordTrace (prefixWord ++ tailWord_2089743) baseStart_2089743 baseEnd_2089743 := by
    simpa [prefixWord, tailWord_2089743, baseEnd_2089743] using wordTrace_append hprefix tailTrace_2089743
  have hstable : (prefixWord ++ tailWord_2089743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089743).length < 2 ^ (prefixWord ++ tailWord_2089743).sum := by decide
  have hdescent : baseEnd_2089743 < baseStart_2089743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089774 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2089774 : Nat := 118140960795 + 2089774 * 2 ^ 59
def prefixEnd_2089774 : Nat := 4983230072969 + 3 ^ 40 * 2089774 * 2
def baseEnd_2089774 : Nat := 476914898341783103695249

theorem tailTrace_2089774 : CollatzResearch.WordTrace tailWord_2089774 prefixEnd_2089774 476914898341783103695249 := by
  unfold tailWord_2089774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527539941389147228706547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50813546354075451886434917 9527539941389147228706547)
  ·
    refine ⟨14291309912083720843059821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527539941389147228706547 14291309912083720843059821)
    ·
      refine ⟨5359241217031395316147433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14291309912083720843059821 5359241217031395316147433)
      ·
        refine ⟨4019430912773546487110575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5359241217031395316147433 4019430912773546487110575)
        ·
          refine ⟨6029146369160319730665863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019430912773546487110575 6029146369160319730665863)
          ·
            refine ⟨9043719553740479595998795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029146369160319730665863 9043719553740479595998795)
            ·
              refine ⟨13565579330610719393998193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9043719553740479595998795 13565579330610719393998193)
              ·
                refine ⟨10174184497958039545498645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13565579330610719393998193 10174184497958039545498645)
                ·
                  refine ⟨476914898341783103695249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10174184497958039545498645 476914898341783103695249)
                  ·
                    rfl

theorem cell21_2089774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2089774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089774 prefixEnd_2089774 := by exact prefixLift 2089774
  have htrace : WordTrace (prefixWord ++ tailWord_2089774) baseStart_2089774 baseEnd_2089774 := by
    simpa [prefixWord, tailWord_2089774, baseEnd_2089774] using wordTrace_append hprefix tailTrace_2089774
  have hstable : (prefixWord ++ tailWord_2089774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089774).length < 2 ^ (prefixWord ++ tailWord_2089774).sum := by decide
  have hdescent : baseEnd_2089774 < baseStart_2089774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089802 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_2089802 : Nat := 118140960795 + 2089802 * 2 ^ 59
def prefixEnd_2089802 : Nat := 4983230072969 + 3 ^ 40 * 2089802 * 2
def baseEnd_2089802 : Nat := 476921288323261277228525

theorem tailTrace_2089802 : CollatzResearch.WordTrace tailWord_2089802 prefixEnd_2089802 476921288323261277228525 := by
  unfold tailWord_2089802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055335193752934652917915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50814227183341159074447773 19055335193752934652917915)
  ·
    refine ⟨28583002790629401979376873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19055335193752934652917915 28583002790629401979376873)
    ·
      refine ⟨21437252092972051484532655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28583002790629401979376873 21437252092972051484532655)
      ·
        refine ⟨32155878139458077226798983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21437252092972051484532655 32155878139458077226798983)
        ·
          refine ⟨48233817209187115840198475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32155878139458077226798983 48233817209187115840198475)
          ·
            refine ⟨72350725813780673760297713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48233817209187115840198475 72350725813780673760297713)
            ·
              refine ⟨54263044360335505320223285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72350725813780673760297713 54263044360335505320223285)
              ·
                refine ⟨5087160408781453623770933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54263044360335505320223285 5087160408781453623770933)
                ·
                  refine ⟨476921288323261277228525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5087160408781453623770933 476921288323261277228525)
                  ·
                    rfl

theorem cell21_2089802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_2089802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089802 prefixEnd_2089802 := by exact prefixLift 2089802
  have htrace : WordTrace (prefixWord ++ tailWord_2089802) baseStart_2089802 baseEnd_2089802 := by
    simpa [prefixWord, tailWord_2089802, baseEnd_2089802] using wordTrace_append hprefix tailTrace_2089802
  have hstable : (prefixWord ++ tailWord_2089802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089802).length < 2 ^ (prefixWord ++ tailWord_2089802).sum := by decide
  have hdescent : baseEnd_2089802 < baseStart_2089802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089864 : List Nat := [2, 1, 3, 3, 2, 1, 3, 6]
def baseStart_2089864 : Nat := 118140960795 + 2089864 * 2 ^ 59
def prefixEnd_2089864 : Nat := 4983230072969 + 3 ^ 40 * 2089864 * 2
def baseEnd_2089864 : Nat := 158978479189320982398355

theorem tailTrace_2089864 : CollatzResearch.WordTrace tailWord_2089864 prefixEnd_2089864 158978479189320982398355 := by
  unfold tailWord_2089864
  simp only [CollatzResearch.WordTrace]
  refine ⟨38111801050393561600214323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50815734733858082133619097 38111801050393561600214323)
  ·
    refine ⟨57167701575590342400321485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38111801050393561600214323 57167701575590342400321485)
    ·
      refine ⟨21437888090846378400120557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57167701575590342400321485 21437888090846378400120557)
      ·
        refine ⟨8039208034067391900045209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21437888090846378400120557 8039208034067391900045209)
        ·
          refine ⟨6029406025550543925033907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8039208034067391900045209 6029406025550543925033907)
          ·
            refine ⟨9044109038325815887550861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029406025550543925033907 9044109038325815887550861)
            ·
              refine ⟨3391540889372180957831573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9044109038325815887550861 3391540889372180957831573)
              ·
                refine ⟨158978479189320982398355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3391540889372180957831573 158978479189320982398355)
                ·
                  rfl

theorem cell21_2089864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_2089864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089864 prefixEnd_2089864 := by exact prefixLift 2089864
  have htrace : WordTrace (prefixWord ++ tailWord_2089864) baseStart_2089864 baseEnd_2089864 := by
    simpa [prefixWord, tailWord_2089864, baseEnd_2089864] using wordTrace_append hprefix tailTrace_2089864
  have hstable : (prefixWord ++ tailWord_2089864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089864).length < 2 ^ (prefixWord ++ tailWord_2089864).sum := by decide
  have hdescent : baseEnd_2089864 < baseStart_2089864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089901 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 4]
def baseStart_2089901 : Nat := 118140960795 + 2089901 * 2 ^ 59
def prefixEnd_2089901 : Nat := 4983230072969 + 3 ^ 40 * 2089901 * 2
def baseEnd_2089901 : Nat := 476943881472059105078323

theorem tailTrace_2089901 : CollatzResearch.WordTrace tailWord_2089901 prefixEnd_2089901 476943881472059105078323 := by
  unfold tailWord_2089901
  simp only [CollatzResearch.WordTrace]
  refine ⟨76224951601653078519525557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50816634401102052346350371 76224951601653078519525557)
  ·
    refine ⟨7146089212654976111205521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76224951601653078519525557 7146089212654976111205521)
    ·
      refine ⟨5359566909491232083404141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7146089212654976111205521 5359566909491232083404141)
      ·
        refine ⟨2009837591059212031276553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5359566909491232083404141 2009837591059212031276553)
        ·
          refine ⟨1507378193294409023457415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009837591059212031276553 1507378193294409023457415)
          ·
            refine ⟨2261067289941613535186123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507378193294409023457415 2261067289941613535186123)
            ·
              refine ⟨3391600934912420302779185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261067289941613535186123 3391600934912420302779185)
              ·
                refine ⟨2543700701184315227084389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3391600934912420302779185 2543700701184315227084389)
                ·
                  refine ⟨476943881472059105078323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543700701184315227084389 476943881472059105078323)
                  ·
                    rfl

theorem cell21_2089901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_2089901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089901 prefixEnd_2089901 := by exact prefixLift 2089901
  have htrace : WordTrace (prefixWord ++ tailWord_2089901) baseStart_2089901 baseEnd_2089901 := by
    simpa [prefixWord, tailWord_2089901, baseEnd_2089901] using wordTrace_append hprefix tailTrace_2089901
  have hstable : (prefixWord ++ tailWord_2089901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089901).length < 2 ^ (prefixWord ++ tailWord_2089901).sum := by decide
  have hdescent : baseEnd_2089901 < baseStart_2089901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089909 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2089909 : Nat := 118140960795 + 2089909 * 2 ^ 59
def prefixEnd_2089909 : Nat := 4983230072969 + 3 ^ 40 * 2089909 * 2
def baseEnd_2089909 : Nat := 476945707181052868944973

theorem tailTrace_2089909 : CollatzResearch.WordTrace tailWord_2089909 prefixEnd_2089909 476945707181052868944973 := by
  unfold tailWord_2089909
  simp only [CollatzResearch.WordTrace]
  refine ⟨76225243385624095885816781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50816828923749397257211187 76225243385624095885816781)
  ·
    refine ⟨28584466269609035957181293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76225243385624095885816781 28584466269609035957181293)
    ·
      refine ⟨10719174851103388483942985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28584466269609035957181293 10719174851103388483942985)
      ·
        refine ⟨8039381138327541362957239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10719174851103388483942985 8039381138327541362957239)
        ·
          refine ⟨12059071707491312044435859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039381138327541362957239 12059071707491312044435859)
          ·
            refine ⟨18088607561236968066653789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059071707491312044435859 18088607561236968066653789)
            ·
              refine ⟨6783227835463863024995171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18088607561236968066653789 6783227835463863024995171)
              ·
                refine ⟨10174841753195794537492757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6783227835463863024995171 10174841753195794537492757)
                ·
                  refine ⟨476945707181052868944973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10174841753195794537492757 476945707181052868944973)
                  ·
                    rfl

theorem cell21_2089909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2089909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089909 prefixEnd_2089909 := by exact prefixLift 2089909
  have htrace : WordTrace (prefixWord ++ tailWord_2089909) baseStart_2089909 baseEnd_2089909 := by
    simpa [prefixWord, tailWord_2089909, baseEnd_2089909] using wordTrace_append hprefix tailTrace_2089909
  have hstable : (prefixWord ++ tailWord_2089909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089909).length < 2 ^ (prefixWord ++ tailWord_2089909).sum := by decide
  have hdescent : baseEnd_2089909 < baseStart_2089909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089940 : List Nat := [2, 4, 1, 2, 1, 3, 1, 7]
def baseStart_2089940 : Nat := 118140960795 + 2089940 * 2 ^ 59
def prefixEnd_2089940 : Nat := 4983230072969 + 3 ^ 40 * 2089940 * 2
def baseEnd_2089940 : Nat := 158984260601134567976081

theorem tailTrace_2089940 : CollatzResearch.WordTrace tailWord_2089940 prefixEnd_2089940 158984260601134567976081 := by
  unfold tailWord_2089940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113187024255894090097637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50817582699007858786796849 38113187024255894090097637)
  ·
    refine ⟨7146222567047980141893307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38113187024255894090097637 7146222567047980141893307)
    ·
      refine ⟨10719333850571970212839961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146222567047980141893307 10719333850571970212839961)
      ·
        refine ⟨8039500387928977659629971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10719333850571970212839961 8039500387928977659629971)
        ·
          refine ⟨12059250581893466489444957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039500387928977659629971 12059250581893466489444957)
          ·
            refine ⟨4522218968210049933541859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12059250581893466489444957 4522218968210049933541859)
            ·
              refine ⟨6783328452315074900312789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522218968210049933541859 6783328452315074900312789)
              ·
                refine ⟨158984260601134567976081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6783328452315074900312789 158984260601134567976081)
                ·
                  rfl

theorem cell21_2089940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_2089940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089940 prefixEnd_2089940 := by exact prefixLift 2089940
  have htrace : WordTrace (prefixWord ++ tailWord_2089940) baseStart_2089940 baseEnd_2089940 := by
    simpa [prefixWord, tailWord_2089940, baseEnd_2089940] using wordTrace_append hprefix tailTrace_2089940
  have hstable : (prefixWord ++ tailWord_2089940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089940).length < 2 ^ (prefixWord ++ tailWord_2089940).sum := by decide
  have hdescent : baseEnd_2089940 < baseStart_2089940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2089957 : List Nat := [1, 3, 1, 6, 1, 2, 7]
def baseStart_2089957 : Nat := 118140960795 + 2089957 * 2 ^ 59
def prefixEnd_2089957 : Nat := 4983230072969 + 3 ^ 40 * 2089957 * 2
def baseEnd_2089957 : Nat := 52995184603890605793875

theorem tailTrace_2089957 : CollatzResearch.WordTrace tailWord_2089957 prefixEnd_2089957 52995184603890605793875 := by
  unfold tailWord_2089957
  simp only [CollatzResearch.WordTrace]
  refine ⟨76226994089450200083564125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50817996059633466722376083 76226994089450200083564125)
  ·
    refine ⟨28585122783543825031336547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76226994089450200083564125 28585122783543825031336547)
    ·
      refine ⟨42877684175315737547004821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28585122783543825031336547 42877684175315737547004821)
      ·
        refine ⟨2009891445717925197515851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42877684175315737547004821 2009891445717925197515851)
        ·
          refine ⟨3014837168576887796273777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009891445717925197515851 3014837168576887796273777)
          ·
            refine ⟨2261127876432665847205333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014837168576887796273777 2261127876432665847205333)
            ·
              refine ⟨52995184603890605793875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2261127876432665847205333 52995184603890605793875)
              ·
                rfl

theorem cell21_2089957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 7].length) (baseStart_2089957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2089957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2089957 prefixEnd_2089957 := by exact prefixLift 2089957
  have htrace : WordTrace (prefixWord ++ tailWord_2089957) baseStart_2089957 baseEnd_2089957 := by
    simpa [prefixWord, tailWord_2089957, baseEnd_2089957] using wordTrace_append hprefix tailTrace_2089957
  have hstable : (prefixWord ++ tailWord_2089957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2089957).length < 2 ^ (prefixWord ++ tailWord_2089957).sum := by decide
  have hdescent : baseEnd_2089957 < baseStart_2089957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2089957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090016 : List Nat := [2, 1, 1, 7, 1, 9]
def baseStart_2090016 : Nat := 118140960795 + 2090016 * 2 ^ 59
def prefixEnd_2090016 : Nat := 4983230072969 + 3 ^ 40 * 2090016 * 2
def baseEnd_2090016 : Nat := 17665560223660905950423

theorem tailTrace_2090016 : CollatzResearch.WordTrace tailWord_2090016 prefixEnd_2090016 17665560223660905950423 := by
  unfold tailWord_2090016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38114572998118226579980951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50819430664157635439974601 38114572998118226579980951)
  ·
    refine ⟨57171859497177339869971427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38114572998118226579980951 57171859497177339869971427)
    ·
      refine ⟨85757789245766009804957141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57171859497177339869971427 85757789245766009804957141)
      ·
        refine ⟨2009948185447640854803683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 85757789245766009804957141 2009948185447640854803683)
        ·
          refine ⟨3014922278171461282205525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009948185447640854803683 3014922278171461282205525)
          ·
            refine ⟨17665560223660905950423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3014922278171461282205525 17665560223660905950423)
            ·
              rfl

theorem cell21_2090016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 9].length) (baseStart_2090016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090016 prefixEnd_2090016 := by exact prefixLift 2090016
  have htrace : WordTrace (prefixWord ++ tailWord_2090016) baseStart_2090016 baseEnd_2090016 := by
    simpa [prefixWord, tailWord_2090016, baseEnd_2090016] using wordTrace_append hprefix tailTrace_2090016
  have hstable : (prefixWord ++ tailWord_2090016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090016).length < 2 ^ (prefixWord ++ tailWord_2090016).sum := by decide
  have hdescent : baseEnd_2090016 < baseStart_2090016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090303 : List Nat := [1, 1, 2, 2, 4, 4, 7]
def baseStart_2090303 : Nat := 118140960795 + 2090303 * 2 ^ 59
def prefixEnd_2090303 : Nat := 4983230072969 + 3 ^ 40 * 2090303 * 2
def baseEnd_2090303 : Nat := 53003958149888415486389

theorem tailTrace_2090303 : CollatzResearch.WordTrace tailWord_2090303 prefixEnd_2090303 53003958149888415486389 := by
  unfold tailWord_2090303
  simp only [CollatzResearch.WordTrace]
  refine ⟨76239613746196701175659563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50826409164131134117106375 76239613746196701175659563)
  ·
    refine ⟨114359420619295051763489345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76239613746196701175659563 114359420619295051763489345)
    ·
      refine ⟨85769565464471288822617009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114359420619295051763489345 85769565464471288822617009)
      ·
        refine ⟨64327174098353466616962757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85769565464471288822617009 64327174098353466616962757)
        ·
          refine ⟨12061345143441274990680517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64327174098353466616962757 12061345143441274990680517)
          ·
            refine ⟨2261502214395239060752597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12061345143441274990680517 2261502214395239060752597)
            ·
              refine ⟨53003958149888415486389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2261502214395239060752597 53003958149888415486389)
              ·
                rfl

theorem cell21_2090303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 7].length) (baseStart_2090303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090303 prefixEnd_2090303 := by exact prefixLift 2090303
  have htrace : WordTrace (prefixWord ++ tailWord_2090303) baseStart_2090303 baseEnd_2090303 := by
    simpa [prefixWord, tailWord_2090303, baseEnd_2090303] using wordTrace_append hprefix tailTrace_2090303
  have hstable : (prefixWord ++ tailWord_2090303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090303).length < 2 ^ (prefixWord ++ tailWord_2090303).sum := by decide
  have hdescent : baseEnd_2090303 < baseStart_2090303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090365 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2090365 : Nat := 118140960795 + 2090365 * 2 ^ 59
def prefixEnd_2090365 : Nat := 4983230072969 + 3 ^ 40 * 2090365 * 2
def baseEnd_2090365 : Nat := 477049772593697409344041

theorem tailTrace_2090365 : CollatzResearch.WordTrace tailWord_2090365 prefixEnd_2090365 477049772593697409344041 := by
  unfold tailWord_2090365
  simp only [CollatzResearch.WordTrace]
  refine ⟨76241875071972085764416549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50827916714648057176277699 76241875071972085764416549)
  ·
    refine ⟨14295351575994766080828103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76241875071972085764416549 14295351575994766080828103)
    ·
      refine ⟨21443027363992149121242155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295351575994766080828103 21443027363992149121242155)
      ·
        refine ⟨32164541045988223681863233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21443027363992149121242155 32164541045988223681863233)
        ·
          refine ⟨24123405784491167761397425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32164541045988223681863233 24123405784491167761397425)
          ·
            refine ⟨18092554338368375821048069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24123405784491167761397425 18092554338368375821048069)
            ·
              refine ⟨3392353938444070466446513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18092554338368375821048069 3392353938444070466446513)
              ·
                refine ⟨2544265453833052849834885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392353938444070466446513 2544265453833052849834885)
                ·
                  refine ⟨477049772593697409344041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544265453833052849834885 477049772593697409344041)
                  ·
                    rfl

theorem cell21_2090365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2090365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090365 prefixEnd_2090365 := by exact prefixLift 2090365
  have htrace : WordTrace (prefixWord ++ tailWord_2090365) baseStart_2090365 baseEnd_2090365 := by
    simpa [prefixWord, tailWord_2090365, baseEnd_2090365] using wordTrace_append hprefix tailTrace_2090365
  have hstable : (prefixWord ++ tailWord_2090365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090365).length < 2 ^ (prefixWord ++ tailWord_2090365).sum := by decide
  have hdescent : baseEnd_2090365 < baseStart_2090365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090393 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_2090393 : Nat := 118140960795 + 2090393 * 2 ^ 59
def prefixEnd_2090393 : Nat := 4983230072969 + 3 ^ 40 * 2090393 * 2
def baseEnd_2090393 : Nat := 477056162575175582877317

theorem tailTrace_2090393 : CollatzResearch.WordTrace tailWord_2090393 prefixEnd_2090393 477056162575175582877317 := by
  unfold tailWord_2090393
  simp only [CollatzResearch.WordTrace]
  refine ⟨76242896315870646546435833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50828597543913764364290555 76242896315870646546435833)
  ·
    refine ⟨57182172236902984909826875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76242896315870646546435833 57182172236902984909826875)
    ·
      refine ⟨85773258355354477364740313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57182172236902984909826875 85773258355354477364740313)
      ·
        refine ⟨64329943766515858023555235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85773258355354477364740313 64329943766515858023555235)
        ·
          refine ⟨96494915649773787035332853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64329943766515858023555235 96494915649773787035332853)
          ·
            refine ⟨9046398342166292534562455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96494915649773787035332853 9046398342166292534562455)
            ·
              refine ⟨13569597513249438801843683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046398342166292534562455 13569597513249438801843683)
              ·
                refine ⟨20354396269874158202765525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569597513249438801843683 20354396269874158202765525)
                ·
                  refine ⟨477056162575175582877317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20354396269874158202765525 477056162575175582877317)
                  ·
                    rfl

theorem cell21_2090393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_2090393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090393 prefixEnd_2090393 := by exact prefixLift 2090393
  have htrace : WordTrace (prefixWord ++ tailWord_2090393) baseStart_2090393 baseEnd_2090393 := by
    simpa [prefixWord, tailWord_2090393, baseEnd_2090393] using wordTrace_append hprefix tailTrace_2090393
  have hstable : (prefixWord ++ tailWord_2090393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090393).length < 2 ^ (prefixWord ++ tailWord_2090393).sum := by decide
  have hdescent : baseEnd_2090393 < baseStart_2090393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090531 : List Nat := [1, 1, 1, 4, 6, 8]
def baseStart_2090531 : Nat := 118140960795 + 2090531 * 2 ^ 59
def prefixEnd_2090531 : Nat := 4983230072969 + 3 ^ 40 * 2090531 * 2
def baseEnd_2090531 : Nat := 17669913187234000354705

theorem tailTrace_2090531 : CollatzResearch.WordTrace tailWord_2090531 prefixEnd_2090531 17669913187234000354705 := by
  unfold tailWord_2090531
  simp only [CollatzResearch.WordTrace]
  refine ⟨76247929589370696114959447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50831953059580464076639631 76247929589370696114959447)
  ·
    refine ⟨114371894384056044172439171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76247929589370696114959447 114371894384056044172439171)
    ·
      refine ⟨171557841576084066258658757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114371894384056044172439171 171557841576084066258658757)
      ·
        refine ⟨32167095295515762423498517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171557841576084066258658757 32167095295515762423498517)
        ·
          refine ⟨1507832591977301363601493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32167095295515762423498517 1507832591977301363601493)
          ·
            refine ⟨17669913187234000354705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1507832591977301363601493 17669913187234000354705)
            ·
              rfl

theorem cell21_2090531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 8].length) (baseStart_2090531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090531 prefixEnd_2090531 := by exact prefixLift 2090531
  have htrace : WordTrace (prefixWord ++ tailWord_2090531) baseStart_2090531 baseEnd_2090531 := by
    simpa [prefixWord, tailWord_2090531, baseEnd_2090531] using wordTrace_append hprefix tailTrace_2090531
  have hstable : (prefixWord ++ tailWord_2090531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090531).length < 2 ^ (prefixWord ++ tailWord_2090531).sum := by decide
  have hdescent : baseEnd_2090531 < baseStart_2090531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090545 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_2090545 : Nat := 118140960795 + 2090545 * 2 ^ 59
def prefixEnd_2090545 : Nat := 4983230072969 + 3 ^ 40 * 2090545 * 2
def baseEnd_2090545 : Nat := 477090851046057096343673

theorem tailTrace_2090545 : CollatzResearch.WordTrace tailWord_2090545 prefixEnd_2090545 477090851046057096343673 := by
  unfold tailWord_2090545
  simp only [CollatzResearch.WordTrace]
  refine ⟨76248440211319976505969089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50832293474213317670646059 76248440211319976505969089)
  ·
    refine ⟨57186330158489982379476817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76248440211319976505969089 57186330158489982379476817)
    ·
      refine ⟨42889747618867486784607613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57186330158489982379476817 42889747618867486784607613)
      ·
        refine ⟨16083655357075307544227855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42889747618867486784607613 16083655357075307544227855)
        ·
          refine ⟨24125483035612961316341783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16083655357075307544227855 24125483035612961316341783)
          ·
            refine ⟨36188224553419441974512675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24125483035612961316341783 36188224553419441974512675)
            ·
              refine ⟨54282336830129162961769013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36188224553419441974512675 54282336830129162961769013)
              ·
                refine ⟨5088969077824609027665845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54282336830129162961769013 5088969077824609027665845)
                ·
                  refine ⟨477090851046057096343673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5088969077824609027665845 477090851046057096343673)
                  ·
                    rfl

theorem cell21_2090545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_2090545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090545 prefixEnd_2090545 := by exact prefixLift 2090545
  have htrace : WordTrace (prefixWord ++ tailWord_2090545) baseStart_2090545 baseEnd_2090545 := by
    simpa [prefixWord, tailWord_2090545, baseEnd_2090545] using wordTrace_append hprefix tailTrace_2090545
  have hstable : (prefixWord ++ tailWord_2090545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090545).length < 2 ^ (prefixWord ++ tailWord_2090545).sum := by decide
  have hdescent : baseEnd_2090545 < baseStart_2090545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090610 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2090610 : Nat := 118140960795 + 2090610 * 2 ^ 59
def prefixEnd_2090610 : Nat := 4983230072969 + 3 ^ 40 * 2090610 * 2
def baseEnd_2090610 : Nat := 477105684931631427760207

theorem tailTrace_2090610 : CollatzResearch.WordTrace tailWord_2090610 prefixEnd_2090610 477105684931631427760207 := by
  unfold tailWord_2090610
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062702739021123151771321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50833873970722995071390189 19062702739021123151771321)
  ·
    refine ⟨14297027054265842363828491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19062702739021123151771321 14297027054265842363828491)
    ·
      refine ⟨21445540581398763545742737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14297027054265842363828491 21445540581398763545742737)
      ·
        refine ⟨16084155436049072659307053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21445540581398763545742737 16084155436049072659307053)
        ·
          refine ⟨6031558288518402247240145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16084155436049072659307053 6031558288518402247240145)
          ·
            refine ⟨4523668716388801685430109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031558288518402247240145 4523668716388801685430109)
            ·
              refine ⟨1696375768645800632036291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4523668716388801685430109 1696375768645800632036291)
              ·
                refine ⟨2544563652968700948054437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696375768645800632036291 2544563652968700948054437)
                ·
                  refine ⟨477105684931631427760207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544563652968700948054437 477105684931631427760207)
                  ·
                    rfl

theorem cell21_2090610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2090610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090610 prefixEnd_2090610 := by exact prefixLift 2090610
  have htrace : WordTrace (prefixWord ++ tailWord_2090610) baseStart_2090610 baseEnd_2090610 := by
    simpa [prefixWord, tailWord_2090610, baseEnd_2090610] using wordTrace_append hprefix tailTrace_2090610
  have hstable : (prefixWord ++ tailWord_2090610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090610).length < 2 ^ (prefixWord ++ tailWord_2090610).sum := by decide
  have hdescent : baseEnd_2090610 < baseStart_2090610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090635 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_2090635 : Nat := 118140960795 + 2090635 * 2 ^ 59
def prefixEnd_2090635 : Nat := 4983230072969 + 3 ^ 40 * 2090635 * 2
def baseEnd_2090635 : Nat := 477111390272236939843489

theorem tailTrace_2090635 : CollatzResearch.WordTrace tailWord_2090635 prefixEnd_2090635 477111390272236939843489 := by
  unfold tailWord_2090635
  simp only [CollatzResearch.WordTrace]
  refine ⟨76251722780993921876745359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50834481853995947917830239 76251722780993921876745359)
  ·
    refine ⟨114377584171490882815118039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76251722780993921876745359 114377584171490882815118039)
    ·
      refine ⟨171566376257236324222677059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114377584171490882815118039 171566376257236324222677059)
      ·
        refine ⟨257349564385854486334015589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171566376257236324222677059 257349564385854486334015589)
        ·
          refine ⟨48253043322347716187627923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257349564385854486334015589 48253043322347716187627923)
          ·
            refine ⟨72379564983521574281441885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48253043322347716187627923 72379564983521574281441885)
            ·
              refine ⟨27142336868820590355540707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72379564983521574281441885 27142336868820590355540707)
              ·
                refine ⟨40713505303230885533311061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27142336868820590355540707 40713505303230885533311061)
                ·
                  refine ⟨477111390272236939843489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40713505303230885533311061 477111390272236939843489)
                  ·
                    rfl

theorem cell21_2090635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_2090635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090635 prefixEnd_2090635 := by exact prefixLift 2090635
  have htrace : WordTrace (prefixWord ++ tailWord_2090635) baseStart_2090635 baseEnd_2090635 := by
    simpa [prefixWord, tailWord_2090635, baseEnd_2090635] using wordTrace_append hprefix tailTrace_2090635
  have hstable : (prefixWord ++ tailWord_2090635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090635).length < 2 ^ (prefixWord ++ tailWord_2090635).sum := by decide
  have hdescent : baseEnd_2090635 < baseStart_2090635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090669 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2090669 : Nat := 118140960795 + 2090669 * 2 ^ 59
def prefixEnd_2090669 : Nat := 4983230072969 + 3 ^ 40 * 2090669 * 2
def baseEnd_2090669 : Nat := 477119149535460436276753

theorem tailTrace_2090669 : CollatzResearch.WordTrace tailWord_2090669 prefixEnd_2090669 477119149535460436276753 := by
  unfold tailWord_2090669
  simp only [CollatzResearch.WordTrace]
  refine ⟨76252962862870745683483061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50835308575247163788988707 76252962862870745683483061)
  ·
    refine ⟨7148715268394132407826537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76252962862870745683483061 7148715268394132407826537)
    ·
      refine ⟨5361536451295599305869903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7148715268394132407826537 5361536451295599305869903)
      ·
        refine ⟨8042304676943398958804855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361536451295599305869903 8042304676943398958804855)
        ·
          refine ⟨12063457015415098438207283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042304676943398958804855 12063457015415098438207283)
          ·
            refine ⟨18095185523122647657310925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063457015415098438207283 18095185523122647657310925)
            ·
              refine ⟨6785694571170992871491597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18095185523122647657310925 6785694571170992871491597)
              ·
                refine ⟨2544635464189122326809349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6785694571170992871491597 2544635464189122326809349)
                ·
                  refine ⟨477119149535460436276753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544635464189122326809349 477119149535460436276753)
                  ·
                    rfl

theorem cell21_2090669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2090669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090669 prefixEnd_2090669 := by exact prefixLift 2090669
  have htrace : WordTrace (prefixWord ++ tailWord_2090669) baseStart_2090669 baseEnd_2090669 := by
    simpa [prefixWord, tailWord_2090669, baseEnd_2090669] using wordTrace_append hprefix tailTrace_2090669
  have hstable : (prefixWord ++ tailWord_2090669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090669).length < 2 ^ (prefixWord ++ tailWord_2090669).sum := by decide
  have hdescent : baseEnd_2090669 < baseStart_2090669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090717 : List Nat := [1, 4, 3, 3, 1, 2, 1, 6]
def baseStart_2090717 : Nat := 118140960795 + 2090717 * 2 ^ 59
def prefixEnd_2090717 : Nat := 4983230072969 + 3 ^ 40 * 2090717 * 2
def baseEnd_2090717 : Nat := 159043367929807673158885

theorem tailTrace_2090717 : CollatzResearch.WordTrace tailWord_2090717 prefixEnd_2090717 159043367929807673158885 := by
  unfold tailWord_2090717
  simp only [CollatzResearch.WordTrace]
  refine ⟨76254713566696849881230405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50836475711131233254153603 76254713566696849881230405)
  ·
    refine ⟨14297758793755659352730701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76254713566696849881230405 14297758793755659352730701)
    ·
      refine ⟨5361659547658372257274013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14297758793755659352730701 5361659547658372257274013)
      ·
        refine ⟨2010622330371889596477755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5361659547658372257274013 2010622330371889596477755)
        ·
          refine ⟨3015933495557834394716633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010622330371889596477755 3015933495557834394716633)
          ·
            refine ⟨2261950121668375796037475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3015933495557834394716633 2261950121668375796037475)
            ·
              refine ⟨3392925182502563694056213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261950121668375796037475 3392925182502563694056213)
              ·
                refine ⟨159043367929807673158885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3392925182502563694056213 159043367929807673158885)
                ·
                  rfl

theorem cell21_2090717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_2090717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090717 prefixEnd_2090717 := by exact prefixLift 2090717
  have htrace : WordTrace (prefixWord ++ tailWord_2090717) baseStart_2090717 baseEnd_2090717 := by
    simpa [prefixWord, tailWord_2090717, baseEnd_2090717] using wordTrace_append hprefix tailTrace_2090717
  have hstable : (prefixWord ++ tailWord_2090717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090717).length < 2 ^ (prefixWord ++ tailWord_2090717).sum := by decide
  have hdescent : baseEnd_2090717 < baseStart_2090717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090759 : List Nat := [1, 1, 4, 4, 2, 1, 8]
def baseStart_2090759 : Nat := 118140960795 + 2090759 * 2 ^ 59
def prefixEnd_2090759 : Nat := 4983230072969 + 3 ^ 40 * 2090759 * 2
def baseEnd_2090759 : Nat := 53015520973515586641841

theorem tailTrace_2090759 : CollatzResearch.WordTrace tailWord_2090759 prefixEnd_2090759 53015520973515586641841 := by
  unfold tailWord_2090759
  simp only [CollatzResearch.WordTrace]
  refine ⟨76256245432544691054259331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50837496955029794036172887 76256245432544691054259331)
  ·
    refine ⟨114384368148817036581388997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76256245432544691054259331 114384368148817036581388997)
    ·
      refine ⟨21447069027903194359010437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114384368148817036581388997 21447069027903194359010437)
      ·
        refine ⟨4021325442731848942314457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21447069027903194359010437 4021325442731848942314457)
        ·
          refine ⟨3015994082048886706735843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4021325442731848942314457 3015994082048886706735843)
          ·
            refine ⟨4523991123073330060103765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015994082048886706735843 4523991123073330060103765)
            ·
              refine ⟨53015520973515586641841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4523991123073330060103765 53015520973515586641841)
              ·
                rfl

theorem cell21_2090759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_2090759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090759 prefixEnd_2090759 := by exact prefixLift 2090759
  have htrace : WordTrace (prefixWord ++ tailWord_2090759) baseStart_2090759 baseEnd_2090759 := by
    simpa [prefixWord, tailWord_2090759, baseEnd_2090759] using wordTrace_append hprefix tailTrace_2090759
  have hstable : (prefixWord ++ tailWord_2090759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090759).length < 2 ^ (prefixWord ++ tailWord_2090759).sum := by decide
  have hdescent : baseEnd_2090759 < baseStart_2090759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090773 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2090773 : Nat := 118140960795 + 2090773 * 2 ^ 59
def prefixEnd_2090773 : Nat := 4983230072969 + 3 ^ 40 * 2090773 * 2
def baseEnd_2090773 : Nat := 477142883752379366543207

theorem tailTrace_2090773 : CollatzResearch.WordTrace tailWord_2090773 prefixEnd_2090773 477142883752379366543207 := by
  unfold tailWord_2090773
  simp only [CollatzResearch.WordTrace]
  refine ⟨76256756054493971445268973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50837837369662647630179315 76256756054493971445268973)
  ·
    refine ⟨28596283520435239291975865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76256756054493971445268973 28596283520435239291975865)
    ·
      refine ⟨21447212640326429468981899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28596283520435239291975865 21447212640326429468981899)
      ·
        refine ⟨32170818960489644203472849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21447212640326429468981899 32170818960489644203472849)
        ·
          refine ⟨24128114220367233152604637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32170818960489644203472849 24128114220367233152604637)
          ·
            refine ⟨9048042832637712432226739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24128114220367233152604637 9048042832637712432226739)
            ·
              refine ⟨13572064248956568648340109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048042832637712432226739 13572064248956568648340109)
              ·
                refine ⟨5089524093358713243127541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13572064248956568648340109 5089524093358713243127541)
                ·
                  refine ⟨477142883752379366543207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5089524093358713243127541 477142883752379366543207)
                  ·
                    rfl

theorem cell21_2090773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2090773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090773 prefixEnd_2090773 := by exact prefixLift 2090773
  have htrace : WordTrace (prefixWord ++ tailWord_2090773) baseStart_2090773 baseEnd_2090773 := by
    simpa [prefixWord, tailWord_2090773, baseEnd_2090773] using wordTrace_append hprefix tailTrace_2090773
  have hstable : (prefixWord ++ tailWord_2090773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090773).length < 2 ^ (prefixWord ++ tailWord_2090773).sum := by decide
  have hdescent : baseEnd_2090773 < baseStart_2090773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090866 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2090866 : Nat := 118140960795 + 2090866 * 2 ^ 59
def prefixEnd_2090866 : Nat := 4983230072969 + 3 ^ 40 * 2090866 * 2
def baseEnd_2090866 : Nat := 477164107619431871493017

theorem tailTrace_2090866 : CollatzResearch.WordTrace tailWord_2090866 prefixEnd_2090866 477164107619431871493017 := by
  unfold tailWord_2090866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065037010789262082101113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50840098695438032218936301 19065037010789262082101113)
  ·
    refine ⟨14298777758091946561575835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19065037010789262082101113 14298777758091946561575835)
    ·
      refine ⟨21448166637137919842363753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14298777758091946561575835 21448166637137919842363753)
      ·
        refine ⟨16086124977853439881772815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21448166637137919842363753 16086124977853439881772815)
        ·
          refine ⟨24129187466780159822659223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086124977853439881772815 24129187466780159822659223)
          ·
            refine ⟨36193781200170239733988835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24129187466780159822659223 36193781200170239733988835)
            ·
              refine ⟨54290671800255359600983253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36193781200170239733988835 54290671800255359600983253)
              ·
                refine ⟨1272437620318484990648045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54290671800255359600983253 1272437620318484990648045)
                ·
                  refine ⟨477164107619431871493017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272437620318484990648045 477164107619431871493017)
                  ·
                    rfl

theorem cell21_2090866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2090866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090866 prefixEnd_2090866 := by exact prefixLift 2090866
  have htrace : WordTrace (prefixWord ++ tailWord_2090866) baseStart_2090866 baseEnd_2090866 := by
    simpa [prefixWord, tailWord_2090866, baseEnd_2090866] using wordTrace_append hprefix tailTrace_2090866
  have hstable : (prefixWord ++ tailWord_2090866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090866).length < 2 ^ (prefixWord ++ tailWord_2090866).sum := by decide
  have hdescent : baseEnd_2090866 < baseStart_2090866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090880 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_2090880 : Nat := 118140960795 + 2090880 * 2 ^ 59
def prefixEnd_2090880 : Nat := 4983230072969 + 3 ^ 40 * 2090880 * 2
def baseEnd_2090880 : Nat := 477167302610170958259655

theorem tailTrace_2090880 : CollatzResearch.WordTrace tailWord_2090880 prefixEnd_2090880 477167302610170958259655 := by
  unfold tailWord_2090880
  simp only [CollatzResearch.WordTrace]
  refine ⟨38130329332553164359707047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50840439110070885812942729 38130329332553164359707047)
  ·
    refine ⟨57195493998829746539560571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38130329332553164359707047 57195493998829746539560571)
    ·
      refine ⟨85793240998244619809340857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57195493998829746539560571 85793240998244619809340857)
      ·
        refine ⟨64344930748683464857005643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85793240998244619809340857 64344930748683464857005643)
        ·
          refine ⟨96517396123025197285508465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64344930748683464857005643 96517396123025197285508465)
          ·
            refine ⟨72388047092268897964131349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96517396123025197285508465 72388047092268897964131349)
            ·
              refine ⟨3393189707450104592068657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72388047092268897964131349 3393189707450104592068657)
              ·
                refine ⟨2544892280587578444051493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393189707450104592068657 2544892280587578444051493)
                ·
                  refine ⟨477167302610170958259655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544892280587578444051493 477167302610170958259655)
                  ·
                    rfl

theorem cell21_2090880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_2090880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090880 prefixEnd_2090880 := by exact prefixLift 2090880
  have htrace : WordTrace (prefixWord ++ tailWord_2090880) baseStart_2090880 baseEnd_2090880 := by
    simpa [prefixWord, tailWord_2090880, baseEnd_2090880] using wordTrace_append hprefix tailTrace_2090880
  have hstable : (prefixWord ++ tailWord_2090880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090880).length < 2 ^ (prefixWord ++ tailWord_2090880).sum := by decide
  have hdescent : baseEnd_2090880 < baseStart_2090880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090883 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 3]
def baseStart_2090883 : Nat := 118140960795 + 2090883 * 2 ^ 59
def prefixEnd_2090883 : Nat := 4983230072969 + 3 ^ 40 * 2090883 * 2
def baseEnd_2090883 : Nat := 477167987251043619709649

theorem tailTrace_2090883 : CollatzResearch.WordTrace tailWord_2090883 prefixEnd_2090883 477167987251043619709649 := by
  unfold tailWord_2090883
  simp only [CollatzResearch.WordTrace]
  refine ⟨76260768084095460231773303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50840512056063640154515535 76260768084095460231773303)
  ·
    refine ⟨114391152126143190347659955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76260768084095460231773303 114391152126143190347659955)
    ·
      refine ⟨171586728189214785521489933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114391152126143190347659955 171586728189214785521489933)
      ·
        refine ⟨64345023070955544570558725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171586728189214785521489933 64345023070955544570558725)
        ·
          refine ⟨12064691825804164606979761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64345023070955544570558725 12064691825804164606979761)
          ·
            refine ⟨9048518869353123455234821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12064691825804164606979761 9048518869353123455234821)
            ·
              refine ⟨1696597288003710647856529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9048518869353123455234821 1696597288003710647856529)
              ·
                refine ⟨1272447966002782985892397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696597288003710647856529 1272447966002782985892397)
                ·
                  refine ⟨477167987251043619709649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272447966002782985892397 477167987251043619709649)
                  ·
                    rfl

theorem cell21_2090883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].length) (baseStart_2090883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090883 prefixEnd_2090883 := by exact prefixLift 2090883
  have htrace : WordTrace (prefixWord ++ tailWord_2090883) baseStart_2090883 baseEnd_2090883 := by
    simpa [prefixWord, tailWord_2090883, baseEnd_2090883] using wordTrace_append hprefix tailTrace_2090883
  have hstable : (prefixWord ++ tailWord_2090883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090883).length < 2 ^ (prefixWord ++ tailWord_2090883).sum := by decide
  have hdescent : baseEnd_2090883 < baseStart_2090883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2090942 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2090942 : Nat := 118140960795 + 2090942 * 2 ^ 59
def prefixEnd_2090942 : Nat := 4983230072969 + 3 ^ 40 * 2090942 * 2
def baseEnd_2090942 : Nat := 477181451854872628226195

theorem tailTrace_2090942 : CollatzResearch.WordTrace tailWord_2090942 prefixEnd_2090942 477181451854872628226195 := by
  unfold tailWord_2090942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532864998860214163521385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50841946660587808872114053 9532864998860214163521385)
  ·
    refine ⟨7149648749145160622641039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9532864998860214163521385 7149648749145160622641039)
    ·
      refine ⟨10724473123717740933961559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149648749145160622641039 10724473123717740933961559)
      ·
        refine ⟨16086709685576611400942339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724473123717740933961559 16086709685576611400942339)
        ·
          refine ⟨24130064528364917101413509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086709685576611400942339 24130064528364917101413509)
          ·
            refine ⟨4524387099068421956515033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24130064528364917101413509 4524387099068421956515033)
            ·
              refine ⟨3393290324301316467386275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524387099068421956515033 3393290324301316467386275)
              ·
                refine ⟨5089935486451974701079413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393290324301316467386275 5089935486451974701079413)
                ·
                  refine ⟨477181451854872628226195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5089935486451974701079413 477181451854872628226195)
                  ·
                    rfl

theorem cell21_2090942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2090942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2090942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2090942 prefixEnd_2090942 := by exact prefixLift 2090942
  have htrace : WordTrace (prefixWord ++ tailWord_2090942) baseStart_2090942 baseEnd_2090942 := by
    simpa [prefixWord, tailWord_2090942, baseEnd_2090942] using wordTrace_append hprefix tailTrace_2090942
  have hstable : (prefixWord ++ tailWord_2090942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2090942).length < 2 ^ (prefixWord ++ tailWord_2090942).sum := by decide
  have hdescent : baseEnd_2090942 < baseStart_2090942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2090942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091001 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_2091001 : Nat := 118140960795 + 2091001 * 2 ^ 59
def prefixEnd_2091001 : Nat := 4983230072969 + 3 ^ 40 * 2091001 * 2
def baseEnd_2091001 : Nat := 477194916458701636742741

theorem tailTrace_2091001 : CollatzResearch.WordTrace tailWord_2091001 prefixEnd_2091001 477194916458701636742741 := by
  unfold tailWord_2091001
  simp only [CollatzResearch.WordTrace]
  refine ⟨76265071897667966384568857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50843381265111977589712571 76265071897667966384568857)
  ·
    refine ⟨57198803923250974788426643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76265071897667966384568857 57198803923250974788426643)
    ·
      refine ⟨85798205884876462182639965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57198803923250974788426643 85798205884876462182639965)
      ·
        refine ⟨32174327206828673318489987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85798205884876462182639965 32174327206828673318489987)
        ·
          refine ⟨48261490810243009977734981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32174327206828673318489987 48261490810243009977734981)
          ·
            refine ⟨9049029526920564370825309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48261490810243009977734981 9049029526920564370825309)
            ·
              refine ⟨3393386072595211639059491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9049029526920564370825309 3393386072595211639059491)
              ·
                refine ⟨5090079108892817458589237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393386072595211639059491 5090079108892817458589237)
                ·
                  refine ⟨477194916458701636742741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090079108892817458589237 477194916458701636742741)
                  ·
                    rfl

theorem cell21_2091001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_2091001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091001 prefixEnd_2091001 := by exact prefixLift 2091001
  have htrace : WordTrace (prefixWord ++ tailWord_2091001) baseStart_2091001 baseEnd_2091001 := by
    simpa [prefixWord, tailWord_2091001, baseEnd_2091001] using wordTrace_append hprefix tailTrace_2091001
  have hstable : (prefixWord ++ tailWord_2091001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091001).length < 2 ^ (prefixWord ++ tailWord_2091001).sum := by decide
  have hdescent : baseEnd_2091001 < baseStart_2091001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091108 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2091108 : Nat := 118140960795 + 2091108 * 2 ^ 59
def prefixEnd_2091108 : Nat := 4983230072969 + 3 ^ 40 * 2091108 * 2
def baseEnd_2091108 : Nat := 477219335316493228459189

theorem tailTrace_2091108 : CollatzResearch.WordTrace tailWord_2091108 prefixEnd_2091108 477219335316493228459189 := by
  unfold tailWord_2091108
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134487254140161829356989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50845983005520215772475985 38134487254140161829356989)
  ·
    refine ⟨14300432720302560686008871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38134487254140161829356989 14300432720302560686008871)
    ·
      refine ⟨21450649080453841029013307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14300432720302560686008871 21450649080453841029013307)
      ·
        refine ⟨32175973620680761543519961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450649080453841029013307 32175973620680761543519961)
        ·
          refine ⟨24131980215510571157639971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32175973620680761543519961 24131980215510571157639971)
          ·
            refine ⟨36197970323265856736459957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131980215510571157639971 36197970323265856736459957)
            ·
              refine ⟨3393559717806174069043121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36197970323265856736459957 3393559717806174069043121)
              ·
                refine ⟨2545169788354630551782341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393559717806174069043121 2545169788354630551782341)
                ·
                  refine ⟨477219335316493228459189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545169788354630551782341 477219335316493228459189)
                  ·
                    rfl

theorem cell21_2091108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2091108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091108 prefixEnd_2091108 := by exact prefixLift 2091108
  have htrace : WordTrace (prefixWord ++ tailWord_2091108) baseStart_2091108 baseEnd_2091108 := by
    simpa [prefixWord, tailWord_2091108, baseEnd_2091108] using wordTrace_append hprefix tailTrace_2091108
  have hstable : (prefixWord ++ tailWord_2091108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091108).length < 2 ^ (prefixWord ++ tailWord_2091108).sum := by decide
  have hdescent : baseEnd_2091108 < baseStart_2091108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091139 : List Nat := [1, 1, 1, 3, 3, 5, 2, 5]
def baseStart_2091139 : Nat := 118140960795 + 2091139 * 2 ^ 59
def prefixEnd_2091139 : Nat := 4983230072969 + 3 ^ 40 * 2091139 * 2
def baseEnd_2091139 : Nat := 159075469979614687814153

theorem tailTrace_2091139 : CollatzResearch.WordTrace tailWord_2091139 prefixEnd_2091139 159075469979614687814153 := by
  unfold tailWord_2091139
  simp only [CollatzResearch.WordTrace]
  refine ⟨76270105171168015953092471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50846736780778677302061647 76270105171168015953092471)
  ·
    refine ⟨114405157756752023929638707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76270105171168015953092471 114405157756752023929638707)
    ·
      refine ⟨171607736635128035894458061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114405157756752023929638707 171607736635128035894458061)
      ·
        refine ⟨64352901238173013460421773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171607736635128035894458061 64352901238173013460421773)
        ·
          refine ⟨24132337964314880047658165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64352901238173013460421773 24132337964314880047658165)
          ·
            refine ⟨2262406684154520004467953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24132337964314880047658165 2262406684154520004467953)
            ·
              refine ⟨1696805013115890003350965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262406684154520004467953 1696805013115890003350965)
              ·
                refine ⟨159075469979614687814153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696805013115890003350965 159075469979614687814153)
                ·
                  rfl

theorem cell21_2091139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].length) (baseStart_2091139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091139 prefixEnd_2091139 := by exact prefixLift 2091139
  have htrace : WordTrace (prefixWord ++ tailWord_2091139) baseStart_2091139 baseEnd_2091139 := by
    simpa [prefixWord, tailWord_2091139, baseEnd_2091139] using wordTrace_append hprefix tailTrace_2091139
  have hstable : (prefixWord ++ tailWord_2091139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091139).length < 2 ^ (prefixWord ++ tailWord_2091139).sum := by decide
  have hdescent : baseEnd_2091139 < baseStart_2091139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091156 : List Nat := [2, 4, 2, 3, 1, 2, 7]
def baseStart_2091156 : Nat := 118140960795 + 2091156 * 2 ^ 59
def prefixEnd_2091156 : Nat := 4983230072969 + 3 ^ 40 * 2091156 * 2
def baseEnd_2091156 : Nat := 53025587730050645739899

theorem tailTrace_2091156 : CollatzResearch.WordTrace tailWord_2091156 prefixEnd_2091156 53025587730050645739899 := by
  unfold tailWord_2091156
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135362606053213928230661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50847150141404285237640881 38135362606053213928230661)
  ·
    refine ⟨7150380488634977611543249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38135362606053213928230661 7150380488634977611543249)
    ·
      refine ⟨5362785366476233208657437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7150380488634977611543249 5362785366476233208657437)
      ·
        refine ⟨2011044512428587453246539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5362785366476233208657437 2011044512428587453246539)
        ·
          refine ⟨3016566768642881179869809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011044512428587453246539 3016566768642881179869809)
          ·
            refine ⟨2262425076482160884902357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016566768642881179869809 2262425076482160884902357)
            ·
              refine ⟨53025587730050645739899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2262425076482160884902357 53025587730050645739899)
              ·
                rfl

theorem cell21_2091156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 7].length) (baseStart_2091156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091156 prefixEnd_2091156 := by exact prefixLift 2091156
  have htrace : WordTrace (prefixWord ++ tailWord_2091156) baseStart_2091156 baseEnd_2091156 := by
    simpa [prefixWord, tailWord_2091156, baseEnd_2091156] using wordTrace_append hprefix tailTrace_2091156
  have hstable : (prefixWord ++ tailWord_2091156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091156).length < 2 ^ (prefixWord ++ tailWord_2091156).sum := by decide
  have hdescent : baseEnd_2091156 < baseStart_2091156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091170 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2091170 : Nat := 118140960795 + 2091170 * 2 ^ 59
def prefixEnd_2091170 : Nat := 4983230072969 + 3 ^ 40 * 2091170 * 2
def baseEnd_2091170 : Nat := 477233484561194898425729

theorem tailTrace_2091170 : CollatzResearch.WordTrace tailWord_2091170 prefixEnd_2091170 477233484561194898425729 := by
  unfold tailWord_2091170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19067808958513927061867741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50847490556037138831647309 19067808958513927061867741)
  ·
    refine ⟨7150428359442722648200403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19067808958513927061867741 7150428359442722648200403)
    ·
      refine ⟨10725642539164083972300605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7150428359442722648200403 10725642539164083972300605)
      ·
        refine ⟨4022115952186531489612727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10725642539164083972300605 4022115952186531489612727)
        ·
          refine ⟨6033173928279797234419091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022115952186531489612727 6033173928279797234419091)
          ·
            refine ⟨9049760892419695851628637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033173928279797234419091 9049760892419695851628637)
            ·
              refine ⟨3393660334657385944360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9049760892419695851628637 3393660334657385944360739)
              ·
                refine ⟨5090490501986078916541109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393660334657385944360739 5090490501986078916541109)
                ·
                  refine ⟨477233484561194898425729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090490501986078916541109 477233484561194898425729)
                  ·
                    rfl

theorem cell21_2091170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2091170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091170 prefixEnd_2091170 := by exact prefixLift 2091170
  have htrace : WordTrace (prefixWord ++ tailWord_2091170) baseStart_2091170 baseEnd_2091170 := by
    simpa [prefixWord, tailWord_2091170, baseEnd_2091170] using wordTrace_append hprefix tailTrace_2091170
  have hstable : (prefixWord ++ tailWord_2091170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091170).length < 2 ^ (prefixWord ++ tailWord_2091170).sum := by decide
  have hdescent : baseEnd_2091170 < baseStart_2091170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091221 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 3]
def baseStart_2091221 : Nat := 118140960795 + 2091221 * 2 ^ 59
def prefixEnd_2091221 : Nat := 4983230072969 + 3 ^ 40 * 2091221 * 2
def baseEnd_2091221 : Nat := 477245123456030143075625

theorem tailTrace_2091221 : CollatzResearch.WordTrace tailWord_2091221 prefixEnd_2091221 477245123456030143075625 := by
  unfold tailWord_2091221
  simp only [CollatzResearch.WordTrace]
  refine ⟨76273095956870943957577517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50848730637913962638385011 76273095956870943957577517)
  ·
    refine ⟨28602410983826603984091569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76273095956870943957577517 28602410983826603984091569)
    ·
      refine ⟨21451808237869952988068677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28602410983826603984091569 21451808237869952988068677)
      ·
        refine ⟨4022214044600616185262877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21451808237869952988068677 4022214044600616185262877)
        ·
          refine ⟨1508330266725231069473579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4022214044600616185262877 1508330266725231069473579)
          ·
            refine ⟨2262495400087846604210369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508330266725231069473579 2262495400087846604210369)
            ·
              refine ⟨1696871550065884953157777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262495400087846604210369 1696871550065884953157777)
              ·
                refine ⟨1272653662549413714868333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696871550065884953157777 1272653662549413714868333)
                ·
                  refine ⟨477245123456030143075625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272653662549413714868333 477245123456030143075625)
                  ·
                    rfl

theorem cell21_2091221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_2091221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091221 prefixEnd_2091221 := by exact prefixLift 2091221
  have htrace : WordTrace (prefixWord ++ tailWord_2091221) baseStart_2091221 baseEnd_2091221 := by
    simpa [prefixWord, tailWord_2091221, baseEnd_2091221] using wordTrace_append hprefix tailTrace_2091221
  have hstable : (prefixWord ++ tailWord_2091221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091221).length < 2 ^ (prefixWord ++ tailWord_2091221).sum := by decide
  have hdescent : baseEnd_2091221 < baseStart_2091221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091243 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_2091243 : Nat := 118140960795 + 2091243 * 2 ^ 59
def prefixEnd_2091243 : Nat := 4983230072969 + 3 ^ 40 * 2091243 * 2
def baseEnd_2091243 : Nat := 477250144155762993708913

theorem tailTrace_2091243 : CollatzResearch.WordTrace tailWord_2091243 prefixEnd_2091243 477250144155762993708913 := by
  unfold tailWord_2091243
  simp only [CollatzResearch.WordTrace]
  refine ⟨76273898362791241714878383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50849265575194161143252255 76273898362791241714878383)
  ·
    refine ⟨114410847544186862572317575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76273898362791241714878383 114410847544186862572317575)
    ·
      refine ⟨171616271316280293858476363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114410847544186862572317575 171616271316280293858476363)
      ·
        refine ⟨257424406974420440787714545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171616271316280293858476363 257424406974420440787714545)
        ·
          refine ⟨193068305230815330590785909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257424406974420440787714545 193068305230815330590785909)
          ·
            refine ⟨18100153615388937242886179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193068305230815330590785909 18100153615388937242886179)
            ·
              refine ⟨27150230423083405864329269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100153615388937242886179 27150230423083405864329269)
              ·
                refine ⟨2545334102164069299780869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27150230423083405864329269 2545334102164069299780869)
                ·
                  refine ⟨477250144155762993708913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545334102164069299780869 477250144155762993708913)
                  ·
                    rfl

theorem cell21_2091243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_2091243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091243 prefixEnd_2091243 := by exact prefixLift 2091243
  have htrace : WordTrace (prefixWord ++ tailWord_2091243) baseStart_2091243 baseEnd_2091243 := by
    simpa [prefixWord, tailWord_2091243, baseEnd_2091243] using wordTrace_append hprefix tailTrace_2091243
  have hstable : (prefixWord ++ tailWord_2091243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091243).length < 2 ^ (prefixWord ++ tailWord_2091243).sum := by decide
  have hdescent : baseEnd_2091243 < baseStart_2091243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091322 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_2091322 : Nat := 118140960795 + 2091322 * 2 ^ 59
def prefixEnd_2091322 : Nat := 4983230072969 + 3 ^ 40 * 2091322 * 2
def baseEnd_2091322 : Nat := 477268173032076411892085

theorem tailTrace_2091322 : CollatzResearch.WordTrace tailWord_2091322 prefixEnd_2091322 477268173032076411892085 := by
  unfold tailWord_2091322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069194932376259551751055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50851186486336692138002813 19069194932376259551751055)
  ·
    refine ⟨28603792398564389327626583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19069194932376259551751055 28603792398564389327626583)
    ·
      refine ⟨42905688597846583991439875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28603792398564389327626583 42905688597846583991439875)
      ·
        refine ⟨64358532896769875987159813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42905688597846583991439875 64358532896769875987159813)
        ·
          refine ⟨12067224918144351747592465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64358532896769875987159813 12067224918144351747592465)
          ·
            refine ⟨9050418688608263810694349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067224918144351747592465 9050418688608263810694349)
            ·
              refine ⟨3393907008228098929010381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9050418688608263810694349 3393907008228098929010381)
              ·
                refine ⟨1272715128085537098378893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3393907008228098929010381 1272715128085537098378893)
                ·
                  refine ⟨477268173032076411892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272715128085537098378893 477268173032076411892085)
                  ·
                    rfl

theorem cell21_2091322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_2091322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091322 prefixEnd_2091322 := by exact prefixLift 2091322
  have htrace : WordTrace (prefixWord ++ tailWord_2091322) baseStart_2091322 baseEnd_2091322 := by
    simpa [prefixWord, tailWord_2091322, baseEnd_2091322] using wordTrace_append hprefix tailTrace_2091322
  have hstable : (prefixWord ++ tailWord_2091322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091322).length < 2 ^ (prefixWord ++ tailWord_2091322).sum := by decide
  have hdescent : baseEnd_2091322 < baseStart_2091322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091364 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2091364 : Nat := 118140960795 + 2091364 * 2 ^ 59
def prefixEnd_2091364 : Nat := 4983230072969 + 3 ^ 40 * 2091364 * 2
def baseEnd_2091364 : Nat := 477277758004293672191999

theorem tailTrace_2091364 : CollatzResearch.WordTrace tailWord_2091364 prefixEnd_2091364 477277758004293672191999 := by
  unfold tailWord_2091364
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139155797676439690016573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50852207730235252920022097 38139155797676439690016573)
  ·
    refine ⟨14302183424128664883756215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38139155797676439690016573 14302183424128664883756215)
    ·
      refine ⟨21453275136192997325634323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14302183424128664883756215 21453275136192997325634323)
      ·
        refine ⟨32179912704289495988451485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21453275136192997325634323 32179912704289495988451485)
        ·
          refine ⟨12067467264108560995669307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32179912704289495988451485 12067467264108560995669307)
          ·
            refine ⟨18101200896162841493503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067467264108560995669307 18101200896162841493503961)
            ·
              refine ⟨13575900672122131120127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18101200896162841493503961 13575900672122131120127971)
              ·
                refine ⟨20363851008183196680191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13575900672122131120127971 20363851008183196680191957)
                ·
                  refine ⟨477277758004293672191999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20363851008183196680191957 477277758004293672191999)
                  ·
                    rfl

theorem cell21_2091364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2091364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091364 prefixEnd_2091364 := by exact prefixLift 2091364
  have htrace : WordTrace (prefixWord ++ tailWord_2091364) baseStart_2091364 baseEnd_2091364 := by
    simpa [prefixWord, tailWord_2091364, baseEnd_2091364] using wordTrace_append hprefix tailTrace_2091364
  have hstable : (prefixWord ++ tailWord_2091364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091364).length < 2 ^ (prefixWord ++ tailWord_2091364).sum := by decide
  have hdescent : baseEnd_2091364 < baseStart_2091364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091491 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 3]
def baseStart_2091491 : Nat := 118140960795 + 2091491 * 2 ^ 59
def prefixEnd_2091491 : Nat := 4983230072969 + 3 ^ 40 * 2091491 * 2
def baseEnd_2091491 : Nat := 477306741134569673575073

theorem tailTrace_2091491 : CollatzResearch.WordTrace tailWord_2091491 prefixEnd_2091491 477306741134569673575073 := by
  unfold tailWord_2091491
  simp only [CollatzResearch.WordTrace]
  refine ⟨76282943665892780069906327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50855295777261853379937551 76282943665892780069906327)
  ·
    refine ⟨114424415498839170104859491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76282943665892780069906327 114424415498839170104859491)
    ·
      refine ⟨171636623248258755157289237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114424415498839170104859491 171636623248258755157289237)
      ·
        refine ⟨8045466714762129147997933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171636623248258755157289237 8045466714762129147997933)
        ·
          refine ⟨3017050018035798430499225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8045466714762129147997933 3017050018035798430499225)
          ·
            refine ⟨2262787513526848822874419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017050018035798430499225 2262787513526848822874419)
            ·
              refine ⟨3394181270290273234311629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262787513526848822874419 3394181270290273234311629)
              ·
                refine ⟨1272817976358852462866861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3394181270290273234311629 1272817976358852462866861)
                ·
                  refine ⟨477306741134569673575073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272817976358852462866861 477306741134569673575073)
                  ·
                    rfl

theorem cell21_2091491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].length) (baseStart_2091491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091491 prefixEnd_2091491 := by exact prefixLift 2091491
  have htrace : WordTrace (prefixWord ++ tailWord_2091491) baseStart_2091491 baseEnd_2091491 := by
    simpa [prefixWord, tailWord_2091491, baseEnd_2091491] using wordTrace_append hprefix tailTrace_2091491
  have hstable : (prefixWord ++ tailWord_2091491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091491).length < 2 ^ (prefixWord ++ tailWord_2091491).sum := by decide
  have hdescent : baseEnd_2091491 < baseStart_2091491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091502 : List Nat := [4, 1, 2, 1, 2, 4, 7]
def baseStart_2091502 : Nat := 118140960795 + 2091502 * 2 ^ 59
def prefixEnd_2091502 : Nat := 4983230072969 + 3 ^ 40 * 2091502 * 2
def baseEnd_2091502 : Nat := 53034361276048455432413

theorem tailTrace_2091502 : CollatzResearch.WordTrace tailWord_2091502 prefixEnd_2091502 53034361276048455432413 := by
  unfold tailWord_2091502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535418108606616118569595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50855563245901952632371173 9535418108606616118569595)
  ·
    refine ⟨14303127162909924177854393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535418108606616118569595 14303127162909924177854393)
    ·
      refine ⟨10727345372182443133390795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14303127162909924177854393 10727345372182443133390795)
      ·
        refine ⟨16091018058273664700086193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10727345372182443133390795 16091018058273664700086193)
        ·
          refine ⟨12068263543705248525064645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16091018058273664700086193 12068263543705248525064645)
          ·
            refine ⟨2262799414444734098449621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12068263543705248525064645 2262799414444734098449621)
            ·
              refine ⟨53034361276048455432413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2262799414444734098449621 53034361276048455432413)
              ·
                rfl

theorem cell21_2091502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 7].length) (baseStart_2091502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091502 prefixEnd_2091502 := by exact prefixLift 2091502
  have htrace : WordTrace (prefixWord ++ tailWord_2091502) baseStart_2091502 baseEnd_2091502 := by
    simpa [prefixWord, tailWord_2091502, baseEnd_2091502] using wordTrace_append hprefix tailTrace_2091502
  have hstable : (prefixWord ++ tailWord_2091502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091502).length < 2 ^ (prefixWord ++ tailWord_2091502).sum := by decide
  have hdescent : baseEnd_2091502 < baseStart_2091502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091578 : List Nat := [3, 1, 1, 1, 3, 5, 1, 6]
def baseStart_2091578 : Nat := 118140960795 + 2091578 * 2 ^ 59
def prefixEnd_2091578 : Nat := 4983230072969 + 3 ^ 40 * 2091578 * 2
def baseEnd_2091578 : Nat := 159108865239958951874965

theorem tailTrace_2091578 : CollatzResearch.WordTrace tailWord_2091578 prefixEnd_2091578 159108865239958951874965 := by
  unfold tailWord_2091578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071529204144398482080847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50857411211051729285548925 19071529204144398482080847)
  ·
    refine ⟨28607293806216597723121271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19071529204144398482080847 28607293806216597723121271)
    ·
      refine ⟨42910940709324896584681907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28607293806216597723121271 42910940709324896584681907)
      ·
        refine ⟨64366411063987344877022861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42910940709324896584681907 64366411063987344877022861)
        ·
          refine ⟨24137404148995254328883573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64366411063987344877022861 24137404148995254328883573)
          ·
            refine ⟨2262881638968305093332835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24137404148995254328883573 2262881638968305093332835)
            ·
              refine ⟨3394322458452457639999253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262881638968305093332835 3394322458452457639999253)
              ·
                refine ⟨159108865239958951874965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3394322458452457639999253 159108865239958951874965)
                ·
                  rfl

theorem cell21_2091578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_2091578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091578 prefixEnd_2091578 := by exact prefixLift 2091578
  have htrace : WordTrace (prefixWord ++ tailWord_2091578) baseStart_2091578 baseEnd_2091578 := by
    simpa [prefixWord, tailWord_2091578, baseEnd_2091578] using wordTrace_append hprefix tailTrace_2091578
  have hstable : (prefixWord ++ tailWord_2091578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091578).length < 2 ^ (prefixWord ++ tailWord_2091578).sum := by decide
  have hdescent : baseEnd_2091578 < baseStart_2091578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091699 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_2091699 : Nat := 118140960795 + 2091699 * 2 ^ 59
def prefixEnd_2091699 : Nat := 4983230072969 + 3 ^ 40 * 2091699 * 2
def baseEnd_2091699 : Nat := 477354209568407534107981

theorem tailTrace_2091699 : CollatzResearch.WordTrace tailWord_2091699 prefixEnd_2091699 477354209568407534107981 := by
  unfold tailWord_2091699
  simp only [CollatzResearch.WordTrace]
  refine ⟨76290530049139231593478151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50860353366092821062318767 76290530049139231593478151)
  ·
    refine ⟨114435795073708847390217227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76290530049139231593478151 114435795073708847390217227)
    ·
      refine ⟨171653692610563271085325841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114435795073708847390217227 171653692610563271085325841)
      ·
        refine ⟨128740269457922453313994381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171653692610563271085325841 128740269457922453313994381)
        ·
          refine ⟨48277601046720919992747893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128740269457922453313994381 48277601046720919992747893)
          ·
            refine ⟨4526025098130086249320115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48277601046720919992747893 4526025098130086249320115)
            ·
              refine ⟨6789037647195129373980173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526025098130086249320115 6789037647195129373980173)
              ·
                refine ⟨2545889117698173515242565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6789037647195129373980173 2545889117698173515242565)
                ·
                  refine ⟨477354209568407534107981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545889117698173515242565 477354209568407534107981)
                  ·
                    rfl

theorem cell21_2091699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_2091699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091699 prefixEnd_2091699 := by exact prefixLift 2091699
  have htrace : WordTrace (prefixWord ++ tailWord_2091699) baseStart_2091699 baseEnd_2091699 := by
    simpa [prefixWord, tailWord_2091699, baseEnd_2091699] using wordTrace_append hprefix tailTrace_2091699
  have hstable : (prefixWord ++ tailWord_2091699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091699).length < 2 ^ (prefixWord ++ tailWord_2091699).sum := by decide
  have hdescent : baseEnd_2091699 < baseStart_2091699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091730 : List Nat := [3, 2, 2, 2, 4, 8]
def baseStart_2091730 : Nat := 118140960795 + 2091730 * 2 ^ 59
def prefixEnd_2091730 : Nat := 4983230072969 + 3 ^ 40 * 2091730 * 2
def baseEnd_2091730 : Nat := 17680047562620680336713

theorem tailTrace_2091730 : CollatzResearch.WordTrace tailWord_2091730 prefixEnd_2091730 17680047562620680336713 := by
  unfold tailWord_2091730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072915178006730971964161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50861107141351282591904429 19072915178006730971964161)
  ·
    refine ⟨14304686383505048228973121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19072915178006730971964161 14304686383505048228973121)
    ·
      refine ⟨10728514787628786171729841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14304686383505048228973121 10728514787628786171729841)
      ·
        refine ⟨8046386090721589628797381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728514787628786171729841 8046386090721589628797381)
        ·
          refine ⟨1508697392010298055399509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8046386090721589628797381 1508697392010298055399509)
          ·
            refine ⟨17680047562620680336713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1508697392010298055399509 17680047562620680336713)
            ·
              rfl

theorem cell21_2091730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 8].length) (baseStart_2091730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091730 prefixEnd_2091730 := by exact prefixLift 2091730
  have htrace : WordTrace (prefixWord ++ tailWord_2091730) baseStart_2091730 baseEnd_2091730 := by
    simpa [prefixWord, tailWord_2091730, baseEnd_2091730] using wordTrace_append hprefix tailTrace_2091730
  have hstable : (prefixWord ++ tailWord_2091730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091730).length < 2 ^ (prefixWord ++ tailWord_2091730).sum := by decide
  have hdescent : baseEnd_2091730 < baseStart_2091730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091733 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_2091733 : Nat := 118140960795 + 2091733 * 2 ^ 59
def prefixEnd_2091733 : Nat := 4983230072969 + 3 ^ 40 * 2091733 * 2
def baseEnd_2091733 : Nat := 477361968831631030541245

theorem tailTrace_2091733 : CollatzResearch.WordTrace tailWord_2091733 prefixEnd_2091733 477361968831631030541245 := by
  unfold tailWord_2091733
  simp only [CollatzResearch.WordTrace]
  refine ⟨76291770131016055400215853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50861180087344036933477235 76291770131016055400215853)
  ·
    refine ⟨28609413799131020775080945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76291770131016055400215853 28609413799131020775080945)
    ·
      refine ⟨21457060349348265581310709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28609413799131020775080945 21457060349348265581310709)
      ·
        refine ⟨2011599407751399898247879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21457060349348265581310709 2011599407751399898247879)
        ·
          refine ⟨3017399111627099847371819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011599407751399898247879 3017399111627099847371819)
          ·
            refine ⟨4526098667440649771057729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017399111627099847371819 4526098667440649771057729)
            ·
              refine ⟨3394574000580487328293297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526098667440649771057729 3394574000580487328293297)
              ·
                refine ⟨2545930500435365496219973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394574000580487328293297 2545930500435365496219973)
                ·
                  refine ⟨477361968831631030541245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545930500435365496219973 477361968831631030541245)
                  ·
                    rfl

theorem cell21_2091733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_2091733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091733 prefixEnd_2091733 := by exact prefixLift 2091733
  have htrace : WordTrace (prefixWord ++ tailWord_2091733) baseStart_2091733 baseEnd_2091733 := by
    simpa [prefixWord, tailWord_2091733, baseEnd_2091733] using wordTrace_append hprefix tailTrace_2091733
  have hstable : (prefixWord ++ tailWord_2091733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091733).length < 2 ^ (prefixWord ++ tailWord_2091733).sum := by decide
  have hdescent : baseEnd_2091733 < baseStart_2091733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091778 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2091778 : Nat := 118140960795 + 2091778 * 2 ^ 59
def prefixEnd_2091778 : Nat := 4983230072969 + 3 ^ 40 * 2091778 * 2
def baseEnd_2091778 : Nat := 477372238444720952291153

theorem tailTrace_2091778 : CollatzResearch.WordTrace tailWord_2091778 prefixEnd_2091778 477372238444720952291153 := by
  unfold tailWord_2091778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073352853963257021400997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50862274277235352057069325 19073352853963257021400997)
  ·
    refine ⟨3576253660118110691512687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19073352853963257021400997 3576253660118110691512687)
    ·
      refine ⟨5364380490177166037269031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576253660118110691512687 5364380490177166037269031)
      ·
        refine ⟨8046570735265749055903547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364380490177166037269031 8046570735265749055903547)
        ·
          refine ⟨12069856102898623583855321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046570735265749055903547 12069856102898623583855321)
          ·
            refine ⟨9052392077173967687891491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069856102898623583855321 9052392077173967687891491)
            ·
              refine ⟨13578588115760951531837237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052392077173967687891491 13578588115760951531837237)
              ·
                refine ⟨1272992635852589206109741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13578588115760951531837237 1272992635852589206109741)
                ·
                  refine ⟨477372238444720952291153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272992635852589206109741 477372238444720952291153)
                  ·
                    rfl

theorem cell21_2091778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2091778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091778 prefixEnd_2091778 := by exact prefixLift 2091778
  have htrace : WordTrace (prefixWord ++ tailWord_2091778) baseStart_2091778 baseEnd_2091778 := by
    simpa [prefixWord, tailWord_2091778, baseEnd_2091778] using wordTrace_append hprefix tailTrace_2091778
  have hstable : (prefixWord ++ tailWord_2091778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091778).length < 2 ^ (prefixWord ++ tailWord_2091778).sum := by decide
  have hdescent : baseEnd_2091778 < baseStart_2091778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091865 : List Nat := [1, 2, 1, 2, 2, 5, 2, 6]
def baseStart_2091865 : Nat := 118140960795 + 2091865 * 2 ^ 59
def prefixEnd_2091865 : Nat := 4983230072969 + 3 ^ 40 * 2091865 * 2
def baseEnd_2091865 : Nat := 159130697676676044780325

theorem tailTrace_2091865 : CollatzResearch.WordTrace tailWord_2091865 prefixEnd_2091865 159130697676676044780325 := by
  unfold tailWord_2091865
  simp only [CollatzResearch.WordTrace]
  refine ⟨76296584566537841944021049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50864389711025227962680699 76296584566537841944021049)
  ·
    refine ⟨57222438424903381458015787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76296584566537841944021049 57222438424903381458015787)
    ·
      refine ⟨85833657637355072187023681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57222438424903381458015787 85833657637355072187023681)
      ·
        refine ⟨64375243228016304140267761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85833657637355072187023681 64375243228016304140267761)
        ·
          refine ⟨48281432421012228105200821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64375243228016304140267761 48281432421012228105200821)
          ·
            refine ⟨4526384289469896384862577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48281432421012228105200821 4526384289469896384862577)
            ·
              refine ⟨3394788217102422288646933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526384289469896384862577 3394788217102422288646933)
              ·
                refine ⟨159130697676676044780325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3394788217102422288646933 159130697676676044780325)
                ·
                  rfl

theorem cell21_2091865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_2091865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091865 prefixEnd_2091865 := by exact prefixLift 2091865
  have htrace : WordTrace (prefixWord ++ tailWord_2091865) baseStart_2091865 baseEnd_2091865 := by
    simpa [prefixWord, tailWord_2091865, baseEnd_2091865] using wordTrace_append hprefix tailTrace_2091865
  have hstable : (prefixWord ++ tailWord_2091865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091865).length < 2 ^ (prefixWord ++ tailWord_2091865).sum := by decide
  have hdescent : baseEnd_2091865 < baseStart_2091865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091868 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_2091868 : Nat := 118140960795 + 2091868 * 2 ^ 59
def prefixEnd_2091868 : Nat := 4983230072969 + 3 ^ 40 * 2091868 * 2
def baseEnd_2091868 : Nat := 477392777670900795790969

theorem tailTrace_2091868 : CollatzResearch.WordTrace tailWord_2091868 prefixEnd_2091868 477392777670900795790969 := by
  unfold tailWord_2091868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38148346992763486728190129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50864462657017982304253505 38148346992763486728190129)
  ·
    refine ⟨28611260244572615046142597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38148346992763486728190129 28611260244572615046142597)
    ·
      refine ⟨5364611295857365321151737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28611260244572615046142597 5364611295857365321151737)
      ·
        refine ⟨4023458471893023990863803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364611295857365321151737 4023458471893023990863803)
        ·
          refine ⟨6035187707839535986295705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023458471893023990863803 6035187707839535986295705)
          ·
            refine ⟨4526390780879651989721779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035187707839535986295705 4526390780879651989721779)
            ·
              refine ⟨6789586171319477984582669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526390780879651989721779 6789586171319477984582669)
              ·
                refine ⟨2546094814244804244218501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6789586171319477984582669 2546094814244804244218501)
                ·
                  refine ⟨477392777670900795790969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546094814244804244218501 477392777670900795790969)
                  ·
                    rfl

theorem cell21_2091868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_2091868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091868 prefixEnd_2091868 := by exact prefixLift 2091868
  have htrace : WordTrace (prefixWord ++ tailWord_2091868) baseStart_2091868 baseEnd_2091868 := by
    simpa [prefixWord, tailWord_2091868, baseEnd_2091868] using wordTrace_append hprefix tailTrace_2091868
  have hstable : (prefixWord ++ tailWord_2091868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091868).length < 2 ^ (prefixWord ++ tailWord_2091868).sum := by decide
  have hdescent : baseEnd_2091868 < baseStart_2091868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2091913 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 3]
def baseStart_2091913 : Nat := 118140960795 + 2091913 * 2 ^ 59
def prefixEnd_2091913 : Nat := 4983230072969 + 3 ^ 40 * 2091913 * 2
def baseEnd_2091913 : Nat := 477403047283990717540877

theorem tailTrace_2091913 : CollatzResearch.WordTrace tailWord_2091913 prefixEnd_2091913 477403047283990717540877 := by
  unfold tailWord_2091913
  simp only [CollatzResearch.WordTrace]
  refine ⟨76298335270363946141768393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50865556846909297427845595 76298335270363946141768393)
  ·
    refine ⟨57223751452772959606326295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76298335270363946141768393 57223751452772959606326295)
    ·
      refine ⟨85835627179159439409489443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57223751452772959606326295 85835627179159439409489443)
      ·
        refine ⟨128753440768739159114234165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85835627179159439409489443 128753440768739159114234165)
        ·
          refine ⟨12070635072069296166959453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128753440768739159114234165 12070635072069296166959453)
          ·
            refine ⟨4526488152025986062609795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12070635072069296166959453 4526488152025986062609795)
            ·
              refine ⟨6789732228038979093914693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526488152025986062609795 6789732228038979093914693)
              ·
                refine ⟨1273074792757308580109005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6789732228038979093914693 1273074792757308580109005)
                ·
                  refine ⟨477403047283990717540877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273074792757308580109005 477403047283990717540877)
                  ·
                    rfl

theorem cell21_2091913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_2091913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2091913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2091913 prefixEnd_2091913 := by exact prefixLift 2091913
  have htrace : WordTrace (prefixWord ++ tailWord_2091913) baseStart_2091913 baseEnd_2091913 := by
    simpa [prefixWord, tailWord_2091913, baseEnd_2091913] using wordTrace_append hprefix tailTrace_2091913
  have hstable : (prefixWord ++ tailWord_2091913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2091913).length < 2 ^ (prefixWord ++ tailWord_2091913).sum := by decide
  have hdescent : baseEnd_2091913 < baseStart_2091913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2091913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092017 : List Nat := [1, 2, 2, 2, 4, 3, 7]
def baseStart_2092017 : Nat := 118140960795 + 2092017 * 2 ^ 59
def prefixEnd_2092017 : Nat := 4983230072969 + 3 ^ 40 * 2092017 * 2
def baseEnd_2092017 : Nat := 53047420166767738645259

theorem tailTrace_2092017 : CollatzResearch.WordTrace tailWord_2092017 prefixEnd_2092017 53047420166767738645259 := by
  unfold tailWord_2092017
  simp only [CollatzResearch.WordTrace]
  refine ⟨76302128461987171903554305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50868085641324781269036203 76302128461987171903554305)
  ·
    refine ⟨57226596346490378927665729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76302128461987171903554305 57226596346490378927665729)
    ·
      refine ⟨42919947259867784195749297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57226596346490378927665729 42919947259867784195749297)
      ·
        refine ⟨32189960444900838146811973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42919947259867784195749297 32189960444900838146811973)
        ·
          refine ⟨6035617583418907152527245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32189960444900838146811973 6035617583418907152527245)
          ·
            refine ⟨2263356593782090182197717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035617583418907152527245 2263356593782090182197717)
            ·
              refine ⟨53047420166767738645259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2263356593782090182197717 53047420166767738645259)
              ·
                rfl

theorem cell21_2092017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 7].length) (baseStart_2092017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092017 prefixEnd_2092017 := by exact prefixLift 2092017
  have htrace : WordTrace (prefixWord ++ tailWord_2092017) baseStart_2092017 baseEnd_2092017 := by
    simpa [prefixWord, tailWord_2092017, baseEnd_2092017] using wordTrace_append hprefix tailTrace_2092017
  have hstable : (prefixWord ++ tailWord_2092017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092017).length < 2 ^ (prefixWord ++ tailWord_2092017).sum := by decide
  have hdescent : baseEnd_2092017 < baseStart_2092017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092093 : List Nat := [1, 4, 1, 3, 1, 2, 3, 6]
def baseStart_2092093 : Nat := 118140960795 + 2092093 * 2 ^ 59
def prefixEnd_2092093 : Nat := 4983230072969 + 3 ^ 40 * 2092093 * 2
def baseEnd_2092093 : Nat := 159148041912116801513503

theorem tailTrace_2092093 : CollatzResearch.WordTrace tailWord_2092093 prefixEnd_2092093 159148041912116801513503 := by
  unfold tailWord_2092093
  simp only [CollatzResearch.WordTrace]
  refine ⟨76304900409711836883320933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50869933606474557922213955 76304900409711836883320933)
  ·
    refine ⟨14307168826820969415622675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76304900409711836883320933 14307168826820969415622675)
    ·
      refine ⟨21460753240231454123434013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14307168826820969415622675 21460753240231454123434013)
      ·
        refine ⟨8047782465086795296287755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21460753240231454123434013 8047782465086795296287755)
        ·
          refine ⟨12071673697630192944431633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047782465086795296287755 12071673697630192944431633)
          ·
            refine ⟨9053755273222644708323725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12071673697630192944431633 9053755273222644708323725)
            ·
              refine ⟨3395158227458491765621397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9053755273222644708323725 3395158227458491765621397)
              ·
                refine ⟨159148041912116801513503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3395158227458491765621397 159148041912116801513503)
                ·
                  rfl

theorem cell21_2092093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_2092093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092093 prefixEnd_2092093 := by exact prefixLift 2092093
  have htrace : WordTrace (prefixWord ++ tailWord_2092093) baseStart_2092093 baseEnd_2092093 := by
    simpa [prefixWord, tailWord_2092093, baseEnd_2092093] using wordTrace_append hprefix tailTrace_2092093
  have hstable : (prefixWord ++ tailWord_2092093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092093).length < 2 ^ (prefixWord ++ tailWord_2092093).sum := by decide
  have hdescent : baseEnd_2092093 < baseStart_2092093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092141 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2092141 : Nat := 118140960795 + 2092141 * 2 ^ 59
def prefixEnd_2092141 : Nat := 4983230072969 + 3 ^ 40 * 2092141 * 2
def baseEnd_2092141 : Nat := 477455079990312987740411

theorem tailTrace_2092141 : CollatzResearch.WordTrace tailWord_2092141 prefixEnd_2092141 477455079990312987740411 := by
  unfold tailWord_2092141
  simp only [CollatzResearch.WordTrace]
  refine ⟨76306651113537941081068277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50871100742358627387378851 76306651113537941081068277)
  ·
    refine ⟨7153748541894181976350151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76306651113537941081068277 7153748541894181976350151)
    ·
      refine ⟨10730622812841272964525227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153748541894181976350151 10730622812841272964525227)
      ·
        refine ⟨16095934219261909446787841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10730622812841272964525227 16095934219261909446787841)
        ·
          refine ⟨12071950664446432085090881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16095934219261909446787841 12071950664446432085090881)
          ·
            refine ⟨9053962998334824063818161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12071950664446432085090881 9053962998334824063818161)
            ·
              refine ⟨6790472248751118047863621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053962998334824063818161 6790472248751118047863621)
              ·
                refine ⟨1273213546640834633974429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6790472248751118047863621 1273213546640834633974429)
                ·
                  refine ⟨477455079990312987740411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273213546640834633974429 477455079990312987740411)
                  ·
                    rfl

theorem cell21_2092141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2092141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092141 prefixEnd_2092141 := by exact prefixLift 2092141
  have htrace : WordTrace (prefixWord ++ tailWord_2092141) baseStart_2092141 baseEnd_2092141 := by
    simpa [prefixWord, tailWord_2092141, baseEnd_2092141] using wordTrace_append hprefix tailTrace_2092141
  have hstable : (prefixWord ++ tailWord_2092141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092141).length < 2 ^ (prefixWord ++ tailWord_2092141).sum := by decide
  have hdescent : baseEnd_2092141 < baseStart_2092141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092169 : List Nat := [1, 2, 1, 1, 4, 3, 4, 5]
def baseStart_2092169 : Nat := 118140960795 + 2092169 * 2 ^ 59
def prefixEnd_2092169 : Nat := 4983230072969 + 3 ^ 40 * 2092169 * 2
def baseEnd_2092169 : Nat := 159153823323930387091229

theorem tailTrace_2092169 : CollatzResearch.WordTrace tailWord_2092169 prefixEnd_2092169 159153823323930387091229 := by
  unfold tailWord_2092169
  simp only [CollatzResearch.WordTrace]
  refine ⟨76307672357436501863087561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50871781571624334575391707 76307672357436501863087561)
  ·
    refine ⟨57230754268077376397315671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76307672357436501863087561 57230754268077376397315671)
    ·
      refine ⟨85846131402116064595973507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57230754268077376397315671 85846131402116064595973507)
      ·
        refine ⟨128769197103174096893960261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85846131402116064595973507 128769197103174096893960261)
        ·
          refine ⟨24144224456845143167617549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128769197103174096893960261 24144224456845143167617549)
          ·
            refine ⟨9054084171316928687856581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24144224456845143167617549 9054084171316928687856581)
            ·
              refine ⟨1697640782121924128973109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9054084171316928687856581 1697640782121924128973109)
              ·
                refine ⟨159153823323930387091229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1697640782121924128973109 159153823323930387091229)
                ·
                  rfl

theorem cell21_2092169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].length) (baseStart_2092169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092169 prefixEnd_2092169 := by exact prefixLift 2092169
  have htrace : WordTrace (prefixWord ++ tailWord_2092169) baseStart_2092169 baseEnd_2092169 := by
    simpa [prefixWord, tailWord_2092169, baseEnd_2092169] using wordTrace_append hprefix tailTrace_2092169
  have hstable : (prefixWord ++ tailWord_2092169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092169).length < 2 ^ (prefixWord ++ tailWord_2092169).sum := by decide
  have hdescent : baseEnd_2092169 < baseStart_2092169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092273 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_2092273 : Nat := 118140960795 + 2092273 * 2 ^ 59
def prefixEnd_2092273 : Nat := 4983230072969 + 3 ^ 40 * 2092273 * 2
def baseEnd_2092273 : Nat := 477485204188710091540141

theorem tailTrace_2092273 : CollatzResearch.WordTrace tailWord_2092273 prefixEnd_2092273 477485204188710091540141 := by
  unfold tailWord_2092273
  simp only [CollatzResearch.WordTrace]
  refine ⟨76311465549059727624873473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50874310366039818416582315 76311465549059727624873473)
  ·
    refine ⟨57233599161794795718655105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76311465549059727624873473 57233599161794795718655105)
    ·
      refine ⟨42925199371346096788991329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57233599161794795718655105 42925199371346096788991329)
      ·
        refine ⟨32193899528509572591743497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42925199371346096788991329 32193899528509572591743497)
        ·
          refine ⟨24145424646382179443807623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32193899528509572591743497 24145424646382179443807623)
          ·
            refine ⟨36218136969573269165711435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145424646382179443807623 36218136969573269165711435)
            ·
              refine ⟨54327205454359903748567153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36218136969573269165711435 54327205454359903748567153)
              ·
                refine ⟨40745404090769927811425365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54327205454359903748567153 40745404090769927811425365)
                ·
                  refine ⟨477485204188710091540141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40745404090769927811425365 477485204188710091540141)
                  ·
                    rfl

theorem cell21_2092273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_2092273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092273 prefixEnd_2092273 := by exact prefixLift 2092273
  have htrace : WordTrace (prefixWord ++ tailWord_2092273) baseStart_2092273 baseEnd_2092273 := by
    simpa [prefixWord, tailWord_2092273, baseEnd_2092273] using wordTrace_append hprefix tailTrace_2092273
  have hstable : (prefixWord ++ tailWord_2092273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092273).length < 2 ^ (prefixWord ++ tailWord_2092273).sum := by decide
  have hdescent : baseEnd_2092273 < baseStart_2092273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092338 : List Nat := [3, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2092338 : Nat := 118140960795 + 2092338 * 2 ^ 59
def prefixEnd_2092338 : Nat := 4983230072969 + 3 ^ 40 * 2092338 * 2
def baseEnd_2092338 : Nat := 159166679358094807652225

theorem tailTrace_2092338 : CollatzResearch.WordTrace tailWord_2092338 prefixEnd_2092338 159166679358094807652225 := by
  unfold tailWord_2092338
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078459073456060931497417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50875890862549495817326445 19078459073456060931497417)
  ·
    refine ⟨14308844305092045698623063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19078459073456060931497417 14308844305092045698623063)
    ·
      refine ⟨21463266457638068547934595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308844305092045698623063 21463266457638068547934595)
      ·
        refine ⟨32194899686457102821901893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463266457638068547934595 32194899686457102821901893)
        ·
          refine ⟨6036543691210706779106605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32194899686457102821901893 6036543691210706779106605)
          ·
            refine ⟨2263703884204015042164977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6036543691210706779106605 2263703884204015042164977)
            ·
              refine ⟨1697777913153011281623733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263703884204015042164977 1697777913153011281623733)
              ·
                refine ⟨159166679358094807652225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1697777913153011281623733 159166679358094807652225)
                ·
                  rfl

theorem cell21_2092338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2092338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092338 prefixEnd_2092338 := by exact prefixLift 2092338
  have htrace : WordTrace (prefixWord ++ tailWord_2092338) baseStart_2092338 baseEnd_2092338 := by
    simpa [prefixWord, tailWord_2092338, baseEnd_2092338] using wordTrace_append hprefix tailTrace_2092338
  have hstable : (prefixWord ++ tailWord_2092338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092338).length < 2 ^ (prefixWord ++ tailWord_2092338).sum := by decide
  have hdescent : baseEnd_2092338 < baseStart_2092338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092366 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2092366 : Nat := 118140960795 + 2092366 * 2 ^ 59
def prefixEnd_2092366 : Nat := 4983230072969 + 3 ^ 40 * 2092366 * 2
def baseEnd_2092366 : Nat := 477506428055762596489951

theorem tailTrace_2092366 : CollatzResearch.WordTrace tailWord_2092366 prefixEnd_2092366 477506428055762596489951 := by
  unfold tailWord_2092366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539357192215350563501119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50876571691815203005339301 9539357192215350563501119)
  ·
    refine ⟨14309035788323025845251679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9539357192215350563501119 14309035788323025845251679)
    ·
      refine ⟨21463553682484538767877519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14309035788323025845251679 21463553682484538767877519)
      ·
        refine ⟨32195330523726808151816279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463553682484538767877519 32195330523726808151816279)
        ·
          refine ⟨48292995785590212227724419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32195330523726808151816279 48292995785590212227724419)
          ·
            refine ⟨72439493678385318341586629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48292995785590212227724419 72439493678385318341586629)
            ·
              refine ⟨13582405064697247189047493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72439493678385318341586629 13582405064697247189047493)
              ·
                refine ⟨2546700949630733847946405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13582405064697247189047493 2546700949630733847946405)
                ·
                  refine ⟨477506428055762596489951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546700949630733847946405 477506428055762596489951)
                  ·
                    rfl

theorem cell21_2092366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2092366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092366 prefixEnd_2092366 := by exact prefixLift 2092366
  have htrace : WordTrace (prefixWord ++ tailWord_2092366) baseStart_2092366 baseEnd_2092366 := by
    simpa [prefixWord, tailWord_2092366, baseEnd_2092366] using wordTrace_append hprefix tailTrace_2092366
  have hstable : (prefixWord ++ tailWord_2092366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092366).length < 2 ^ (prefixWord ++ tailWord_2092366).sum := by decide
  have hdescent : baseEnd_2092366 < baseStart_2092366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092369 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 3]
def baseStart_2092369 : Nat := 118140960795 + 2092369 * 2 ^ 59
def prefixEnd_2092369 : Nat := 4983230072969 + 3 ^ 40 * 2092369 * 2
def baseEnd_2092369 : Nat := 477507112696635257939945

theorem tailTrace_2092369 : CollatzResearch.WordTrace tailWord_2092369 prefixEnd_2092369 477507112696635257939945 := by
  unfold tailWord_2092369
  simp only [CollatzResearch.WordTrace]
  refine ⟨76314966956711936020368161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50876644637807957346912107 76314966956711936020368161)
  ·
    refine ⟨57236225217533952015276121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76314966956711936020368161 57236225217533952015276121)
    ·
      refine ⟨42927168913150464011457091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57236225217533952015276121 42927168913150464011457091)
      ·
        refine ⟨64390753369725696017185637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42927168913150464011457091 64390753369725696017185637)
        ·
          refine ⟨12073266256823568003222307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64390753369725696017185637 12073266256823568003222307)
          ·
            refine ⟨18109899385235352004833461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073266256823568003222307 18109899385235352004833461)
            ·
              refine ⟨1697803067365814250453137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18109899385235352004833461 1697803067365814250453137)
              ·
                refine ⟨1273352300524360687839853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697803067365814250453137 1273352300524360687839853)
                ·
                  refine ⟨477507112696635257939945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273352300524360687839853 477507112696635257939945)
                  ·
                    rfl

theorem cell21_2092369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_2092369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092369 prefixEnd_2092369 := by exact prefixLift 2092369
  have htrace : WordTrace (prefixWord ++ tailWord_2092369) baseStart_2092369 baseEnd_2092369 := by
    simpa [prefixWord, tailWord_2092369, baseEnd_2092369] using wordTrace_append hprefix tailTrace_2092369
  have hstable : (prefixWord ++ tailWord_2092369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092369).length < 2 ^ (prefixWord ++ tailWord_2092369).sum := by decide
  have hdescent : baseEnd_2092369 < baseStart_2092369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092414 : List Nat := [4, 2, 3, 2, 1, 9]
def baseStart_2092414 : Nat := 118140960795 + 2092414 * 2 ^ 59
def prefixEnd_2092414 : Nat := 4983230072969 + 3 ^ 40 * 2092414 * 2
def baseEnd_2092414 : Nat := 17685828974434265914439

theorem tailTrace_2092414 : CollatzResearch.WordTrace tailWord_2092414 prefixEnd_2092414 17685828974434265914439 := by
  unfold tailWord_2092414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539576030193613588219537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50877738827699272470504197 9539576030193613588219537)
  ·
    refine ⟨7154682022645210191164653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9539576030193613588219537 7154682022645210191164653)
    ·
      refine ⟨2683005758491953821686745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7154682022645210191164653 2683005758491953821686745)
      ·
        refine ⟨2012254318868965366265059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683005758491953821686745 2012254318868965366265059)
        ·
          refine ⟨3018381478303448049397589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012254318868965366265059 3018381478303448049397589)
          ·
            refine ⟨17685828974434265914439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3018381478303448049397589 17685828974434265914439)
            ·
              rfl

theorem cell21_2092414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 9].length) (baseStart_2092414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092414 prefixEnd_2092414 := by exact prefixLift 2092414
  have htrace : WordTrace (prefixWord ++ tailWord_2092414) baseStart_2092414 baseEnd_2092414 := by
    simpa [prefixWord, tailWord_2092414, baseEnd_2092414] using wordTrace_append hprefix tailTrace_2092414
  have hstable : (prefixWord ++ tailWord_2092414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092414).length < 2 ^ (prefixWord ++ tailWord_2092414).sum := by decide
  have hdescent : baseEnd_2092414 < baseStart_2092414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092428 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2092428 : Nat := 118140960795 + 2092428 * 2 ^ 59
def prefixEnd_2092428 : Nat := 4983230072969 + 3 ^ 40 * 2092428 * 2
def baseEnd_2092428 : Nat := 477520577300464266456491

theorem tailTrace_2092428 : CollatzResearch.WordTrace tailWord_2092428 prefixEnd_2092428 477520577300464266456491 := by
  unfold tailWord_2092428
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158559431749094548382969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50878079242332126064510625 38158559431749094548382969)
  ·
    refine ⟨28618919573811820911287227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38158559431749094548382969 28618919573811820911287227)
    ·
      refine ⟨42928379360717731366930841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618919573811820911287227 42928379360717731366930841)
      ·
        refine ⟨32196284520538298525198131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42928379360717731366930841 32196284520538298525198131)
        ·
          refine ⟨48294426780807447787797197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32196284520538298525198131 48294426780807447787797197)
          ·
            refine ⟨18110410042802792920423949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48294426780807447787797197 18110410042802792920423949)
            ·
              refine ⟨6791403766051047345158981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18110410042802792920423949 6791403766051047345158981)
              ·
                refine ⟨1273388206134571377217309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6791403766051047345158981 1273388206134571377217309)
                ·
                  refine ⟨477520577300464266456491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273388206134571377217309 477520577300464266456491)
                  ·
                    rfl

theorem cell21_2092428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2092428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092428 prefixEnd_2092428 := by exact prefixLift 2092428
  have htrace : WordTrace (prefixWord ++ tailWord_2092428) baseStart_2092428 baseEnd_2092428 := by
    simpa [prefixWord, tailWord_2092428, baseEnd_2092428] using wordTrace_append hprefix tailTrace_2092428
  have hstable : (prefixWord ++ tailWord_2092428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092428).length < 2 ^ (prefixWord ++ tailWord_2092428).sum := by decide
  have hdescent : baseEnd_2092428 < baseStart_2092428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092442 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_2092442 : Nat := 118140960795 + 2092442 * 2 ^ 59
def prefixEnd_2092442 : Nat := 4983230072969 + 3 ^ 40 * 2092442 * 2
def baseEnd_2092442 : Nat := 477523772291203353223129

theorem tailTrace_2092442 : CollatzResearch.WordTrace tailWord_2092442 prefixEnd_2092442 477523772291203353223129 := by
  unfold tailWord_2092442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079407371361867371943895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50878419656964979658517053 19079407371361867371943895)
  ·
    refine ⟨28619111057042801057915843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19079407371361867371943895 28619111057042801057915843)
    ·
      refine ⟨42928666585564201586873765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28619111057042801057915843 42928666585564201586873765)
      ·
        refine ⟨8049124984793287797538831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42928666585564201586873765 8049124984793287797538831)
        ·
          refine ⟨12073687477189931696308247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049124984793287797538831 12073687477189931696308247)
          ·
            refine ⟨18110531215784897544462371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12073687477189931696308247 18110531215784897544462371)
            ·
              refine ⟨27165796823677346316693557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18110531215784897544462371 27165796823677346316693557)
              ·
                refine ⟨2546793452219751217190021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27165796823677346316693557 2546793452219751217190021)
                ·
                  refine ⟨477523772291203353223129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546793452219751217190021 477523772291203353223129)
                  ·
                    rfl

theorem cell21_2092442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_2092442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092442 prefixEnd_2092442 := by exact prefixLift 2092442
  have htrace : WordTrace (prefixWord ++ tailWord_2092442) baseStart_2092442 baseEnd_2092442 := by
    simpa [prefixWord, tailWord_2092442, baseEnd_2092442] using wordTrace_append hprefix tailTrace_2092442
  have hstable : (prefixWord ++ tailWord_2092442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092442).length < 2 ^ (prefixWord ++ tailWord_2092442).sum := by decide
  have hdescent : baseEnd_2092442 < baseStart_2092442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092476 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2092476 : Nat := 118140960795 + 2092476 * 2 ^ 59
def prefixEnd_2092476 : Nat := 4983230072969 + 3 ^ 40 * 2092476 * 2
def baseEnd_2092476 : Nat := 477531531554426849656393

theorem tailTrace_2092476 : CollatzResearch.WordTrace tailWord_2092476 prefixEnd_2092476 477531531554426849656393 := by
  unfold tailWord_2092476
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159434783662146647256641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50879246378216195529675521 38159434783662146647256641)
  ·
    refine ⟨28619576087746609985442481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38159434783662146647256641 28619576087746609985442481)
    ·
      refine ⟨21464682065809957489081861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28619576087746609985442481 21464682065809957489081861)
      ·
        refine ⟨4024627887339367029202849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21464682065809957489081861 4024627887339367029202849)
        ·
          refine ⟨3018470915504525271902137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4024627887339367029202849 3018470915504525271902137)
          ·
            refine ⟨2263853186628393953926603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018470915504525271902137 2263853186628393953926603)
            ·
              refine ⟨3395779779942590930889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263853186628393953926603 3395779779942590930889905)
              ·
                refine ⟨2546834834956943198167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395779779942590930889905 2546834834956943198167429)
                ·
                  refine ⟨477531531554426849656393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546834834956943198167429 477531531554426849656393)
                  ·
                    rfl

theorem cell21_2092476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2092476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092476 prefixEnd_2092476 := by exact prefixLift 2092476
  have htrace : WordTrace (prefixWord ++ tailWord_2092476) baseStart_2092476 baseEnd_2092476 := by
    simpa [prefixWord, tailWord_2092476, baseEnd_2092476] using wordTrace_append hprefix tailTrace_2092476
  have hstable : (prefixWord ++ tailWord_2092476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092476).length < 2 ^ (prefixWord ++ tailWord_2092476).sum := by decide
  have hdescent : baseEnd_2092476 < baseStart_2092476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092487 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_2092487 : Nat := 118140960795 + 2092487 * 2 ^ 59
def prefixEnd_2092487 : Nat := 4983230072969 + 3 ^ 40 * 2092487 * 2
def baseEnd_2092487 : Nat := 477534041904293274973037

theorem tailTrace_2092487 : CollatzResearch.WordTrace tailWord_2092487 prefixEnd_2092487 477534041904293274973037 := by
  unfold tailWord_2092487
  simp only [CollatzResearch.WordTrace]
  refine ⟨76319270770284442173163715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50879513846856294782109143 76319270770284442173163715)
  ·
    refine ⟨114478906155426663259745573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76319270770284442173163715 114478906155426663259745573)
    ·
      refine ⟨21464794904142499361202295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114478906155426663259745573 21464794904142499361202295)
      ·
        refine ⟨32197192356213749041803443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21464794904142499361202295 32197192356213749041803443)
        ·
          refine ⟨48295788534320623562705165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32197192356213749041803443 48295788534320623562705165)
          ·
            refine ⟨18110920700370233836014437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48295788534320623562705165 18110920700370233836014437)
            ·
              refine ⟨3395797631319418844252707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18110920700370233836014437 3395797631319418844252707)
              ·
                refine ⟨5093696446979128266379061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395797631319418844252707 5093696446979128266379061)
                ·
                  refine ⟨477534041904293274973037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093696446979128266379061 477534041904293274973037)
                  ·
                    rfl

theorem cell21_2092487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_2092487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092487 prefixEnd_2092487 := by exact prefixLift 2092487
  have htrace : WordTrace (prefixWord ++ tailWord_2092487) baseStart_2092487 baseEnd_2092487 := by
    simpa [prefixWord, tailWord_2092487, baseEnd_2092487] using wordTrace_append hprefix tailTrace_2092487
  have hstable : (prefixWord ++ tailWord_2092487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092487).length < 2 ^ (prefixWord ++ tailWord_2092487).sum := by decide
  have hdescent : baseEnd_2092487 < baseStart_2092487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092597 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 3]
def baseStart_2092597 : Nat := 118140960795 + 2092597 * 2 ^ 59
def prefixEnd_2092597 : Nat := 4983230072969 + 3 ^ 40 * 2092597 * 2
def baseEnd_2092597 : Nat := 477559145402957528139479

theorem tailTrace_2092597 : CollatzResearch.WordTrace tailWord_2092597 prefixEnd_2092597 477559145402957528139479 := by
  unfold tailWord_2092597
  simp only [CollatzResearch.WordTrace]
  refine ⟨76323282799885930959668045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50882188533257287306445363 76323282799885930959668045)
  ·
    refine ⟨28621231049957224109875517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76323282799885930959668045 28621231049957224109875517)
    ·
      refine ⟨10732961643733959041203319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28621231049957224109875517 10732961643733959041203319)
      ·
        refine ⟨16099442465600938561804979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732961643733959041203319 16099442465600938561804979)
        ·
          refine ⟨24149163698401407842707469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16099442465600938561804979 24149163698401407842707469)
          ·
            refine ⟨9055936386900527941015301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24149163698401407842707469 9055936386900527941015301)
            ·
              refine ⟨1697988072543848988940369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9055936386900527941015301 1697988072543848988940369)
              ·
                refine ⟨1273491054407886741705277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1697988072543848988940369 1273491054407886741705277)
                ·
                  refine ⟨477559145402957528139479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273491054407886741705277 477559145402957528139479)
                  ·
                    rfl

theorem cell21_2092597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_2092597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092597 prefixEnd_2092597 := by exact prefixLift 2092597
  have htrace : WordTrace (prefixWord ++ tailWord_2092597) baseStart_2092597 baseEnd_2092597 := by
    simpa [prefixWord, tailWord_2092597, baseEnd_2092597] using wordTrace_append hprefix tailTrace_2092597
  have hstable : (prefixWord ++ tailWord_2092597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092597).length < 2 ^ (prefixWord ++ tailWord_2092597).sum := by decide
  have hdescent : baseEnd_2092597 < baseStart_2092597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092656 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_2092656 : Nat := 118140960795 + 2092656 * 2 ^ 59
def prefixEnd_2092656 : Nat := 4983230072969 + 3 ^ 40 * 2092656 * 2
def baseEnd_2092656 : Nat := 477572610006786536656025

theorem tailTrace_2092656 : CollatzResearch.WordTrace tailWord_2092656 prefixEnd_2092656 477572610006786536656025 := by
  unfold tailWord_2092656
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162717353336092018032911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50883623137781456024043881 38162717353336092018032911)
  ·
    refine ⟨57244076030004138027049367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38162717353336092018032911 57244076030004138027049367)
    ·
      refine ⟨85866114045006207040574051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57244076030004138027049367 85866114045006207040574051)
      ·
        refine ⟨128799171067509310560861077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85866114045006207040574051 128799171067509310560861077)
        ·
          refine ⟨6037461143789498932540363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128799171067509310560861077 6037461143789498932540363)
          ·
            refine ⟨9056191715684248398810545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037461143789498932540363 9056191715684248398810545)
            ·
              refine ⟨6792143786763186299107909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056191715684248398810545 6792143786763186299107909)
              ·
                refine ⟨1273526960018097431082733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6792143786763186299107909 1273526960018097431082733)
                ·
                  refine ⟨477572610006786536656025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273526960018097431082733 477572610006786536656025)
                  ·
                    rfl

theorem cell21_2092656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_2092656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092656 prefixEnd_2092656 := by exact prefixLift 2092656
  have htrace : WordTrace (prefixWord ++ tailWord_2092656) baseStart_2092656 baseEnd_2092656 := by
    simpa [prefixWord, tailWord_2092656, baseEnd_2092656] using wordTrace_append hprefix tailTrace_2092656
  have hstable : (prefixWord ++ tailWord_2092656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092656).length < 2 ^ (prefixWord ++ tailWord_2092656).sum := by decide
  have hdescent : baseEnd_2092656 < baseStart_2092656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092667 : List Nat := [1, 1, 1, 1, 1, 4, 4, 8]
def baseStart_2092667 : Nat := 118140960795 + 2092667 * 2 ^ 59
def prefixEnd_2092667 : Nat := 4983230072969 + 3 ^ 40 * 2092667 * 2
def baseEnd_2092667 : Nat := 159191706785550987324223

theorem tailTrace_2092667 : CollatzResearch.WordTrace tailWord_2092667 prefixEnd_2092667 159191706785550987324223 := by
  unfold tailWord_2092667
  simp only [CollatzResearch.WordTrace]
  refine ⟨76325835909632332914716255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50883890606421555276477503 76325835909632332914716255)
  ·
    refine ⟨114488753864448499372074383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76325835909632332914716255 114488753864448499372074383)
    ·
      refine ⟨171733130796672749058111575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114488753864448499372074383 171733130796672749058111575)
      ·
        refine ⟨257599696195009123587167363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171733130796672749058111575 257599696195009123587167363)
        ·
          refine ⟨386399544292513685380751045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257599696195009123587167363 386399544292513685380751045)
          ·
            refine ⟨72449914554846316008890821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386399544292513685380751045 72449914554846316008890821)
            ·
              refine ⟨13584358979033684251667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72449914554846316008890821 13584358979033684251667029)
              ·
                refine ⟨159191706785550987324223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13584358979033684251667029 159191706785550987324223)
                ·
                  rfl

theorem cell21_2092667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_2092667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092667 prefixEnd_2092667 := by exact prefixLift 2092667
  have htrace : WordTrace (prefixWord ++ tailWord_2092667) baseStart_2092667 baseEnd_2092667 := by
    simpa [prefixWord, tailWord_2092667, baseEnd_2092667] using wordTrace_append hprefix tailTrace_2092667
  have hstable : (prefixWord ++ tailWord_2092667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092667).length < 2 ^ (prefixWord ++ tailWord_2092667).sum := by decide
  have hdescent : baseEnd_2092667 < baseStart_2092667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092690 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2092690 : Nat := 118140960795 + 2092690 * 2 ^ 59
def prefixEnd_2092690 : Nat := 4983230072969 + 3 ^ 40 * 2092690 * 2
def baseEnd_2092690 : Nat := 477580369270010033089289

theorem tailTrace_2092690 : CollatzResearch.WordTrace tailWord_2092690 prefixEnd_2092690 477580369270010033089289 := by
  unfold tailWord_2092690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081668697137251960700881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50884449859032671895202349 19081668697137251960700881)
  ·
    refine ⟨14311251522852938970525661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19081668697137251960700881 14311251522852938970525661)
    ·
      refine ⟨5366719321069852113947123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14311251522852938970525661 5366719321069852113947123)
      ·
        refine ⟨8050078981604778170920685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366719321069852113947123 8050078981604778170920685)
        ·
          refine ⟨3018779618101791814095257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8050078981604778170920685 3018779618101791814095257)
          ·
            refine ⟨2264084713576343860571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018779618101791814095257 2264084713576343860571443)
            ·
              refine ⟨3396127070364515790857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264084713576343860571443 3396127070364515790857165)
              ·
                refine ⟨1273547651386693421571437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396127070364515790857165 1273547651386693421571437)
                ·
                  refine ⟨477580369270010033089289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273547651386693421571437 477580369270010033089289)
                  ·
                    rfl

theorem cell21_2092690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2092690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092690 prefixEnd_2092690 := by exact prefixLift 2092690
  have htrace : WordTrace (prefixWord ++ tailWord_2092690) baseStart_2092690 baseEnd_2092690 := by
    simpa [prefixWord, tailWord_2092690, baseEnd_2092690] using wordTrace_append hprefix tailTrace_2092690
  have hstable : (prefixWord ++ tailWord_2092690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092690).length < 2 ^ (prefixWord ++ tailWord_2092690).sum := by decide
  have hdescent : baseEnd_2092690 < baseStart_2092690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092718 : List Nat := [4, 1, 4, 1, 2, 1, 2, 6]
def baseStart_2092718 : Nat := 118140960795 + 2092718 * 2 ^ 59
def prefixEnd_2092718 : Nat := 4983230072969 + 3 ^ 40 * 2092718 * 2
def baseEnd_2092718 : Nat := 159195586417162735540855

theorem tailTrace_2092718 : CollatzResearch.WordTrace tailWord_2092718 prefixEnd_2092718 159195586417162735540855 := by
  unfold tailWord_2092718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540962004055946078102851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50885130688298379083215205 9540962004055946078102851)
  ·
    refine ⟨14311443006083919117154277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9540962004055946078102851 14311443006083919117154277)
    ·
      refine ⟨2683395563640734834466427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14311443006083919117154277 2683395563640734834466427)
      ·
        refine ⟨4025093345461102251699641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2683395563640734834466427 4025093345461102251699641)
        ·
          refine ⟨3018820009095826688774731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025093345461102251699641 3018820009095826688774731)
          ·
            refine ⟨4528230013643740033162097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018820009095826688774731 4528230013643740033162097)
            ·
              refine ⟨3396172510232805024871573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528230013643740033162097 3396172510232805024871573)
              ·
                refine ⟨159195586417162735540855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3396172510232805024871573 159195586417162735540855)
                ·
                  rfl

theorem cell21_2092718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_2092718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092718 prefixEnd_2092718 := by exact prefixLift 2092718
  have htrace : WordTrace (prefixWord ++ tailWord_2092718) baseStart_2092718 baseEnd_2092718 := by
    simpa [prefixWord, tailWord_2092718, baseEnd_2092718] using wordTrace_append hprefix tailTrace_2092718
  have hstable : (prefixWord ++ tailWord_2092718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092718).length < 2 ^ (prefixWord ++ tailWord_2092718).sum := by decide
  have hdescent : baseEnd_2092718 < baseStart_2092718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092743 : List Nat := [1, 1, 4, 1, 1, 1, 3, 9]
def baseStart_2092743 : Nat := 118140960795 + 2092743 * 2 ^ 59
def prefixEnd_2092743 : Nat := 4983230072969 + 3 ^ 40 * 2092743 * 2
def baseEnd_2092743 : Nat := 159197488197364572901949

theorem tailTrace_2092743 : CollatzResearch.WordTrace tailWord_2092743 prefixEnd_2092743 159197488197364572901949 := by
  unfold tailWord_2092743
  simp only [CollatzResearch.WordTrace]
  refine ⟨76328607857356997894482883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50885738571571331929655255 76328607857356997894482883)
  ·
    refine ⟨114492911786035496841724325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76328607857356997894482883 114492911786035496841724325)
    ·
      refine ⟨21467420959881655657823311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114492911786035496841724325 21467420959881655657823311)
      ·
        refine ⟨32201131439822483486734967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21467420959881655657823311 32201131439822483486734967)
        ·
          refine ⟨48301697159733725230102451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32201131439822483486734967 48301697159733725230102451)
          ·
            refine ⟨72452545739600587845153677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48301697159733725230102451 72452545739600587845153677)
            ·
              refine ⟨27169704652350220441932629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72452545739600587845153677 27169704652350220441932629)
              ·
                refine ⟨159197488197364572901949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27169704652350220441932629 159197488197364572901949)
                ·
                  rfl

theorem cell21_2092743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_2092743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092743 prefixEnd_2092743 := by exact prefixLift 2092743
  have htrace : WordTrace (prefixWord ++ tailWord_2092743) baseStart_2092743 baseEnd_2092743 := by
    simpa [prefixWord, tailWord_2092743, baseEnd_2092743] using wordTrace_append hprefix tailTrace_2092743
  have hstable : (prefixWord ++ tailWord_2092743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092743).length < 2 ^ (prefixWord ++ tailWord_2092743).sum := by decide
  have hdescent : baseEnd_2092743 < baseStart_2092743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092808 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_2092808 : Nat := 118140960795 + 2092808 * 2 ^ 59
def prefixEnd_2092808 : Nat := 4983230072969 + 3 ^ 40 * 2092808 * 2
def baseEnd_2092808 : Nat := 477607298477668050122381

theorem tailTrace_2092808 : CollatzResearch.WordTrace tailWord_2092808 prefixEnd_2092808 477607298477668050122381 := by
  unfold tailWord_2092808
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165489301060756997799539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50887319068081009330399385 38165489301060756997799539)
  ·
    refine ⟨57248233951591135496699309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38165489301060756997799539 57248233951591135496699309)
    ·
      refine ⟨21468087731846675811262241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57248233951591135496699309 21468087731846675811262241)
      ·
        refine ⟨16101065798885006858446681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21468087731846675811262241 16101065798885006858446681)
        ·
          refine ⟨12075799349163755143835011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16101065798885006858446681 12075799349163755143835011)
          ·
            refine ⟨18113699023745632715752517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075799349163755143835011 18113699023745632715752517)
            ·
              refine ⟨3396318566952306134203597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18113699023745632715752517 3396318566952306134203597)
              ·
                refine ⟨1273619462607114800326349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396318566952306134203597 1273619462607114800326349)
                ·
                  refine ⟨477607298477668050122381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273619462607114800326349 477607298477668050122381)
                  ·
                    rfl

theorem cell21_2092808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_2092808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092808 prefixEnd_2092808 := by exact prefixLift 2092808
  have htrace : WordTrace (prefixWord ++ tailWord_2092808) baseStart_2092808 baseEnd_2092808 := by
    simpa [prefixWord, tailWord_2092808, baseEnd_2092808] using wordTrace_append hprefix tailTrace_2092808
  have hstable : (prefixWord ++ tailWord_2092808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092808).length < 2 ^ (prefixWord ++ tailWord_2092808).sum := by decide
  have hdescent : baseEnd_2092808 < baseStart_2092808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092870 : List Nat := [6, 1, 1, 2, 1, 3, 7]
def baseStart_2092870 : Nat := 118140960795 + 2092870 * 2 ^ 59
def prefixEnd_2092870 : Nat := 4983230072969 + 3 ^ 40 * 2092870 * 2
def baseEnd_2092870 : Nat := 53069049746929968898769

theorem tailTrace_2092870 : CollatzResearch.WordTrace tailWord_2092870 prefixEnd_2092870 53069049746929968898769 := by
  unfold tailWord_2092870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385413747746778080761127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50888826618597932389570709 2385413747746778080761127)
  ·
    refine ⟨3578120621620167121141691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385413747746778080761127 3578120621620167121141691)
    ·
      refine ⟨5367180932430250681712537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578120621620167121141691 5367180932430250681712537)
      ·
        refine ⟨4025385699322688011284403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367180932430250681712537 4025385699322688011284403)
        ·
          refine ⟨6038078548984032016926605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025385699322688011284403 6038078548984032016926605)
          ·
            refine ⟨2264279455869012006347477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038078548984032016926605 2264279455869012006347477)
            ·
              refine ⟨53069049746929968898769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2264279455869012006347477 53069049746929968898769)
              ·
                rfl

theorem cell21_2092870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 7].length) (baseStart_2092870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092870 prefixEnd_2092870 := by exact prefixLift 2092870
  have htrace : WordTrace (prefixWord ++ tailWord_2092870) baseStart_2092870 baseEnd_2092870 := by
    simpa [prefixWord, tailWord_2092870, baseEnd_2092870] using wordTrace_append hprefix tailTrace_2092870
  have hstable : (prefixWord ++ tailWord_2092870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092870).length < 2 ^ (prefixWord ++ tailWord_2092870).sum := by decide
  have hdescent : baseEnd_2092870 < baseStart_2092870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092881 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2092881 : Nat := 118140960795 + 2092881 * 2 ^ 59
def prefixEnd_2092881 : Nat := 4983230072969 + 3 ^ 40 * 2092881 * 2
def baseEnd_2092881 : Nat := 477623958072236145405565

theorem tailTrace_2092881 : CollatzResearch.WordTrace tailWord_2092881 prefixEnd_2092881 477623958072236145405565 := by
  unfold tailWord_2092881
  simp only [CollatzResearch.WordTrace]
  refine ⟨76333641130857047463006497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50889094087238031642004331 76333641130857047463006497)
  ·
    refine ⟨57250230848142785597254873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76333641130857047463006497 57250230848142785597254873)
    ·
      refine ⟨42937673136107089197941155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57250230848142785597254873 42937673136107089197941155)
      ·
        refine ⟨64406509704160633796911733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42937673136107089197941155 64406509704160633796911733)
        ·
          refine ⟨6038110284765059418460475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64406509704160633796911733 6038110284765059418460475)
          ·
            refine ⟨9057165427147589127690713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038110284765059418460475 9057165427147589127690713)
            ·
              refine ⟨6792874070360691845768035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057165427147589127690713 6792874070360691845768035)
              ·
                refine ⟨10189311105541037768652053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792874070360691845768035 10189311105541037768652053)
                ·
                  refine ⟨477623958072236145405565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10189311105541037768652053 477623958072236145405565)
                  ·
                    rfl

theorem cell21_2092881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2092881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092881 prefixEnd_2092881 := by exact prefixLift 2092881
  have htrace : WordTrace (prefixWord ++ tailWord_2092881) baseStart_2092881 baseEnd_2092881 := by
    simpa [prefixWord, tailWord_2092881, baseEnd_2092881] using wordTrace_append hprefix tailTrace_2092881
  have hstable : (prefixWord ++ tailWord_2092881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092881).length < 2 ^ (prefixWord ++ tailWord_2092881).sum := by decide
  have hdescent : baseEnd_2092881 < baseStart_2092881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092884 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2092884 : Nat := 118140960795 + 2092884 * 2 ^ 59
def prefixEnd_2092884 : Nat := 4983230072969 + 3 ^ 40 * 2092884 * 2
def baseEnd_2092884 : Nat := 477624642713108806855559

theorem tailTrace_2092884 : CollatzResearch.WordTrace tailWord_2092884 prefixEnd_2092884 477624642713108806855559 := by
  unfold tailWord_2092884
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166875274923089487682853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50889167033230785983577137 38166875274923089487682853)
  ·
    refine ⟨7156289114048079278940535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38166875274923089487682853 7156289114048079278940535)
    ·
      refine ⟨10734433671072118918410803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156289114048079278940535 10734433671072118918410803)
      ·
        refine ⟨16101650506608178377616205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734433671072118918410803 16101650506608178377616205)
        ·
          refine ⟨6038118939978066891606077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16101650506608178377616205 6038118939978066891606077)
          ·
            refine ⟨2264294602491775084352279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038118939978066891606077 2264294602491775084352279)
            ·
              refine ⟨3396441903737662626528419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264294602491775084352279 3396441903737662626528419)
              ·
                refine ⟨5094662855606493939792629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396441903737662626528419 5094662855606493939792629)
                ·
                  refine ⟨477624642713108806855559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5094662855606493939792629 477624642713108806855559)
                  ·
                    rfl

theorem cell21_2092884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2092884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092884 prefixEnd_2092884 := by exact prefixLift 2092884
  have htrace : WordTrace (prefixWord ++ tailWord_2092884) baseStart_2092884 baseEnd_2092884 := by
    simpa [prefixWord, tailWord_2092884, baseEnd_2092884] using wordTrace_append hprefix tailTrace_2092884
  have hstable : (prefixWord ++ tailWord_2092884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092884).length < 2 ^ (prefixWord ++ tailWord_2092884).sum := by decide
  have hdescent : baseEnd_2092884 < baseStart_2092884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092895 : List Nat := [1, 1, 2, 3, 1, 4, 1, 8]
def baseStart_2092895 : Nat := 118140960795 + 2092895 * 2 ^ 59
def prefixEnd_2092895 : Nat := 4983230072969 + 3 ^ 40 * 2092895 * 2
def baseEnd_2092895 : Nat := 159209051020991744057401

theorem tailTrace_2092895 : CollatzResearch.WordTrace tailWord_2092895 prefixEnd_2092895 159209051020991744057401 := by
  unfold tailWord_2092895
  simp only [CollatzResearch.WordTrace]
  refine ⟨76334151752806327854016139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50889434501870885236010759 76334151752806327854016139)
  ·
    refine ⟨114501227629209491781024209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76334151752806327854016139 114501227629209491781024209)
    ·
      refine ⟨85875920721907118835768157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114501227629209491781024209 85875920721907118835768157)
      ·
        refine ⟨32203470270715169563413059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85875920721907118835768157 32203470270715169563413059)
        ·
          refine ⟨48305205406072754345119589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32203470270715169563413059 48305205406072754345119589)
          ·
            refine ⟨9057226013638641439709923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48305205406072754345119589 9057226013638641439709923)
            ·
              refine ⟨13585839020457962159564885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057226013638641439709923 13585839020457962159564885)
              ·
                refine ⟨159209051020991744057401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13585839020457962159564885 159209051020991744057401)
                ·
                  rfl

theorem cell21_2092895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_2092895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092895 prefixEnd_2092895 := by exact prefixLift 2092895
  have htrace : WordTrace (prefixWord ++ tailWord_2092895) baseStart_2092895 baseEnd_2092895 := by
    simpa [prefixWord, tailWord_2092895, baseEnd_2092895] using wordTrace_append hprefix tailTrace_2092895
  have hstable : (prefixWord ++ tailWord_2092895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092895).length < 2 ^ (prefixWord ++ tailWord_2092895).sum := by decide
  have hdescent : baseEnd_2092895 < baseStart_2092895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2092929 : List Nat := [1, 2, 4, 4, 2, 8]
def baseStart_2092929 : Nat := 118140960795 + 2092929 * 2 ^ 59
def prefixEnd_2092929 : Nat := 4983230072969 + 3 ^ 40 * 2092929 * 2
def baseEnd_2092929 : Nat := 17690181938007360318721

theorem tailTrace_2092929 : CollatzResearch.WordTrace tailWord_2092929 prefixEnd_2092929 17690181938007360318721 := by
  unfold tailWord_2092929
  simp only [CollatzResearch.WordTrace]
  refine ⟨76335391834683151660753841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50890261223122101107169227 76335391834683151660753841)
  ·
    refine ⟨57251543876012363745565381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76335391834683151660753841 57251543876012363745565381)
    ·
      refine ⟨10734664476752318202293509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57251543876012363745565381 10734664476752318202293509)
      ·
        refine ⟨2012749589391059662930033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10734664476752318202293509 2012749589391059662930033)
        ·
          refine ⟨1509562192043294747197525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2012749589391059662930033 1509562192043294747197525)
          ·
            refine ⟨17690181938007360318721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1509562192043294747197525 17690181938007360318721)
            ·
              rfl

theorem cell21_2092929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 8].length) (baseStart_2092929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2092929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2092929 prefixEnd_2092929 := by exact prefixLift 2092929
  have htrace : WordTrace (prefixWord ++ tailWord_2092929) baseStart_2092929 baseEnd_2092929 := by
    simpa [prefixWord, tailWord_2092929, baseEnd_2092929] using wordTrace_append hprefix tailTrace_2092929
  have hstable : (prefixWord ++ tailWord_2092929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2092929).length < 2 ^ (prefixWord ++ tailWord_2092929).sum := by decide
  have hdescent : baseEnd_2092929 < baseStart_2092929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2092929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093002 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_2093002 : Nat := 118140960795 + 2093002 * 2 ^ 59
def prefixEnd_2093002 : Nat := 4983230072969 + 3 ^ 40 * 2093002 * 2
def baseEnd_2093002 : Nat := 477651571920766823888651

theorem tailTrace_2093002 : CollatzResearch.WordTrace tailWord_2093002 prefixEnd_2093002 477651571920766823888651 := by
  unfold tailWord_2093002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084513590854671282040315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50892036242279123418774173 19084513590854671282040315)
  ·
    refine ⟨28626770386282006923060473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19084513590854671282040315 28626770386282006923060473)
    ·
      refine ⟨21470077789711505192295355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28626770386282006923060473 21470077789711505192295355)
      ·
        refine ⟨32205116684567257788443033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21470077789711505192295355 32205116684567257788443033)
        ·
          refine ⟨24153837513425443341332275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32205116684567257788443033 24153837513425443341332275)
          ·
            refine ⟨36230756270138165011998413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153837513425443341332275 36230756270138165011998413)
            ·
              refine ⟨13586533601301811879499405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36230756270138165011998413 13586533601301811879499405)
              ·
                refine ⟨5094950100488179454812277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13586533601301811879499405 5094950100488179454812277)
                ·
                  refine ⟨477651571920766823888651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5094950100488179454812277 477651571920766823888651)
                  ·
                    rfl

theorem cell21_2093002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_2093002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093002 prefixEnd_2093002 := by exact prefixLift 2093002
  have htrace : WordTrace (prefixWord ++ tailWord_2093002) baseStart_2093002 baseEnd_2093002 := by
    simpa [prefixWord, tailWord_2093002, baseEnd_2093002] using wordTrace_append hprefix tailTrace_2093002
  have hstable : (prefixWord ++ tailWord_2093002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093002).length < 2 ^ (prefixWord ++ tailWord_2093002).sum := by decide
  have hdescent : baseEnd_2093002 < baseStart_2093002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093109 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2093109 : Nat := 118140960795 + 2093109 * 2 ^ 59
def prefixEnd_2093109 : Nat := 4983230072969 + 3 ^ 40 * 2093109 * 2
def baseEnd_2093109 : Nat := 477675990778558415605099

theorem tailTrace_2093109 : CollatzResearch.WordTrace tailWord_2093109 prefixEnd_2093109 477675990778558415605099 := by
  unfold tailWord_2093109
  simp only [CollatzResearch.WordTrace]
  refine ⟨76341956974031042402306381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50894637982687361601537587 76341956974031042402306381)
  ·
    refine ⟨28628233865261640900864893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76341956974031042402306381 28628233865261640900864893)
    ·
      refine ⟨10735587699473115337824335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28628233865261640900864893 10735587699473115337824335)
      ·
        refine ⟨16103381549209673006736503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10735587699473115337824335 16103381549209673006736503)
        ·
          refine ⟨24155072323814509510104755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16103381549209673006736503 24155072323814509510104755)
          ·
            refine ⟨36232608485721764265157133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24155072323814509510104755 36232608485721764265157133)
            ·
              refine ⟨13587228182145661599433925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36232608485721764265157133 13587228182145661599433925)
              ·
                refine ⟨2547605284152311549893861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13587228182145661599433925 2547605284152311549893861)
                ·
                  refine ⟨477675990778558415605099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547605284152311549893861 477675990778558415605099)
                  ·
                    rfl

theorem cell21_2093109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2093109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093109 prefixEnd_2093109 := by exact prefixLift 2093109
  have htrace : WordTrace (prefixWord ++ tailWord_2093109) baseStart_2093109 baseEnd_2093109 := by
    simpa [prefixWord, tailWord_2093109, baseEnd_2093109] using wordTrace_append hprefix tailTrace_2093109
  have hstable : (prefixWord ++ tailWord_2093109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093109).length < 2 ^ (prefixWord ++ tailWord_2093109).sum := by decide
  have hdescent : baseEnd_2093109 < baseStart_2093109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093112 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_2093112 : Nat := 118140960795 + 2093112 * 2 ^ 59
def prefixEnd_2093112 : Nat := 4983230072969 + 3 ^ 40 * 2093112 * 2
def baseEnd_2093112 : Nat := 477676675419431077055093

theorem tailTrace_2093112 : CollatzResearch.WordTrace tailWord_2093112 prefixEnd_2093112 477676675419431077055093 := by
  unfold tailWord_2093112
  simp only [CollatzResearch.WordTrace]
  refine ⟨38171033196510086957332795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50894710928680115943110393 38171033196510086957332795)
  ·
    refine ⟨57256549794765130435999193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38171033196510086957332795 57256549794765130435999193)
    ·
      refine ⟨42942412346073847826999395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57256549794765130435999193 42942412346073847826999395)
      ·
        refine ⟨64413618519110771740499093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42942412346073847826999395 64413618519110771740499093)
        ·
          refine ⟨3019388368083317425335895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64413618519110771740499093 3019388368083317425335895)
          ·
            refine ⟨4529082552124976138003843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019388368083317425335895 4529082552124976138003843)
            ·
              refine ⟨6793623828187464207005765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529082552124976138003843 6793623828187464207005765)
              ·
                refine ⟨1273804467785149538813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6793623828187464207005765 1273804467785149538813581)
                ·
                  refine ⟨477676675419431077055093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273804467785149538813581 477676675419431077055093)
                  ·
                    rfl

theorem cell21_2093112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_2093112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093112 prefixEnd_2093112 := by exact prefixLift 2093112
  have htrace : WordTrace (prefixWord ++ tailWord_2093112) baseStart_2093112 baseEnd_2093112 := by
    simpa [prefixWord, tailWord_2093112, baseEnd_2093112] using wordTrace_append hprefix tailTrace_2093112
  have hstable : (prefixWord ++ tailWord_2093112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093112).length < 2 ^ (prefixWord ++ tailWord_2093112).sum := by decide
  have hdescent : baseEnd_2093112 < baseStart_2093112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093306 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_2093306 : Nat := 118140960795 + 2093306 * 2 ^ 59
def prefixEnd_2093306 : Nat := 4983230072969 + 3 ^ 40 * 2093306 * 2
def baseEnd_2093306 : Nat := 477720948862529850821363

theorem tailTrace_2093306 : CollatzResearch.WordTrace tailWord_2093306 prefixEnd_2093306 477720948862529850821363 := by
  unfold tailWord_2093306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087285538579336261806943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50899428102878230031485181 19087285538579336261806943)
  ·
    refine ⟨28630928307869004392710415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19087285538579336261806943 28630928307869004392710415)
    ·
      refine ⟨42946392461803506589065623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28630928307869004392710415 42946392461803506589065623)
      ·
        refine ⟨64419588692705259883598435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42946392461803506589065623 64419588692705259883598435)
        ·
          refine ⟨96629383039057889825397653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64419588692705259883598435 96629383039057889825397653)
          ·
            refine ⟨4529502329955838585565515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96629383039057889825397653 4529502329955838585565515)
            ·
              refine ⟨6794253494933757878348273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529502329955838585565515 6794253494933757878348273)
              ·
                refine ⟨5095690121200318408761205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794253494933757878348273 5095690121200318408761205)
                ·
                  refine ⟨477720948862529850821363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5095690121200318408761205 477720948862529850821363)
                  ·
                    rfl

theorem cell21_2093306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_2093306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093306 prefixEnd_2093306 := by exact prefixLift 2093306
  have htrace : WordTrace (prefixWord ++ tailWord_2093306) baseStart_2093306 baseEnd_2093306 := by
    simpa [prefixWord, tailWord_2093306, baseEnd_2093306] using wordTrace_append hprefix tailTrace_2093306
  have hstable : (prefixWord ++ tailWord_2093306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093306).length < 2 ^ (prefixWord ++ tailWord_2093306).sum := by decide
  have hdescent : baseEnd_2093306 < baseStart_2093306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093323 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 3]
def baseStart_2093323 : Nat := 118140960795 + 2093323 * 2 ^ 59
def prefixEnd_2093323 : Nat := 4983230072969 + 3 ^ 40 * 2093323 * 2
def baseEnd_2093323 : Nat := 477724828494141599037995

theorem tailTrace_2093323 : CollatzResearch.WordTrace tailWord_2093323 prefixEnd_2093323 477724828494141599037995 := by
  unfold tailWord_2093323
  simp only [CollatzResearch.WordTrace]
  refine ⟨76349762195255756950596623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50899841463503837967064415 76349762195255756950596623)
  ·
    refine ⟨114524643292883635425894935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76349762195255756950596623 114524643292883635425894935)
    ·
      refine ⟨171786964939325453138842403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114524643292883635425894935 171786964939325453138842403)
      ·
        refine ⟨257680447408988179708263605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171786964939325453138842403 257680447408988179708263605)
        ·
          refine ⟨24157541944592641847649713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257680447408988179708263605 24157541944592641847649713)
          ·
            refine ⟨18118156458444481385737285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24157541944592641847649713 18118156458444481385737285)
            ·
              refine ⟨3397154335958340259825741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18118156458444481385737285 3397154335958340259825741)
              ·
                refine ⟨1273932875984377597434653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3397154335958340259825741 1273932875984377597434653)
                ·
                  refine ⟨477724828494141599037995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273932875984377597434653 477724828494141599037995)
                  ·
                    rfl

theorem cell21_2093323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].length) (baseStart_2093323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093323 prefixEnd_2093323 := by exact prefixLift 2093323
  have htrace : WordTrace (prefixWord ++ tailWord_2093323) baseStart_2093323 baseEnd_2093323 := by
    simpa [prefixWord, tailWord_2093323, baseEnd_2093323] using wordTrace_append hprefix tailTrace_2093323
  have hstable : (prefixWord ++ tailWord_2093323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093323).length < 2 ^ (prefixWord ++ tailWord_2093323).sum := by decide
  have hdescent : baseEnd_2093323 < baseStart_2093323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093413 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_2093413 : Nat := 118140960795 + 2093413 * 2 ^ 59
def prefixEnd_2093413 : Nat := 4983230072969 + 3 ^ 40 * 2093413 * 2
def baseEnd_2093413 : Nat := 477745367720321442537811

theorem tailTrace_2093413 : CollatzResearch.WordTrace tailWord_2093413 prefixEnd_2093413 477745367720321442537811 := by
  unfold tailWord_2093413
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353044764929702321372893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50902029843286468214248595 76353044764929702321372893)
  ·
    refine ⟨28632391786848638370514835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76353044764929702321372893 28632391786848638370514835)
    ·
      refine ⟨42948587680272957555772253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632391786848638370514835 42948587680272957555772253)
      ·
        refine ⟨16105720380102359083414595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42948587680272957555772253 16105720380102359083414595)
        ·
          refine ⟨24158580570153538625121893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105720380102359083414595 24158580570153538625121893)
          ·
            refine ⟨4529733856903788492210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24158580570153538625121893 4529733856903788492210355)
            ·
              refine ⟨6794600785355682738315533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529733856903788492210355 6794600785355682738315533)
              ·
                refine ⟨2547975294508381026868325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6794600785355682738315533 2547975294508381026868325)
                ·
                  refine ⟨477745367720321442537811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547975294508381026868325 477745367720321442537811)
                  ·
                    rfl

theorem cell21_2093413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_2093413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093413 prefixEnd_2093413 := by exact prefixLift 2093413
  have htrace : WordTrace (prefixWord ++ tailWord_2093413) baseStart_2093413 baseEnd_2093413 := by
    simpa [prefixWord, tailWord_2093413, baseEnd_2093413] using wordTrace_append hprefix tailTrace_2093413
  have hstable : (prefixWord ++ tailWord_2093413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093413).length < 2 ^ (prefixWord ++ tailWord_2093413).sum := by decide
  have hdescent : baseEnd_2093413 < baseStart_2093413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093450 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_2093450 : Nat := 118140960795 + 2093450 * 2 ^ 59
def prefixEnd_2093450 : Nat := 4983230072969 + 3 ^ 40 * 2093450 * 2
def baseEnd_2093450 : Nat := 477753811624417600421069

theorem tailTrace_2093450 : CollatzResearch.WordTrace tailWord_2093450 prefixEnd_2093450 477753811624417600421069 := by
  unfold tailWord_2093450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088598566448914410117451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50902929510530438426979869 19088598566448914410117451)
  ·
    refine ⟨28632897849673371615176177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088598566448914410117451 28632897849673371615176177)
    ·
      refine ⟨21474673387255028711382133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28632897849673371615176177 21474673387255028711382133)
      ·
        refine ⟨2013250630055158941692075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21474673387255028711382133 2013250630055158941692075)
        ·
          refine ⟨3019875945082738412538113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013250630055158941692075 3019875945082738412538113)
          ·
            refine ⟨2264906958812053809403585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019875945082738412538113 2264906958812053809403585)
            ·
              refine ⟨1698680219109040357052689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264906958812053809403585 1698680219109040357052689)
              ·
                refine ⟨1274010164331780267789517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698680219109040357052689 1274010164331780267789517)
                ·
                  refine ⟨477753811624417600421069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274010164331780267789517 477753811624417600421069)
                  ·
                    rfl

theorem cell21_2093450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_2093450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093450 prefixEnd_2093450 := by exact prefixLift 2093450
  have htrace : WordTrace (prefixWord ++ tailWord_2093450) baseStart_2093450 baseEnd_2093450 := by
    simpa [prefixWord, tailWord_2093450, baseEnd_2093450] using wordTrace_append hprefix tailTrace_2093450
  have hstable : (prefixWord ++ tailWord_2093450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093450).length < 2 ^ (prefixWord ++ tailWord_2093450).sum := by decide
  have hdescent : baseEnd_2093450 < baseStart_2093450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093579 : List Nat := [1, 1, 1, 1, 7, 2, 2, 6]
def baseStart_2093579 : Nat := 118140960795 + 2093579 * 2 ^ 59
def prefixEnd_2093579 : Nat := 4983230072969 + 3 ^ 40 * 2093579 * 2
def baseEnd_2093579 : Nat := 159261083727314014256935

theorem tailTrace_2093579 : CollatzResearch.WordTrace tailWord_2093579 prefixEnd_2093579 159261083727314014256935 := by
  unfold tailWord_2093579
  simp only [CollatzResearch.WordTrace]
  refine ⟨76359099282328312671915791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50906066188218875114610527 76359099282328312671915791)
  ·
    refine ⟨114538648923492469007873687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76359099282328312671915791 114538648923492469007873687)
    ·
      refine ⟨171807973385238703511810531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114538648923492469007873687 171807973385238703511810531)
      ·
        refine ⟨257711960077858055267715797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171807973385238703511810531 257711960077858055267715797)
        ·
          refine ⟨6040124064324798170337089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257711960077858055267715797 6040124064324798170337089)
          ·
            refine ⟨4530093048243598627752817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6040124064324798170337089 4530093048243598627752817)
            ·
              refine ⟨3397569786182698970814613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530093048243598627752817 3397569786182698970814613)
              ·
                refine ⟨159261083727314014256935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3397569786182698970814613 159261083727314014256935)
                ·
                  rfl

theorem cell21_2093579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_2093579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093579 prefixEnd_2093579 := by exact prefixLift 2093579
  have htrace : WordTrace (prefixWord ++ tailWord_2093579) baseStart_2093579 baseEnd_2093579 := by
    simpa [prefixWord, tailWord_2093579, baseEnd_2093579] using wordTrace_append hprefix tailTrace_2093579
  have hstable : (prefixWord ++ tailWord_2093579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093579).length < 2 ^ (prefixWord ++ tailWord_2093579).sum := by decide
  have hdescent : baseEnd_2093579 < baseStart_2093579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093582 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_2093582 : Nat := 118140960795 + 2093582 * 2 ^ 59
def prefixEnd_2093582 : Nat := 4983230072969 + 3 ^ 40 * 2093582 * 2
def baseEnd_2093582 : Nat := 477783935822814704220799

theorem tailTrace_2093582 : CollatzResearch.WordTrace tailWord_2093582 prefixEnd_2093582 477783935822814704220799 := by
  unfold tailWord_2093582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9544901087664680523034375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50906139134211629456183333 9544901087664680523034375)
  ·
    refine ⟨14317351631497020784551563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9544901087664680523034375 14317351631497020784551563)
    ·
      refine ⟨21476027447245531176827345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14317351631497020784551563 21476027447245531176827345)
      ·
        refine ⟨16107020585434148382620509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21476027447245531176827345 16107020585434148382620509)
        ·
          refine ⟨6040132719537805643482691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16107020585434148382620509 6040132719537805643482691)
          ·
            refine ⟨9060199079306708465224037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040132719537805643482691 9060199079306708465224037)
            ·
              refine ⟨1698787327370007837229507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9060199079306708465224037 1698787327370007837229507)
              ·
                refine ⟨2548180991055011755844261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698787327370007837229507 2548180991055011755844261)
                ·
                  refine ⟨477783935822814704220799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548180991055011755844261 477783935822814704220799)
                  ·
                    rfl

theorem cell21_2093582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_2093582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093582 prefixEnd_2093582 := by exact prefixLift 2093582
  have htrace : WordTrace (prefixWord ++ tailWord_2093582) baseStart_2093582 baseEnd_2093582 := by
    simpa [prefixWord, tailWord_2093582, baseEnd_2093582] using wordTrace_append hprefix tailTrace_2093582
  have hstable : (prefixWord ++ tailWord_2093582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093582).length < 2 ^ (prefixWord ++ tailWord_2093582).sum := by decide
  have hdescent : baseEnd_2093582 < baseStart_2093582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093613 : List Nat := [1, 5, 4, 1, 1, 9]
def baseStart_2093613 : Nat := 118140960795 + 2093613 * 2 ^ 59
def prefixEnd_2093613 : Nat := 4983230072969 + 3 ^ 40 * 2093613 * 2
def baseEnd_2093613 : Nat := 17695963349820945896447

theorem tailTrace_2093613 : CollatzResearch.WordTrace tailWord_2093613 prefixEnd_2093613 17695963349820945896447 := by
  unfold tailWord_2093613
  simp only [CollatzResearch.WordTrace]
  refine ⟨76360339364205136478653493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50906892909470090985768995 76360339364205136478653493)
  ·
    refine ⟨7158781815394231544873765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76360339364205136478653493 7158781815394231544873765)
    ·
      refine ⟨1342271590386418414663831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7158781815394231544873765 1342271590386418414663831)
      ·
        refine ⟨2013407385579627621995747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342271590386418414663831 2013407385579627621995747)
        ·
          refine ⟨3020111078369441432993621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013407385579627621995747 3020111078369441432993621)
          ·
            refine ⟨17695963349820945896447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3020111078369441432993621 17695963349820945896447)
            ·
              rfl

theorem cell21_2093613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 9].length) (baseStart_2093613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093613 prefixEnd_2093613 := by exact prefixLift 2093613
  have htrace : WordTrace (prefixWord ++ tailWord_2093613) baseStart_2093613 baseEnd_2093613 := by
    simpa [prefixWord, tailWord_2093613, baseEnd_2093613] using wordTrace_append hprefix tailTrace_2093613
  have hstable : (prefixWord ++ tailWord_2093613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093613).length < 2 ^ (prefixWord ++ tailWord_2093613).sum := by decide
  have hdescent : baseEnd_2093613 < baseStart_2093613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093630 : List Nat := [4, 2, 1, 4, 2, 1, 1, 6]
def baseStart_2093630 : Nat := 118140960795 + 2093630 * 2 ^ 59
def prefixEnd_2093630 : Nat := 4983230072969 + 3 ^ 40 * 2093630 * 2
def baseEnd_2093630 : Nat := 159264963358925762473567

theorem tailTrace_2093630 : CollatzResearch.WordTrace tailWord_2093630 prefixEnd_2093630 159264963358925762473567 := by
  unfold tailWord_2093630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545119925642943547752793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50907306270095698921348229 9545119925642943547752793)
  ·
    refine ⟨7158839944232207660814595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9545119925642943547752793 7158839944232207660814595)
    ·
      refine ⟨10738259916348311491221893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158839944232207660814595 10738259916348311491221893)
      ·
        refine ⟨2013423734315308404604105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10738259916348311491221893 2013423734315308404604105)
        ·
          refine ⟨1510067800736481303453079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013423734315308404604105 1510067800736481303453079)
          ·
            refine ⟨2265101701104721955179619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510067800736481303453079 2265101701104721955179619)
            ·
              refine ⟨3397652551657082932769429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265101701104721955179619 3397652551657082932769429)
              ·
                refine ⟨159264963358925762473567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3397652551657082932769429 159264963358925762473567)
                ·
                  rfl

theorem cell21_2093630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_2093630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093630 prefixEnd_2093630 := by exact prefixLift 2093630
  have htrace : WordTrace (prefixWord ++ tailWord_2093630) baseStart_2093630 baseEnd_2093630 := by
    simpa [prefixWord, tailWord_2093630, baseEnd_2093630] using wordTrace_append hprefix tailTrace_2093630
  have hstable : (prefixWord ++ tailWord_2093630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093630).length < 2 ^ (prefixWord ++ tailWord_2093630).sum := by decide
  have hdescent : baseEnd_2093630 < baseStart_2093630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093655 : List Nat := [1, 1, 3, 2, 2, 2, 5, 5]
def baseStart_2093655 : Nat := 118140960795 + 2093655 * 2 ^ 59
def prefixEnd_2093655 : Nat := 4983230072969 + 3 ^ 40 * 2093655 * 2
def baseEnd_2093655 : Nat := 159266865139127599834661

theorem tailTrace_2093655 : CollatzResearch.WordTrace tailWord_2093655 prefixEnd_2093655 159266865139127599834661 := by
  unfold tailWord_2093655
  simp only [CollatzResearch.WordTrace]
  refine ⟨76361871230052977651682419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50907914153368651767788279 76361871230052977651682419)
  ·
    refine ⟨114542806845079466477523629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76361871230052977651682419 114542806845079466477523629)
    ·
      refine ⟨42953552566904799929071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114542806845079466477523629 42953552566904799929071361)
      ·
        refine ⟨32215164425178599946803521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42953552566904799929071361 32215164425178599946803521)
        ·
          refine ⟨24161373318883949960102641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32215164425178599946803521 24161373318883949960102641)
          ·
            refine ⟨18121029989162962470076981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24161373318883949960102641 18121029989162962470076981)
            ·
              refine ⟨1698846561484027731569717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18121029989162962470076981 1698846561484027731569717)
              ·
                refine ⟨159266865139127599834661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1698846561484027731569717 159266865139127599834661)
                ·
                  rfl

theorem cell21_2093655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].length) (baseStart_2093655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093655 prefixEnd_2093655 := by exact prefixLift 2093655
  have htrace : WordTrace (prefixWord ++ tailWord_2093655) baseStart_2093655 baseEnd_2093655 := by
    simpa [prefixWord, tailWord_2093655, baseEnd_2093655] using wordTrace_append hprefix tailTrace_2093655
  have hstable : (prefixWord ++ tailWord_2093655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093655).length < 2 ^ (prefixWord ++ tailWord_2093655).sum := by decide
  have hdescent : baseEnd_2093655 < baseStart_2093655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093751 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 4]
def baseStart_2093751 : Nat := 118140960795 + 2093751 * 2 ^ 59
def prefixEnd_2093751 : Nat := 4983230072969 + 3 ^ 40 * 2093751 * 2
def baseEnd_2093751 : Nat := 477822503925307965903787

theorem tailTrace_2093751 : CollatzResearch.WordTrace tailWord_2093751 prefixEnd_2093751 477822503925307965903787 := by
  unfold tailWord_2093751
  simp only [CollatzResearch.WordTrace]
  refine ⟨76365372637705186047177107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50910248425136790698118071 76365372637705186047177107)
  ·
    refine ⟨114548058956557779070765661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76365372637705186047177107 114548058956557779070765661)
    ·
      refine ⟨42955522108709167151537123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114548058956557779070765661 42955522108709167151537123)
      ·
        refine ⟨64433283163063750727305685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42955522108709167151537123 64433283163063750727305685)
        ·
          refine ⟨1510155074134306657671227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64433283163063750727305685 1510155074134306657671227)
          ·
            refine ⟨2265232611201459986506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510155074134306657671227 2265232611201459986506841)
            ·
              refine ⟨1698924458401094989880131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265232611201459986506841 1698924458401094989880131)
              ·
                refine ⟨2548386687601642484820197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698924458401094989880131 2548386687601642484820197)
                ·
                  refine ⟨477822503925307965903787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548386687601642484820197 477822503925307965903787)
                  ·
                    rfl

theorem cell21_2093751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].length) (baseStart_2093751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093751 prefixEnd_2093751 := by exact prefixLift 2093751
  have htrace : WordTrace (prefixWord ++ tailWord_2093751) baseStart_2093751 baseEnd_2093751 := by
    simpa [prefixWord, tailWord_2093751, baseEnd_2093751] using wordTrace_append hprefix tailTrace_2093751
  have hstable : (prefixWord ++ tailWord_2093751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093751).length < 2 ^ (prefixWord ++ tailWord_2093751).sum := by decide
  have hdescent : baseEnd_2093751 < baseStart_2093751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093793 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2093793 : Nat := 118140960795 + 2093793 * 2 ^ 59
def prefixEnd_2093793 : Nat := 4983230072969 + 3 ^ 40 * 2093793 * 2
def baseEnd_2093793 : Nat := 477832088897525226203701

theorem tailTrace_2093793 : CollatzResearch.WordTrace tailWord_2093793 prefixEnd_2093793 477832088897525226203701 := by
  unfold tailWord_2093793
  simp only [CollatzResearch.WordTrace]
  refine ⟨76366904503553027220206033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50911269669035351480137355 76366904503553027220206033)
  ·
    refine ⟨57275178377664770415154525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76366904503553027220206033 57275178377664770415154525)
    ·
      refine ⟨21478191891624288905682947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57275178377664770415154525 21478191891624288905682947)
      ·
        refine ⟨32217287837436433358524421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21478191891624288905682947 32217287837436433358524421)
        ·
          refine ⟨6040741469519331254723329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32217287837436433358524421 6040741469519331254723329)
          ·
            refine ⟨4530556102139498441042497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6040741469519331254723329 4530556102139498441042497)
            ·
              refine ⟨3397917076604623830781873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530556102139498441042497 3397917076604623830781873)
              ·
                refine ⟨2548437807453467873086405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397917076604623830781873 2548437807453467873086405)
                ·
                  refine ⟨477832088897525226203701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548437807453467873086405 477832088897525226203701)
                  ·
                    rfl

theorem cell21_2093793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2093793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093793 prefixEnd_2093793 := by exact prefixLift 2093793
  have htrace : WordTrace (prefixWord ++ tailWord_2093793) baseStart_2093793 baseEnd_2093793 := by
    simpa [prefixWord, tailWord_2093793, baseEnd_2093793] using wordTrace_append hprefix tailTrace_2093793
  have hstable : (prefixWord ++ tailWord_2093793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093793).length < 2 ^ (prefixWord ++ tailWord_2093793).sum := by decide
  have hdescent : baseEnd_2093793 < baseStart_2093793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093796 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2093796 : Nat := 118140960795 + 2093796 * 2 ^ 59
def prefixEnd_2093796 : Nat := 4983230072969 + 3 ^ 40 * 2093796 * 2
def baseEnd_2093796 : Nat := 477832773538397887653695

theorem tailTrace_2093796 : CollatzResearch.WordTrace tailWord_2093796 prefixEnd_2093796 477832773538397887653695 := by
  unfold tailWord_2093796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38183506961271079366282621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50911342615028105821710161 38183506961271079366282621)
  ·
    refine ⟨14318815110476654762355983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38183506961271079366282621 14318815110476654762355983)
    ·
      refine ⟨21478222665714982143533975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14318815110476654762355983 21478222665714982143533975)
      ·
        refine ⟨32217333998572473215300963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21478222665714982143533975 32217333998572473215300963)
        ·
          refine ⟨48326000997858709822951445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32217333998572473215300963 48326000997858709822951445)
          ·
            refine ⟨2265281296774627022950849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48326000997858709822951445 2265281296774627022950849)
            ·
              refine ⟨1698960972580970267213137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265281296774627022950849 1698960972580970267213137)
              ·
                refine ⟨1274220729435727700409853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698960972580970267213137 1274220729435727700409853)
                ·
                  refine ⟨477832773538397887653695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274220729435727700409853 477832773538397887653695)
                  ·
                    rfl

theorem cell21_2093796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2093796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093796 prefixEnd_2093796 := by exact prefixLift 2093796
  have htrace : WordTrace (prefixWord ++ tailWord_2093796) baseStart_2093796 baseEnd_2093796 := by
    simpa [prefixWord, tailWord_2093796, baseEnd_2093796] using wordTrace_append hprefix tailTrace_2093796
  have hstable : (prefixWord ++ tailWord_2093796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093796).length < 2 ^ (prefixWord ++ tailWord_2093796).sum := by decide
  have hdescent : baseEnd_2093796 < baseStart_2093796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093807 : List Nat := [1, 1, 2, 1, 5, 4, 1, 6]
def baseStart_2093807 : Nat := 118140960795 + 2093807 * 2 ^ 59
def prefixEnd_2093807 : Nat := 4983230072969 + 3 ^ 40 * 2093807 * 2
def baseEnd_2093807 : Nat := 159278427962754770990113

theorem tailTrace_2093807 : CollatzResearch.WordTrace tailWord_2093807 prefixEnd_2093807 159278427962754770990113 := by
  unfold tailWord_2093807
  simp only [CollatzResearch.WordTrace]
  refine ⟨76367415125502307611215675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50911610083668205074143783 76367415125502307611215675)
  ·
    refine ⟨114551122688253461416823513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76367415125502307611215675 114551122688253461416823513)
    ·
      refine ⟨85913342016190096062617635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114551122688253461416823513 85913342016190096062617635)
      ·
        refine ⟨128870013024285144093926453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85913342016190096062617635 128870013024285144093926453)
        ·
          refine ⟨12081563721026732258805605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128870013024285144093926453 12081563721026732258805605)
          ·
            refine ⟨2265293197692512298526051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12081563721026732258805605 2265293197692512298526051)
            ·
              refine ⟨3397939796538768447789077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265293197692512298526051 3397939796538768447789077)
              ·
                refine ⟨159278427962754770990113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3397939796538768447789077 159278427962754770990113)
                ·
                  rfl

theorem cell21_2093807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_2093807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093807 prefixEnd_2093807 := by exact prefixLift 2093807
  have htrace : WordTrace (prefixWord ++ tailWord_2093807) baseStart_2093807 baseEnd_2093807 := by
    simpa [prefixWord, tailWord_2093807, baseEnd_2093807] using wordTrace_append hprefix tailTrace_2093807
  have hstable : (prefixWord ++ tailWord_2093807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093807).length < 2 ^ (prefixWord ++ tailWord_2093807).sum := by decide
  have hdescent : baseEnd_2093807 < baseStart_2093807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093821 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2093821 : Nat := 118140960795 + 2093821 * 2 ^ 59
def prefixEnd_2093821 : Nat := 4983230072969 + 3 ^ 40 * 2093821 * 2
def baseEnd_2093821 : Nat := 477838478879003399736977

theorem tailTrace_2093821 : CollatzResearch.WordTrace tailWord_2093821 prefixEnd_2093821 477838478879003399736977 := by
  unfold tailWord_2093821
  simp only [CollatzResearch.WordTrace]
  refine ⟨76367925747451588002225317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50911950498301058668150211 76367925747451588002225317)
  ·
    refine ⟨14318986077647172750417247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76367925747451588002225317 14318986077647172750417247)
    ·
      refine ⟨21478479116470759125625871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14318986077647172750417247 21478479116470759125625871)
      ·
        refine ⟨32217718674706138688438807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21478479116470759125625871 32217718674706138688438807)
        ·
          refine ⟨48326578012059208032658211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32217718674706138688438807 48326578012059208032658211)
          ·
            refine ⟨72489867018088812048987317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48326578012059208032658211 72489867018088812048987317)
            ·
              refine ⟨6795925032945826129592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72489867018088812048987317 6795925032945826129592561)
              ·
                refine ⟨5096943774709369597194421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795925032945826129592561 5096943774709369597194421)
                ·
                  refine ⟨477838478879003399736977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096943774709369597194421 477838478879003399736977)
                  ·
                    rfl

theorem cell21_2093821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2093821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093821 prefixEnd_2093821 := by exact prefixLift 2093821
  have htrace : WordTrace (prefixWord ++ tailWord_2093821) baseStart_2093821 baseEnd_2093821 := by
    simpa [prefixWord, tailWord_2093821, baseEnd_2093821] using wordTrace_append hprefix tailTrace_2093821
  have hstable : (prefixWord ++ tailWord_2093821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093821).length < 2 ^ (prefixWord ++ tailWord_2093821).sum := by decide
  have hdescent : baseEnd_2093821 < baseStart_2093821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093835 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_2093835 : Nat := 118140960795 + 2093835 * 2 ^ 59
def prefixEnd_2093835 : Nat := 4983230072969 + 3 ^ 40 * 2093835 * 2
def baseEnd_2093835 : Nat := 477841673869742486503615

theorem tailTrace_2093835 : CollatzResearch.WordTrace tailWord_2093835 prefixEnd_2093835 477841673869742486503615 := by
  unfold tailWord_2093835
  simp only [CollatzResearch.WordTrace]
  refine ⟨76368436369400868393234959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50912290912933912262156639 76368436369400868393234959)
  ·
    refine ⟨114552654554101302589852439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76368436369400868393234959 114552654554101302589852439)
    ·
      refine ⟨171828981831151953884778659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114552654554101302589852439 171828981831151953884778659)
      ·
        refine ⟨257743472746727930827167989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171828981831151953884778659 257743472746727930827167989)
        ·
          refine ⟨24163450570005743515046999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257743472746727930827167989 24163450570005743515046999)
          ·
            refine ⟨36245175855008615272570499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24163450570005743515046999 36245175855008615272570499)
            ·
              refine ⟨54367763782512922908855749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36245175855008615272570499 54367763782512922908855749)
              ·
                refine ⟨10193955709221173045410453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54367763782512922908855749 10193955709221173045410453)
                ·
                  refine ⟨477841673869742486503615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10193955709221173045410453 477841673869742486503615)
                  ·
                    rfl

theorem cell21_2093835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_2093835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093835 prefixEnd_2093835 := by exact prefixLift 2093835
  have htrace : WordTrace (prefixWord ++ tailWord_2093835) baseStart_2093835 baseEnd_2093835 := by
    simpa [prefixWord, tailWord_2093835, baseEnd_2093835] using wordTrace_append hprefix tailTrace_2093835
  have hstable : (prefixWord ++ tailWord_2093835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093835).length < 2 ^ (prefixWord ++ tailWord_2093835).sum := by decide
  have hdescent : baseEnd_2093835 < baseStart_2093835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093852 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_2093852 : Nat := 118140960795 + 2093852 * 2 ^ 59
def prefixEnd_2093852 : Nat := 4983230072969 + 3 ^ 40 * 2093852 * 2
def baseEnd_2093852 : Nat := 477845553501354234720247

theorem tailTrace_2093852 : CollatzResearch.WordTrace tailWord_2093852 prefixEnd_2093852 477845553501354234720247 := by
  unfold tailWord_2093852
  simp only [CollatzResearch.WordTrace]
  refine ⟨38184528205169640148301905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50912704273559520197735873 38184528205169640148301905)
  ·
    refine ⟨28638396153877230111226429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38184528205169640148301905 28638396153877230111226429)
    ·
      refine ⟨10739398557703961291709911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28638396153877230111226429 10739398557703961291709911)
      ·
        refine ⟨16109097836555941937564867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739398557703961291709911 16109097836555941937564867)
        ·
          refine ⟨24163646754833912906347301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109097836555941937564867 24163646754833912906347301)
          ·
            refine ⟨4530683766531358669940119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24163646754833912906347301 4530683766531358669940119)
            ·
              refine ⟨6796025649797038004910179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530683766531358669940119 6796025649797038004910179)
              ·
                refine ⟨10194038474695557007365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796025649797038004910179 10194038474695557007365269)
                ·
                  refine ⟨477845553501354234720247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10194038474695557007365269 477845553501354234720247)
                  ·
                    rfl

theorem cell21_2093852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_2093852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093852 prefixEnd_2093852 := by exact prefixLift 2093852
  have htrace : WordTrace (prefixWord ++ tailWord_2093852) baseStart_2093852 baseEnd_2093852 := by
    simpa [prefixWord, tailWord_2093852, baseEnd_2093852] using wordTrace_append hprefix tailTrace_2093852
  have hstable : (prefixWord ++ tailWord_2093852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093852).length < 2 ^ (prefixWord ++ tailWord_2093852).sum := by decide
  have hdescent : baseEnd_2093852 < baseStart_2093852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093889 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 3]
def baseStart_2093889 : Nat := 118140960795 + 2093889 * 2 ^ 59
def prefixEnd_2093889 : Nat := 4983230072969 + 3 ^ 40 * 2093889 * 2
def baseEnd_2093889 : Nat := 477853997405450392603505

theorem tailTrace_2093889 : CollatzResearch.WordTrace tailWord_2093889 prefixEnd_2093889 477853997405450392603505 := by
  unfold tailWord_2093889
  simp only [CollatzResearch.WordTrace]
  refine ⟨76370405911205235615700721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50913603940803490410467147 76370405911205235615700721)
  ·
    refine ⟨57277804433403926711775541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76370405911205235615700721 57277804433403926711775541)
    ·
      refine ⟨5369794165631618129228957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57277804433403926711775541 5369794165631618129228957)
      ·
        refine ⟨2013672812111856798460859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5369794165631618129228957 2013672812111856798460859)
        ·
          refine ⟨3020509218167785197691289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013672812111856798460859 3020509218167785197691289)
          ·
            refine ⟨2265381913625838898268467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020509218167785197691289 2265381913625838898268467)
            ·
              refine ⟨3398072870438758347402701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265381913625838898268467 3398072870438758347402701)
              ·
                refine ⟨1274277326414534380276013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398072870438758347402701 1274277326414534380276013)
                ·
                  refine ⟨477853997405450392603505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274277326414534380276013 477853997405450392603505)
                  ·
                    rfl

theorem cell21_2093889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_2093889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093889 prefixEnd_2093889 := by exact prefixLift 2093889
  have htrace : WordTrace (prefixWord ++ tailWord_2093889) baseStart_2093889 baseEnd_2093889 := by
    simpa [prefixWord, tailWord_2093889, baseEnd_2093889] using wordTrace_append hprefix tailTrace_2093889
  have hstable : (prefixWord ++ tailWord_2093889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093889).length < 2 ^ (prefixWord ++ tailWord_2093889).sum := by decide
  have hdescent : baseEnd_2093889 < baseStart_2093889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2093914 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_2093914 : Nat := 118140960795 + 2093914 * 2 ^ 59
def prefixEnd_2093914 : Nat := 4983230072969 + 3 ^ 40 * 2093914 * 2
def baseEnd_2093914 : Nat := 477859702746055904686787

theorem tailTrace_2093914 : CollatzResearch.WordTrace tailWord_2093914 prefixEnd_2093914 477859702746055904686787 := by
  unfold tailWord_2093914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092829434028666221340199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50914211824076443256907197 19092829434028666221340199)
  ·
    refine ⟨28639244151042999332010299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092829434028666221340199 28639244151042999332010299)
    ·
      refine ⟨42958866226564498998015449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28639244151042999332010299 42958866226564498998015449)
      ·
        refine ⟨32219149669923374248511587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42958866226564498998015449 32219149669923374248511587)
        ·
          refine ⟨48328724504885061372767381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32219149669923374248511587 48328724504885061372767381)
          ·
            refine ⟨2265408961166487251848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48328724504885061372767381 2265408961166487251848471)
            ·
              refine ⟨3398113441749730877772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265408961166487251848471 3398113441749730877772707)
              ·
                refine ⟨5097170162624596316659061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398113441749730877772707 5097170162624596316659061)
                ·
                  refine ⟨477859702746055904686787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5097170162624596316659061 477859702746055904686787)
                  ·
                    rfl

theorem cell21_2093914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_2093914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2093914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2093914 prefixEnd_2093914 := by exact prefixLift 2093914
  have htrace : WordTrace (prefixWord ++ tailWord_2093914) baseStart_2093914 baseEnd_2093914 := by
    simpa [prefixWord, tailWord_2093914, baseEnd_2093914] using wordTrace_append hprefix tailTrace_2093914
  have hstable : (prefixWord ++ tailWord_2093914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2093914).length < 2 ^ (prefixWord ++ tailWord_2093914).sum := by decide
  have hdescent : baseEnd_2093914 < baseStart_2093914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2093914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094063 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_2094063 : Nat := 118140960795 + 2094063 * 2 ^ 59
def prefixEnd_2094063 : Nat := 4983230072969 + 3 ^ 40 * 2094063 * 2
def baseEnd_2094063 : Nat := 477893706576064756703149

theorem tailTrace_2094063 : CollatzResearch.WordTrace tailWord_2094063 prefixEnd_2094063 477893706576064756703149 := by
  unfold tailWord_2094063
  simp only [CollatzResearch.WordTrace]
  refine ⟨76376752212574863332534843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50917834808383242221689895 76376752212574863332534843)
  ·
    refine ⟨114565128318862294998802265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76376752212574863332534843 114565128318862294998802265)
    ·
      refine ⟨85923846239146721249101699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114565128318862294998802265 85923846239146721249101699)
      ·
        refine ⟨128885769358720081873652549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85923846239146721249101699 128885769358720081873652549)
        ·
          refine ⟨24166081754760015351309853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128885769358720081873652549 24166081754760015351309853)
          ·
            refine ⟨9062280658035005756741195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24166081754760015351309853 9062280658035005756741195)
            ·
              refine ⟨13593420987052508635111793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062280658035005756741195 13593420987052508635111793)
              ·
                refine ⟨10195065740289381476333845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13593420987052508635111793 10195065740289381476333845)
                ·
                  refine ⟨477893706576064756703149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10195065740289381476333845 477893706576064756703149)
                  ·
                    rfl

theorem cell21_2094063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_2094063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094063 prefixEnd_2094063 := by exact prefixLift 2094063
  have htrace : WordTrace (prefixWord ++ tailWord_2094063) baseStart_2094063 baseEnd_2094063 := by
    simpa [prefixWord, tailWord_2094063, baseEnd_2094063] using wordTrace_append hprefix tailTrace_2094063
  have hstable : (prefixWord ++ tailWord_2094063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094063).length < 2 ^ (prefixWord ++ tailWord_2094063).sum := by decide
  have hdescent : baseEnd_2094063 < baseStart_2094063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094069 : List Nat := [1, 3, 5, 2, 2, 1, 7]
def baseStart_2094069 : Nat := 118140960795 + 2094069 * 2 ^ 59
def prefixEnd_2094069 : Nat := 4983230072969 + 3 ^ 40 * 2094069 * 2
def baseEnd_2094069 : Nat := 53099452873090008844793

theorem tailTrace_2094069 : CollatzResearch.WordTrace tailWord_2094069 prefixEnd_2094069 53099452873090008844793 := by
  unfold tailWord_2094069
  simp only [CollatzResearch.WordTrace]
  refine ⟨76376971050553126357253261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50917980700368750904835507 76376971050553126357253261)
  ·
    refine ⟨28641364143957422383969973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76376971050553126357253261 28641364143957422383969973)
    ·
      refine ⟨2685127888496008348497185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28641364143957422383969973 2685127888496008348497185)
      ·
        refine ⟨2013845916372006261372889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685127888496008348497185 2013845916372006261372889)
        ·
          refine ⟨1510384437279004696029667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013845916372006261372889 1510384437279004696029667)
          ·
            refine ⟨2265576655918507044044501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510384437279004696029667 2265576655918507044044501)
            ·
              refine ⟨53099452873090008844793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2265576655918507044044501 53099452873090008844793)
              ·
                rfl

theorem cell21_2094069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 7].length) (baseStart_2094069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094069 prefixEnd_2094069 := by exact prefixLift 2094069
  have htrace : WordTrace (prefixWord ++ tailWord_2094069) baseStart_2094069 baseEnd_2094069 := by
    simpa [prefixWord, tailWord_2094069, baseEnd_2094069] using wordTrace_append hprefix tailTrace_2094069
  have hstable : (prefixWord ++ tailWord_2094069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094069).length < 2 ^ (prefixWord ++ tailWord_2094069).sum := by decide
  have hdescent : baseEnd_2094069 < baseStart_2094069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094094 : List Nat := [4, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2094094 : Nat := 118140960795 + 2094094 * 2 ^ 59
def prefixEnd_2094094 : Nat := 4983230072969 + 3 ^ 40 * 2094094 * 2
def baseEnd_2094094 : Nat := 159300260399471863895473

theorem tailTrace_2094094 : CollatzResearch.WordTrace tailWord_2094094 prefixEnd_2094094 159300260399471863895473 := by
  unfold tailWord_2094094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547235359432819453364167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50918588583641703751275557 9547235359432819453364167)
  ·
    refine ⟨14320853039149229180046251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9547235359432819453364167 14320853039149229180046251)
    ·
      refine ⟨21481279558723843770069377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14320853039149229180046251 21481279558723843770069377)
      ·
        refine ⟨16110959669042882827552033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21481279558723843770069377 16110959669042882827552033)
        ·
          refine ⟨12083219751782162120664025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110959669042882827552033 12083219751782162120664025)
          ·
            refine ⟨9062414813836621590498019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083219751782162120664025 9062414813836621590498019)
            ·
              refine ⟨13593622220754932385747029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062414813836621590498019 13593622220754932385747029)
              ·
                refine ⟨159300260399471863895473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13593622220754932385747029 159300260399471863895473)
                ·
                  rfl

theorem cell21_2094094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2094094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094094 prefixEnd_2094094 := by exact prefixLift 2094094
  have htrace : WordTrace (prefixWord ++ tailWord_2094094) baseStart_2094094 baseEnd_2094094 := by
    simpa [prefixWord, tailWord_2094094, baseEnd_2094094] using wordTrace_append hprefix tailTrace_2094094
  have hstable : (prefixWord ++ tailWord_2094094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094094).length < 2 ^ (prefixWord ++ tailWord_2094094).sum := by decide
  have hdescent : baseEnd_2094094 < baseStart_2094094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094153 : List Nat := [1, 2, 1, 1, 2, 2, 2, 10]
def baseStart_2094153 : Nat := 118140960795 + 2094153 * 2 ^ 59
def prefixEnd_2094153 : Nat := 4983230072969 + 3 ^ 40 * 2094153 * 2
def baseEnd_2094153 : Nat := 159304748600748200067655

theorem tailTrace_2094153 : CollatzResearch.WordTrace tailWord_2094153 prefixEnd_2094153 159304748600748200067655 := by
  unfold tailWord_2094153
  simp only [CollatzResearch.WordTrace]
  refine ⟨76380034782248808703311113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50920023188165872468874075 76380034782248808703311113)
  ·
    refine ⟨57285026086686606527483335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76380034782248808703311113 57285026086686606527483335)
    ·
      refine ⟨85927539130029909791225003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57285026086686606527483335 85927539130029909791225003)
      ·
        refine ⟨128891308695044864686837505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85927539130029909791225003 128891308695044864686837505)
        ·
          refine ⟨96668481521283648515128129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128891308695044864686837505 96668481521283648515128129)
          ·
            refine ⟨72501361140962736386346097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96668481521283648515128129 72501361140962736386346097)
            ·
              refine ⟨54376020855722052289759573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72501361140962736386346097 54376020855722052289759573)
              ·
                refine ⟨159304748600748200067655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54376020855722052289759573 159304748600748200067655)
                ·
                  rfl

theorem cell21_2094153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_2094153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094153 prefixEnd_2094153 := by exact prefixLift 2094153
  have htrace : WordTrace (prefixWord ++ tailWord_2094153) baseStart_2094153 baseEnd_2094153 := by
    simpa [prefixWord, tailWord_2094153, baseEnd_2094153] using wordTrace_append hprefix tailTrace_2094153
  have hstable : (prefixWord ++ tailWord_2094153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094153).length < 2 ^ (prefixWord ++ tailWord_2094153).sum := by decide
  have hdescent : baseEnd_2094153 < baseStart_2094153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094305 : List Nat := [1, 2, 3, 1, 3, 11]
def baseStart_2094305 : Nat := 118140960795 + 2094305 * 2 ^ 59
def prefixEnd_2094305 : Nat := 4983230072969 + 3 ^ 40 * 2094305 * 2
def baseEnd_2094305 : Nat := 17701812380486152358123

theorem tailTrace_2094305 : CollatzResearch.WordTrace tailWord_2094305 prefixEnd_2094305 17701812380486152358123 := by
  unfold tailWord_2094305
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385578677698138662844369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50923719118465425775229579 76385578677698138662844369)
  ·
    refine ⟨57289184008273603997133277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76385578677698138662844369 57289184008273603997133277)
    ·
      refine ⟨21483444003102601498924979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57289184008273603997133277 21483444003102601498924979)
      ·
        refine ⟨32225166004653902248387469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21483444003102601498924979 32225166004653902248387469)
        ·
          refine ⟨12084437251745213343145301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32225166004653902248387469 12084437251745213343145301)
          ·
            refine ⟨17701812380486152358123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12084437251745213343145301 17701812380486152358123)
            ·
              rfl

theorem cell21_2094305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 11].length) (baseStart_2094305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094305 prefixEnd_2094305 := by exact prefixLift 2094305
  have htrace : WordTrace (prefixWord ++ tailWord_2094305) baseStart_2094305 baseEnd_2094305 := by
    simpa [prefixWord, tailWord_2094305, baseEnd_2094305] using wordTrace_append hprefix tailTrace_2094305
  have hstable : (prefixWord ++ tailWord_2094305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094305).length < 2 ^ (prefixWord ++ tailWord_2094305).sum := by decide
  have hdescent : baseEnd_2094305 < baseStart_2094305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094311 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 3]
def baseStart_2094311 : Nat := 118140960795 + 2094311 * 2 ^ 59
def prefixEnd_2094311 : Nat := 4983230072969 + 3 ^ 40 * 2094311 * 2
def baseEnd_2094311 : Nat := 477950303554871436569309

theorem tailTrace_2094311 : CollatzResearch.WordTrace tailWord_2094311 prefixEnd_2094311 477950303554871436569309 := by
  unfold tailWord_2094311
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385797515676401687562787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50923865010450934458375191 76385797515676401687562787)
  ·
    refine ⟨114578696273514602531344181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76385797515676401687562787 114578696273514602531344181)
    ·
      refine ⟨10741752775641993987313517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114578696273514602531344181 10741752775641993987313517)
      ·
        refine ⟨4028157290865747745242569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10741752775641993987313517 4028157290865747745242569)
        ·
          refine ⟨3021117968149310808931927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4028157290865747745242569 3021117968149310808931927)
          ·
            refine ⟨4531676952223966213397891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021117968149310808931927 4531676952223966213397891)
            ·
              refine ⟨6797515428335949320096837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531676952223966213397891 6797515428335949320096837)
              ·
                refine ⟨1274534142812990497518157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6797515428335949320096837 1274534142812990497518157)
                ·
                  refine ⟨477950303554871436569309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274534142812990497518157 477950303554871436569309)
                  ·
                    rfl

theorem cell21_2094311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].length) (baseStart_2094311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094311 prefixEnd_2094311 := by exact prefixLift 2094311
  have htrace : WordTrace (prefixWord ++ tailWord_2094311) baseStart_2094311 baseEnd_2094311 := by
    simpa [prefixWord, tailWord_2094311, baseEnd_2094311] using wordTrace_append hprefix tailTrace_2094311
  have hstable : (prefixWord ++ tailWord_2094311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094311).length < 2 ^ (prefixWord ++ tailWord_2094311).sum := by decide
  have hdescent : baseEnd_2094311 < baseStart_2094311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094370 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2094370 : Nat := 118140960795 + 2094370 * 2 ^ 59
def prefixEnd_2094370 : Nat := 4983230072969 + 3 ^ 40 * 2094370 * 2
def baseEnd_2094370 : Nat := 477963768158700445085855

theorem tailTrace_2094370 : CollatzResearch.WordTrace tailWord_2094370 prefixEnd_2094370 477963768158700445085855 := by
  unfold tailWord_2094370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096987355615663690990141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50925299614975103175973709 19096987355615663690990141)
  ·
    refine ⟨7161370258355873884121303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19096987355615663690990141 7161370258355873884121303)
    ·
      refine ⟨10742055387533810826181955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161370258355873884121303 10742055387533810826181955)
      ·
        refine ⟨16113083081300716239272933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10742055387533810826181955 16113083081300716239272933)
        ·
          refine ⟨3021203077743884294863675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16113083081300716239272933 3021203077743884294863675)
          ·
            refine ⟨4531804616615826442295513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021203077743884294863675 4531804616615826442295513)
            ·
              refine ⟨3398853462461869831721635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531804616615826442295513 3398853462461869831721635)
              ·
                refine ⟨5098280193692804747582453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398853462461869831721635 5098280193692804747582453)
                ·
                  refine ⟨477963768158700445085855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5098280193692804747582453 477963768158700445085855)
                  ·
                    rfl

theorem cell21_2094370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2094370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094370 prefixEnd_2094370 := by exact prefixLift 2094370
  have htrace : WordTrace (prefixWord ++ tailWord_2094370) baseStart_2094370 baseEnd_2094370 := by
    simpa [prefixWord, tailWord_2094370, baseEnd_2094370] using wordTrace_append hprefix tailTrace_2094370
  have hstable : (prefixWord ++ tailWord_2094370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094370).length < 2 ^ (prefixWord ++ tailWord_2094370).sum := by decide
  have hdescent : baseEnd_2094370 < baseStart_2094370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094384 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_2094384 : Nat := 118140960795 + 2094384 * 2 ^ 59
def prefixEnd_2094384 : Nat := 4983230072969 + 3 ^ 40 * 2094384 * 2
def baseEnd_2094384 : Nat := 477966963149439531852493

theorem tailTrace_2094384 : CollatzResearch.WordTrace tailWord_2094384 prefixEnd_2094384 477966963149439531852493 := by
  unfold tailWord_2094384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38194230022205967577485103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50925640029607956769980137 38194230022205967577485103)
  ·
    refine ⟨57291345033308951366227655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38194230022205967577485103 57291345033308951366227655)
    ·
      refine ⟨85937017549963427049341483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57291345033308951366227655 85937017549963427049341483)
      ·
        refine ⟨128905526324945140574012225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85937017549963427049341483 128905526324945140574012225)
        ·
          refine ⟨96679144743708855430509169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128905526324945140574012225 96679144743708855430509169)
          ·
            refine ⟨72509358557781641572881877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96679144743708855430509169 72509358557781641572881877)
            ·
              refine ⟨1699438091198007224364419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 72509358557781641572881877 1699438091198007224364419)
              ·
                refine ⟨2549157136797010836546629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699438091198007224364419 2549157136797010836546629)
                ·
                  refine ⟨477966963149439531852493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549157136797010836546629 477966963149439531852493)
                  ·
                    rfl

theorem cell21_2094384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_2094384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094384 prefixEnd_2094384 := by exact prefixLift 2094384
  have htrace : WordTrace (prefixWord ++ tailWord_2094384) baseStart_2094384 baseEnd_2094384 := by
    simpa [prefixWord, tailWord_2094384, baseEnd_2094384] using wordTrace_append hprefix tailTrace_2094384
  have hstable : (prefixWord ++ tailWord_2094384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094384).length < 2 ^ (prefixWord ++ tailWord_2094384).sum := by decide
  have hdescent : baseEnd_2094384 < baseStart_2094384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094390 : List Nat := [5, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2094390 : Nat := 118140960795 + 2094390 * 2 ^ 59
def prefixEnd_2094390 : Nat := 4983230072969 + 3 ^ 40 * 2094390 * 2
def baseEnd_2094390 : Nat := 159322777477061618250827

theorem tailTrace_2094390 : CollatzResearch.WordTrace tailWord_2094390 prefixEnd_2094390 159322777477061618250827 := by
  unfold tailWord_2094390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774292430149387386230539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50925785921593465453125749 4774292430149387386230539)
  ·
    refine ⟨7161438645224081079345809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774292430149387386230539 7161438645224081079345809)
    ·
      refine ⟨5371078983918060809509357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7161438645224081079345809 5371078983918060809509357)
      ·
        refine ⟨2014154618969272803566009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5371078983918060809509357 2014154618969272803566009)
        ·
          refine ⟨1510615964226954602674507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014154618969272803566009 1510615964226954602674507)
          ·
            refine ⟨2265923946340431904011761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510615964226954602674507 2265923946340431904011761)
            ·
              refine ⟨1699442959755323928008821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265923946340431904011761 1699442959755323928008821)
              ·
                refine ⟨159322777477061618250827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699442959755323928008821 159322777477061618250827)
                ·
                  rfl

theorem cell21_2094390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2094390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094390 prefixEnd_2094390 := by exact prefixLift 2094390
  have htrace : WordTrace (prefixWord ++ tailWord_2094390) baseStart_2094390 baseEnd_2094390 := by
    simpa [prefixWord, tailWord_2094390, baseEnd_2094390] using wordTrace_append hprefix tailTrace_2094390
  have hstable : (prefixWord ++ tailWord_2094390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094390).length < 2 ^ (prefixWord ++ tailWord_2094390).sum := by decide
  have hdescent : baseEnd_2094390 < baseStart_2094390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094398 : List Nat := [4, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2094398 : Nat := 118140960795 + 2094398 * 2 ^ 59
def prefixEnd_2094398 : Nat := 4983230072969 + 3 ^ 40 * 2094398 * 2
def baseEnd_2094398 : Nat := 159323386046726206206377

theorem tailTrace_2094398 : CollatzResearch.WordTrace tailWord_2094398 prefixEnd_2094398 159323386046726206206377 := by
  unfold tailWord_2094398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548621333295151943247481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50925980444240810363986565 9548621333295151943247481)
  ·
    refine ⟨7161465999971363957435611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9548621333295151943247481 7161465999971363957435611)
    ·
      refine ⟨10742198999957045936153417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161465999971363957435611 10742198999957045936153417)
      ·
        refine ⟨8056649249967784452115063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10742198999957045936153417 8056649249967784452115063)
        ·
          refine ⟨12084973874951676678172595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8056649249967784452115063 12084973874951676678172595)
          ·
            refine ⟨18127460812427515017258893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12084973874951676678172595 18127460812427515017258893)
            ·
              refine ⟨6797797804660318131472085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18127460812427515017258893 6797797804660318131472085)
              ·
                refine ⟨159323386046726206206377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6797797804660318131472085 159323386046726206206377)
                ·
                  rfl

theorem cell21_2094398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2094398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094398 prefixEnd_2094398 := by exact prefixLift 2094398
  have htrace : WordTrace (prefixWord ++ tailWord_2094398) baseStart_2094398 baseEnd_2094398 := by
    simpa [prefixWord, tailWord_2094398, baseEnd_2094398] using wordTrace_append hprefix tailTrace_2094398
  have hstable : (prefixWord ++ tailWord_2094398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094398).length < 2 ^ (prefixWord ++ tailWord_2094398).sum := by decide
  have hdescent : baseEnd_2094398 < baseStart_2094398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094404 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_2094404 : Nat := 118140960795 + 2094404 * 2 ^ 59
def prefixEnd_2094404 : Nat := 4983230072969 + 3 ^ 40 * 2094404 * 2
def baseEnd_2094404 : Nat := 477971527421923941519119

theorem tailTrace_2094404 : CollatzResearch.WordTrace tailWord_2094404 prefixEnd_2094404 477971527421923941519119 := by
  unfold tailWord_2094404
  simp only [CollatzResearch.WordTrace]
  refine ⟨38194594752169739285349133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50926126336226319047132177 38194594752169739285349133)
  ·
    refine ⟨14322973032063652232005925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38194594752169739285349133 14322973032063652232005925)
    ·
      refine ⟨2685557443511934793501111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14322973032063652232005925 2685557443511934793501111)
      ·
        refine ⟨4028336165267902190251667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685557443511934793501111 4028336165267902190251667)
        ·
          refine ⟨6042504247901853285377501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028336165267902190251667 6042504247901853285377501)
          ·
            refine ⟨2265939092963194982016563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6042504247901853285377501 2265939092963194982016563)
            ·
              refine ⟨3398908639444792473024845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265939092963194982016563 3398908639444792473024845)
              ·
                refine ⟨1274590739791797177384317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3398908639444792473024845 1274590739791797177384317)
                ·
                  refine ⟨477971527421923941519119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274590739791797177384317 477971527421923941519119)
                  ·
                    rfl

theorem cell21_2094404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_2094404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094404 prefixEnd_2094404 := by exact prefixLift 2094404
  have htrace : WordTrace (prefixWord ++ tailWord_2094404) baseStart_2094404 baseEnd_2094404 := by
    simpa [prefixWord, tailWord_2094404, baseEnd_2094404] using wordTrace_append hprefix tailTrace_2094404
  have hstable : (prefixWord ++ tailWord_2094404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094404).length < 2 ^ (prefixWord ++ tailWord_2094404).sum := by decide
  have hdescent : baseEnd_2094404 < baseStart_2094404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094457 : List Nat := [1, 2, 1, 3, 2, 1, 4, 7]
def baseStart_2094457 : Nat := 118140960795 + 2094457 * 2 ^ 59
def prefixEnd_2094457 : Nat := 4983230072969 + 3 ^ 40 * 2094457 * 2
def baseEnd_2094457 : Nat := 159327874248002542378559

theorem tailTrace_2094457 : CollatzResearch.WordTrace tailWord_2094457 prefixEnd_2094457 159327874248002542378559 := by
  unfold tailWord_2094457
  simp only [CollatzResearch.WordTrace]
  refine ⟨76391122573147468622377625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50927415048764979081585083 76391122573147468622377625)
  ·
    refine ⟨57293341929860601466783219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76391122573147468622377625 57293341929860601466783219)
    ·
      refine ⟨85940012894790902200174829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57293341929860601466783219 85940012894790902200174829)
      ·
        refine ⟨32227504835546588325065561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85940012894790902200174829 32227504835546588325065561)
        ·
          refine ⟨24170628626659941243799171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32227504835546588325065561 24170628626659941243799171)
          ·
            refine ⟨36255942939989911865698757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24170628626659941243799171 36255942939989911865698757)
            ·
              refine ⟨6797989301248108474818517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36255942939989911865698757 6797989301248108474818517)
              ·
                refine ⟨159327874248002542378559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6797989301248108474818517 159327874248002542378559)
                ·
                  rfl

theorem cell21_2094457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_2094457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094457 prefixEnd_2094457 := by exact prefixLift 2094457
  have htrace : WordTrace (prefixWord ++ tailWord_2094457) baseStart_2094457 baseEnd_2094457 := by
    simpa [prefixWord, tailWord_2094457, baseEnd_2094457] using wordTrace_append hprefix tailTrace_2094457
  have hstable : (prefixWord ++ tailWord_2094457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094457).length < 2 ^ (prefixWord ++ tailWord_2094457).sum := by decide
  have hdescent : baseEnd_2094457 < baseStart_2094457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094567 : List Nat := [1, 1, 5, 2, 1, 4, 2, 5]
def baseStart_2094567 : Nat := 118140960795 + 2094567 * 2 ^ 59
def prefixEnd_2094567 : Nat := 4983230072969 + 3 ^ 40 * 2094567 * 2
def baseEnd_2094567 : Nat := 159336242080890626767373

theorem tailTrace_2094567 : CollatzResearch.WordTrace tailWord_2094567 prefixEnd_2094567 159336242080890626767373 := by
  unfold tailWord_2094567
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395134602748957408881955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50930089735165971605921303 76395134602748957408881955)
  ·
    refine ⟨114592701904123436113322933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76395134602748957408881955 114592701904123436113322933)
    ·
      refine ⟨10743065803511572135624025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114592701904123436113322933 10743065803511572135624025)
      ·
        refine ⟨8057299352633679101718019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10743065803511572135624025 8057299352633679101718019)
        ·
          refine ⟨12085949028950518652577029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057299352633679101718019 12085949028950518652577029)
          ·
            refine ⟨2266115442928222247358193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12085949028950518652577029 2266115442928222247358193)
            ·
              refine ⟨1699586582196166685518645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266115442928222247358193 1699586582196166685518645)
              ·
                refine ⟨159336242080890626767373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699586582196166685518645 159336242080890626767373)
                ·
                  rfl

theorem cell21_2094567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].length) (baseStart_2094567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094567 prefixEnd_2094567 := by exact prefixLift 2094567
  have htrace : WordTrace (prefixWord ++ tailWord_2094567) baseStart_2094567 baseEnd_2094567 := by
    simpa [prefixWord, tailWord_2094567, baseEnd_2094567] using wordTrace_append hprefix tailTrace_2094567
  have hstable : (prefixWord ++ tailWord_2094567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094567).length < 2 ^ (prefixWord ++ tailWord_2094567).sum := by decide
  have hdescent : baseEnd_2094567 < baseStart_2094567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094609 : List Nat := [1, 2, 2, 1, 1, 2, 6, 6]
def baseStart_2094609 : Nat := 118140960795 + 2094609 * 2 ^ 59
def prefixEnd_2094609 : Nat := 4983230072969 + 3 ^ 40 * 2094609 * 2
def baseEnd_2094609 : Nat := 159339437071629713534011

theorem tailTrace_2094609 : CollatzResearch.WordTrace tailWord_2094609 prefixEnd_2094609 159339437071629713534011 := by
  unfold tailWord_2094609
  simp only [CollatzResearch.WordTrace]
  refine ⟨76396666468596798581910881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50931110979064532387940587 76396666468596798581910881)
  ·
    refine ⟨57297499851447598936433161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76396666468596798581910881 57297499851447598936433161)
    ·
      refine ⟨42973124888585699202324871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57297499851447598936433161 42973124888585699202324871)
      ·
        refine ⟨64459687332878548803487307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42973124888585699202324871 64459687332878548803487307)
        ·
          refine ⟨96689530999317823205230961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64459687332878548803487307 96689530999317823205230961)
          ·
            refine ⟨72517148249488367403923221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96689530999317823205230961 72517148249488367403923221)
            ·
              refine ⟨3399241324194767222058901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72517148249488367403923221 3399241324194767222058901)
              ·
                refine ⟨159339437071629713534011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3399241324194767222058901 159339437071629713534011)
                ·
                  rfl

theorem cell21_2094609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_2094609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094609 prefixEnd_2094609 := by exact prefixLift 2094609
  have htrace : WordTrace (prefixWord ++ tailWord_2094609) baseStart_2094609 baseEnd_2094609 := by
    simpa [prefixWord, tailWord_2094609, baseEnd_2094609] using wordTrace_append hprefix tailTrace_2094609
  have hstable : (prefixWord ++ tailWord_2094609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094609).length < 2 ^ (prefixWord ++ tailWord_2094609).sum := by decide
  have hdescent : baseEnd_2094609 < baseStart_2094609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2094702 : List Nat := [4, 1, 2, 2, 3, 1, 8]
def baseStart_2094702 : Nat := 118140960795 + 2094702 * 2 ^ 59
def prefixEnd_2094702 : Nat := 4983230072969 + 3 ^ 40 * 2094702 * 2
def baseEnd_2094702 : Nat := 53115503897993516172427

theorem tailTrace_2094702 : CollatzResearch.WordTrace tailWord_2094702 prefixEnd_2094702 53115503897993516172427 := by
  unfold tailWord_2094702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550007307157484433130795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50933372304839916976697573 9550007307157484433130795)
  ·
    refine ⟨14325010960736226649696193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550007307157484433130795 14325010960736226649696193)
    ·
      refine ⟨10743758220552169987272145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14325010960736226649696193 10743758220552169987272145)
      ·
        refine ⟨8057818665414127490454109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10743758220552169987272145 8057818665414127490454109)
        ·
          refine ⟨3021681999530297808920291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8057818665414127490454109 3021681999530297808920291)
          ·
            refine ⟨4532522999295446713380437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021681999530297808920291 4532522999295446713380437)
            ·
              refine ⟨53115503897993516172427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4532522999295446713380437 53115503897993516172427)
              ·
                rfl

theorem cell21_2094702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 8].length) (baseStart_2094702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2094702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2094702 prefixEnd_2094702 := by exact prefixLift 2094702
  have htrace : WordTrace (prefixWord ++ tailWord_2094702) baseStart_2094702 baseEnd_2094702 := by
    simpa [prefixWord, tailWord_2094702, baseEnd_2094702] using wordTrace_append hprefix tailTrace_2094702
  have hstable : (prefixWord ++ tailWord_2094702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2094702).length < 2 ^ (prefixWord ++ tailWord_2094702).sum := by decide
  have hdescent : baseEnd_2094702 < baseStart_2094702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2094702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
