import V185TrunkScan23Chunk0055

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_330809 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_330809 : Nat := 118140960795 + 330809 * 2 ^ 59
def prefixEnd_330809 : Nat := 4983230072969 + 3 ^ 40 * 330809 * 2
def baseEnd_330809 : Nat := 56621340611100480655381

theorem tailTrace_330809 : CollatzResearch.WordTrace tailWord_330809 prefixEnd_330809 56621340611100480655381 := by
  unfold tailWord_330809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065595458542965524299481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8043730305695310349532987 12065595458542965524299481)
  ·
    refine ⟨9049196593907224143224611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12065595458542965524299481 9049196593907224143224611)
    ·
      refine ⟨13573794890860836214836917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049196593907224143224611 13573794890860836214836917)
      ·
        refine ⟨1272543271018203395140961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13573794890860836214836917 1272543271018203395140961)
        ·
          refine ⟨954407453263652546355721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272543271018203395140961 954407453263652546355721)
          ·
            refine ⟨715805589947739409766791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954407453263652546355721 715805589947739409766791)
            ·
              refine ⟨1073708384921609114650187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715805589947739409766791 1073708384921609114650187)
              ·
                refine ⟨1610562577382413671975281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073708384921609114650187 1610562577382413671975281)
                ·
                  refine ⟨1207921933036810253981461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610562577382413671975281 1207921933036810253981461)
                  ·
                    refine ⟨56621340611100480655381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1207921933036810253981461 56621340611100480655381)
                    ·
                      rfl

theorem cell23_330809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_330809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330809 prefixEnd_330809 := by exact prefixLift 330809
  have htrace : WordTrace (prefixWord ++ tailWord_330809) baseStart_330809 baseEnd_330809 := by
    simpa [prefixWord, tailWord_330809, baseEnd_330809] using wordTrace_append hprefix tailTrace_330809
  have hstable : (prefixWord ++ tailWord_330809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330809).length < 2 ^ (prefixWord ++ tailWord_330809).sum := by decide
  have hdescent : baseEnd_330809 < baseStart_330809 := by decide
  rcases family_descends (prefixWord ++ tailWord_330809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330816 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2]
def baseStart_330816 : Nat := 118140960795 + 330816 * 2 ^ 59
def prefixEnd_330816 : Nat := 4983230072969 + 3 ^ 40 * 330816 * 2
def baseEnd_330816 : Nat := 169867616197882914578611

theorem tailTrace_330816 : CollatzResearch.WordTrace tailWord_330816 prefixEnd_330816 169867616197882914578611 := by
  unfold tailWord_330816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032925384758802859902151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8043900513011737146536201 6032925384758802859902151)
  ·
    refine ⟨9049388077138204289853227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6032925384758802859902151 9049388077138204289853227)
    ·
      refine ⟨13574082115707306434779841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049388077138204289853227 13574082115707306434779841)
      ·
        refine ⟨10180561586780479826084881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13574082115707306434779841 10180561586780479826084881)
        ·
          refine ⟨7635421190085359869563661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10180561586780479826084881 7635421190085359869563661)
          ·
            refine ⟨2863282946282009951086373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7635421190085359869563661 2863282946282009951086373)
            ·
              refine ⟨536865552427876865828695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2863282946282009951086373 536865552427876865828695)
              ·
                refine ⟨805298328641815298743043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536865552427876865828695 805298328641815298743043)
                ·
                  refine ⟨1207947492962722948114565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805298328641815298743043 1207947492962722948114565)
                  ·
                    refine ⟨226490154930510552771481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1207947492962722948114565 226490154930510552771481)
                    ·
                      refine ⟨169867616197882914578611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226490154930510552771481 169867616197882914578611)
                      ·
                        rfl

theorem cell23_330816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_330816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330816 prefixEnd_330816 := by exact prefixLift 330816
  have htrace : WordTrace (prefixWord ++ tailWord_330816) baseStart_330816 baseEnd_330816 := by
    simpa [prefixWord, tailWord_330816, baseEnd_330816] using wordTrace_append hprefix tailTrace_330816
  have hstable : (prefixWord ++ tailWord_330816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330816).length < 2 ^ (prefixWord ++ tailWord_330816).sum := by decide
  have hdescent : baseEnd_330816 < baseStart_330816 := by decide
  rcases family_descends (prefixWord ++ tailWord_330816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330849 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_330849 : Nat := 118140960795 + 330849 * 2 ^ 59
def prefixEnd_330849 : Nat := 4983230072969 + 3 ^ 40 * 330849 * 2
def baseEnd_330849 : Nat := 169884561059481285465959

theorem tailTrace_330849 : CollatzResearch.WordTrace tailWord_330849 prefixEnd_330849 169884561059481285465959 := by
  unfold tailWord_330849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067054378398052355755601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8044702918932034903837067 12067054378398052355755601)
  ·
    refine ⟨9050290783798539266816701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12067054378398052355755601 9050290783798539266816701)
    ·
      refine ⟨3393859043924452225056263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9050290783798539266816701 3393859043924452225056263)
      ·
        refine ⟨5090788565886678337584395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393859043924452225056263 5090788565886678337584395)
        ·
          refine ⟨7636182848830017506376593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090788565886678337584395 7636182848830017506376593)
          ·
            refine ⟨5727137136622513129782445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7636182848830017506376593 5727137136622513129782445)
            ·
              refine ⟨2147676426233442423668417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5727137136622513129782445 2147676426233442423668417)
              ·
                refine ⟨1610757319675081817751313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147676426233442423668417 1610757319675081817751313)
                ·
                  refine ⟨1208067989756311363313485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610757319675081817751313 1208067989756311363313485)
                  ·
                    refine ⟨453025496158616761242557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208067989756311363313485 453025496158616761242557)
                    ·
                      refine ⟨169884561059481285465959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453025496158616761242557 169884561059481285465959)
                      ·
                        rfl

theorem cell23_330849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_330849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330849 prefixEnd_330849 := by exact prefixLift 330849
  have htrace : WordTrace (prefixWord ++ tailWord_330849) baseStart_330849 baseEnd_330849 := by
    simpa [prefixWord, tailWord_330849, baseEnd_330849] using wordTrace_append hprefix tailTrace_330849
  have hstable : (prefixWord ++ tailWord_330849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330849).length < 2 ^ (prefixWord ++ tailWord_330849).sum := by decide
  have hdescent : baseEnd_330849 < baseStart_330849 := by decide
  rcases family_descends (prefixWord ++ tailWord_330849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330850 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_330850 : Nat := 118140960795 + 330850 * 2 ^ 59
def prefixEnd_330850 : Nat := 4983230072969 + 3 ^ 40 * 330850 * 2
def baseEnd_330850 : Nat := 169885074540135781553455

theorem tailTrace_330850 : CollatzResearch.WordTrace tailWord_330850 prefixEnd_330850 169885074540135781553455 := by
  unfold tailWord_330850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016772712848607381635501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8044727234262953017694669 3016772712848607381635501)
  ·
    refine ⟨1131289767318227768113313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3016772712848607381635501 1131289767318227768113313)
    ·
      refine ⟨848467325488670826084985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131289767318227768113313 848467325488670826084985)
      ·
        refine ⟨636350494116503119563739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848467325488670826084985 636350494116503119563739)
        ·
          refine ⟨954525741174754679345609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636350494116503119563739 954525741174754679345609)
          ·
            refine ⟨715894305881066009509207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954525741174754679345609 715894305881066009509207)
            ·
              refine ⟨1073841458821599014263811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715894305881066009509207 1073841458821599014263811)
              ·
                refine ⟨1610762188232398521395717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073841458821599014263811 1610762188232398521395717)
                ·
                  refine ⟨302017910293574722761697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610762188232398521395717 302017910293574722761697)
                  ·
                    refine ⟨226513432720181042071273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302017910293574722761697 226513432720181042071273)
                    ·
                      refine ⟨169885074540135781553455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226513432720181042071273 169885074540135781553455)
                      ·
                        rfl

theorem cell23_330850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_330850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330850 prefixEnd_330850 := by exact prefixLift 330850
  have htrace : WordTrace (prefixWord ++ tailWord_330850) baseStart_330850 baseEnd_330850 := by
    simpa [prefixWord, tailWord_330850, baseEnd_330850] using wordTrace_append hprefix tailTrace_330850
  have hstable : (prefixWord ++ tailWord_330850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330850).length < 2 ^ (prefixWord ++ tailWord_330850).sum := by decide
  have hdescent : baseEnd_330850 < baseStart_330850 := by decide
  rcases family_descends (prefixWord ++ tailWord_330850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330889 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_330889 : Nat := 118140960795 + 330889 * 2 ^ 59
def prefixEnd_330889 : Nat := 4983230072969 + 3 ^ 40 * 330889 * 2
def baseEnd_330889 : Nat := 169905100285661128965775

theorem tailTrace_330889 : CollatzResearch.WordTrace tailWord_330889 prefixEnd_330889 169905100285661128965775 := by
  unfold tailWord_330889
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068513298253139187211721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8045675532168759458141147 12068513298253139187211721)
  ·
    refine ⟨9051384973689854390408791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12068513298253139187211721 9051384973689854390408791)
    ·
      refine ⟨13577077460534781585613187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051384973689854390408791 13577077460534781585613187)
      ·
        refine ⟨20365616190802172378419781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577077460534781585613187 20365616190802172378419781)
        ·
          refine ⟨3818553035775407320953709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20365616190802172378419781 3818553035775407320953709)
          ·
            refine ⟨1431957388415777745357641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3818553035775407320953709 1431957388415777745357641)
            ·
              refine ⟨1073968041311833309018231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431957388415777745357641 1073968041311833309018231)
              ·
                refine ⟨1610952061967749963527347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073968041311833309018231 1610952061967749963527347)
                ·
                  refine ⟨2416428092951624945291021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610952061967749963527347 2416428092951624945291021)
                  ·
                    refine ⟨906160534856859354484133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2416428092951624945291021 906160534856859354484133)
                    ·
                      refine ⟨169905100285661128965775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 906160534856859354484133 169905100285661128965775)
                      ·
                        rfl

theorem cell23_330889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_330889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330889 prefixEnd_330889 := by exact prefixLift 330889
  have htrace : WordTrace (prefixWord ++ tailWord_330889) baseStart_330889 baseEnd_330889 := by
    simpa [prefixWord, tailWord_330889, baseEnd_330889] using wordTrace_append hprefix tailTrace_330889
  have hstable : (prefixWord ++ tailWord_330889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330889).length < 2 ^ (prefixWord ++ tailWord_330889).sum := by decide
  have hdescent : baseEnd_330889 < baseStart_330889 := by decide
  rcases family_descends (prefixWord ++ tailWord_330889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330899 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 5, 4]
def baseStart_330899 : Nat := 118140960795 + 330899 * 2 ^ 59
def prefixEnd_330899 : Nat := 4983230072969 + 3 ^ 40 * 330899 * 2
def baseEnd_330899 : Nat := 56636745030735363280243

theorem tailTrace_330899 : CollatzResearch.WordTrace tailWord_330899 prefixEnd_330899 56636745030735363280243 := by
  unfold tailWord_330899
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068878028216910895075751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8045918685477940596717167 12068878028216910895075751)
  ·
    refine ⟨18103317042325366342613627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12068878028216910895075751 18103317042325366342613627)
    ·
      refine ⟨27154975563488049513920441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18103317042325366342613627 27154975563488049513920441)
      ·
        refine ⟨20366231672616037135440331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27154975563488049513920441 20366231672616037135440331)
        ·
          refine ⟨30549347508924055703160497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366231672616037135440331 30549347508924055703160497)
          ·
            refine ⟨22912010631693041777370373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30549347508924055703160497 22912010631693041777370373)
            ·
              refine ⟨4296001993442445333256945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22912010631693041777370373 4296001993442445333256945)
              ·
                refine ⟨3222001495081833999942709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296001993442445333256945 3222001495081833999942709)
                ·
                  refine ⟨302062640163921937494629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3222001495081833999942709 302062640163921937494629)
                  ·
                    refine ⟨56636745030735363280243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302062640163921937494629 56636745030735363280243)
                    ·
                      rfl

theorem cell23_330899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 4].length) (baseStart_330899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330899 prefixEnd_330899 := by exact prefixLift 330899
  have htrace : WordTrace (prefixWord ++ tailWord_330899) baseStart_330899 baseEnd_330899 := by
    simpa [prefixWord, tailWord_330899, baseEnd_330899] using wordTrace_append hprefix tailTrace_330899
  have hstable : (prefixWord ++ tailWord_330899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330899).length < 2 ^ (prefixWord ++ tailWord_330899).sum := by decide
  have hdescent : baseEnd_330899 < baseStart_330899 := by decide
  rcases family_descends (prefixWord ++ tailWord_330899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330906 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_330906 : Nat := 118140960795 + 330906 * 2 ^ 59
def prefixEnd_330906 : Nat := 4983230072969 + 3 ^ 40 * 330906 * 2
def baseEnd_330906 : Nat := 169913829456787562453197

theorem tailTrace_330906 : CollatzResearch.WordTrace tailWord_330906 prefixEnd_330906 169913829456787562453197 := by
  unfold tailWord_330906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3017283334797887772645143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8046088892794367393720381 3017283334797887772645143)
  ·
    refine ⟨4525925002196831658967715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3017283334797887772645143 4525925002196831658967715)
    ·
      refine ⟨6788887503295247488451573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525925002196831658967715 6788887503295247488451573)
      ·
        refine ⟨636458203433929452042335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6788887503295247488451573 636458203433929452042335)
        ·
          refine ⟨954687305150894178063503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636458203433929452042335 954687305150894178063503)
          ·
            refine ⟨1432030957726341267095255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954687305150894178063503 1432030957726341267095255)
            ·
              refine ⟨2148046436589511900642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432030957726341267095255 2148046436589511900642883)
              ·
                refine ⟨3222069654884267850964325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148046436589511900642883 3222069654884267850964325)
                ·
                  refine ⟨604138060290800222055811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3222069654884267850964325 604138060290800222055811)
                  ·
                    refine ⟨906207090436200333083717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604138060290800222055811 906207090436200333083717)
                    ·
                      refine ⟨169913829456787562453197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 906207090436200333083717 169913829456787562453197)
                      ·
                        rfl

theorem cell23_330906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_330906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330906 prefixEnd_330906 := by exact prefixLift 330906
  have htrace : WordTrace (prefixWord ++ tailWord_330906) baseStart_330906 baseEnd_330906 := by
    simpa [prefixWord, tailWord_330906, baseEnd_330906] using wordTrace_append hprefix tailTrace_330906
  have hstable : (prefixWord ++ tailWord_330906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330906).length < 2 ^ (prefixWord ++ tailWord_330906).sum := by decide
  have hdescent : baseEnd_330906 < baseStart_330906 := by decide
  rcases family_descends (prefixWord ++ tailWord_330906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_330999 : Nat := 118140960795 + 330999 * 2 ^ 59
def prefixEnd_330999 : Nat := 4983230072969 + 3 ^ 40 * 330999 * 2
def baseEnd_330999 : Nat := 169961583157655698590269

theorem tailTrace_330999 : CollatzResearch.WordTrace tailWord_330999 prefixEnd_330999 169961583157655698590269 := by
  unfold tailWord_330999
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072525327854627973716051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8048350218569751982477367 12072525327854627973716051)
  ·
    refine ⟨18108787991781941960574077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12072525327854627973716051 18108787991781941960574077)
    ·
      refine ⟨6790795496918228235215279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18108787991781941960574077 6790795496918228235215279)
      ·
        refine ⟨10186193245377342352822919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790795496918228235215279 10186193245377342352822919)
        ·
          refine ⟨15279289868066013529234379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186193245377342352822919 15279289868066013529234379)
          ·
            refine ⟨22918934802099020293851569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15279289868066013529234379 22918934802099020293851569)
            ·
              refine ⟨17189201101574265220388677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22918934802099020293851569 17189201101574265220388677)
              ·
                refine ⟨3222975206545174728822877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17189201101574265220388677 3222975206545174728822877)
                ·
                  refine ⟨1208615702454440523308579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3222975206545174728822877 1208615702454440523308579)
                  ·
                    refine ⟨1812923553681660784962869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1208615702454440523308579 1812923553681660784962869)
                    ·
                      refine ⟨169961583157655698590269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1812923553681660784962869 169961583157655698590269)
                      ·
                        rfl

theorem cell23_330999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_330999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330999 prefixEnd_330999 := by exact prefixLift 330999
  have htrace : WordTrace (prefixWord ++ tailWord_330999) baseStart_330999 baseEnd_330999 := by
    simpa [prefixWord, tailWord_330999, baseEnd_330999] using wordTrace_append hprefix tailTrace_330999
  have hstable : (prefixWord ++ tailWord_330999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330999).length < 2 ^ (prefixWord ++ tailWord_330999).sum := by decide
  have hdescent : baseEnd_330999 < baseStart_330999 := by decide
  rcases family_descends (prefixWord ++ tailWord_330999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331010 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_331010 : Nat := 118140960795 + 331010 * 2 ^ 59
def prefixEnd_331010 : Nat := 4983230072969 + 3 ^ 40 * 331010 * 2
def baseEnd_331010 : Nat := 56655743814951718517573

theorem tailTrace_331010 : CollatzResearch.WordTrace tailWord_331010 prefixEnd_331010 56655743814951718517573 := by
  unfold tailWord_331010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018231632703694213091621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8048617687209851234910989 3018231632703694213091621)
  ·
    refine ⟨565918431131942664954679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3018231632703694213091621 565918431131942664954679)
    ·
      refine ⟨848877646697913997432019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565918431131942664954679 848877646697913997432019)
      ·
        refine ⟨1273316470046870996148029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848877646697913997432019 1273316470046870996148029)
        ·
          refine ⟨477493676267576623555511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1273316470046870996148029 477493676267576623555511)
          ·
            refine ⟨716240514401364935333267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477493676267576623555511 716240514401364935333267)
            ·
              refine ⟨1074360771602047402999901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716240514401364935333267 1074360771602047402999901)
              ·
                refine ⟨402885289350767776124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074360771602047402999901 402885289350767776124963)
                ·
                  refine ⟨604327934026151664187445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402885289350767776124963 604327934026151664187445)
                  ·
                    refine ⟨56655743814951718517573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 604327934026151664187445 56655743814951718517573)
                    ·
                      rfl

theorem cell23_331010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_331010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331010 prefixEnd_331010 := by exact prefixLift 331010
  have htrace : WordTrace (prefixWord ++ tailWord_331010) baseStart_331010 baseEnd_331010 := by
    simpa [prefixWord, tailWord_331010, baseEnd_331010] using wordTrace_append hprefix tailTrace_331010
  have hstable : (prefixWord ++ tailWord_331010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331010).length < 2 ^ (prefixWord ++ tailWord_331010).sum := by decide
  have hdescent : baseEnd_331010 < baseStart_331010 := by decide
  rcases family_descends (prefixWord ++ tailWord_331010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331013 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_331013 : Nat := 118140960795 + 331013 * 2 ^ 59
def prefixEnd_331013 : Nat := 4983230072969 + 3 ^ 40 * 331013 * 2
def baseEnd_331013 : Nat := 169968771886818643815205

theorem tailTrace_331013 : CollatzResearch.WordTrace tailWord_331013 prefixEnd_331013 169968771886818643815205 := by
  unfold tailWord_331013
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073035949803908364725693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8048690633202605576483795 12073035949803908364725693)
  ·
    refine ⟨4527388481176465636772135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12073035949803908364725693 4527388481176465636772135)
    ·
      refine ⟨6791082721764698455158203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527388481176465636772135 6791082721764698455158203)
      ·
        refine ⟨10186624082647047682737305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791082721764698455158203 10186624082647047682737305)
        ·
          refine ⟨7639968061985285762052979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10186624082647047682737305 7639968061985285762052979)
          ·
            refine ⟨11459952092977928643079469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639968061985285762052979 11459952092977928643079469)
            ·
              refine ⟨4297482034866723241154801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11459952092977928643079469 4297482034866723241154801)
              ·
                refine ⟨3223111526150042430866101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297482034866723241154801 3223111526150042430866101)
                ·
                  refine ⟨302166705576566477893697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3223111526150042430866101 302166705576566477893697)
                  ·
                    refine ⟨226625029182424858420273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302166705576566477893697 226625029182424858420273)
                    ·
                      refine ⟨169968771886818643815205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226625029182424858420273 169968771886818643815205)
                      ·
                        rfl

theorem cell23_331013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_331013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331013 prefixEnd_331013 := by exact prefixLift 331013
  have htrace : WordTrace (prefixWord ++ tailWord_331013) baseStart_331013 baseEnd_331013 := by
    simpa [prefixWord, tailWord_331013, baseEnd_331013] using wordTrace_append hprefix tailTrace_331013
  have hstable : (prefixWord ++ tailWord_331013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331013).length < 2 ^ (prefixWord ++ tailWord_331013).sum := by decide
  have hdescent : baseEnd_331013 < baseStart_331013 := by decide
  rcases family_descends (prefixWord ++ tailWord_331013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331019 : List Nat := [1, 1, 1, 1, 5, 4, 10]
def baseStart_331019 : Nat := 118140960795 + 331019 * 2 ^ 59
def prefixEnd_331019 : Nat := 4983230072969 + 3 ^ 40 * 331019 * 2
def baseEnd_331019 : Nat := 2098417935441303954817

theorem tailTrace_331019 : CollatzResearch.WordTrace tailWord_331019 prefixEnd_331019 2098417935441303954817 := by
  unfold tailWord_331019
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073254787782171389444111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8048836525188114259629407 12073254787782171389444111)
  ·
    refine ⟨18109882181673257084166167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12073254787782171389444111 18109882181673257084166167)
    ·
      refine ⟨27164823272509885626249251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18109882181673257084166167 27164823272509885626249251)
      ·
        refine ⟨40747234908764828439373877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27164823272509885626249251 40747234908764828439373877)
        ·
          refine ⟨3820053272696702666191301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40747234908764828439373877 3820053272696702666191301)
          ·
            refine ⟨716259988630631749910869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3820053272696702666191301 716259988630631749910869)
            ·
              refine ⟨2098417935441303954817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 716259988630631749910869 2098417935441303954817)
              ·
                rfl

theorem cell23_331019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 10].length) (baseStart_331019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331019 prefixEnd_331019 := by exact prefixLift 331019
  have htrace : WordTrace (prefixWord ++ tailWord_331019) baseStart_331019 baseEnd_331019 := by
    simpa [prefixWord, tailWord_331019, baseEnd_331019] using wordTrace_append hprefix tailTrace_331019
  have hstable : (prefixWord ++ tailWord_331019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331019).length < 2 ^ (prefixWord ++ tailWord_331019).sum := by decide
  have hdescent : baseEnd_331019 < baseStart_331019 := by decide
  rcases family_descends (prefixWord ++ tailWord_331019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331029 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_331029 : Nat := 118140960795 + 331029 * 2 ^ 59
def prefixEnd_331029 : Nat := 4983230072969 + 3 ^ 40 * 331029 * 2
def baseEnd_331029 : Nat := 169976987577290581215131

theorem tailTrace_331029 : CollatzResearch.WordTrace tailWord_331029 prefixEnd_331029 169976987577290581215131 := by
  unfold tailWord_331029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073619517745943097308141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8049079678497295398205427 12073619517745943097308141)
  ·
    refine ⟨4527607319154728661490553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12073619517745943097308141 4527607319154728661490553)
    ·
      refine ⟨3395705489366046496117915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4527607319154728661490553 3395705489366046496117915)
      ·
        refine ⟨5093558234049069744176873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395705489366046496117915 5093558234049069744176873)
        ·
          refine ⟨3820168675536802308132655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093558234049069744176873 3820168675536802308132655)
          ·
            refine ⟨5730253013305203462198983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820168675536802308132655 5730253013305203462198983)
            ·
              refine ⟨8595379519957805193298475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5730253013305203462198983 8595379519957805193298475)
              ·
                refine ⟨12893069279936707789947713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8595379519957805193298475 12893069279936707789947713)
                ·
                  refine ⟨9669801959952530842460785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12893069279936707789947713 9669801959952530842460785)
                  ·
                    refine ⟨7252351469964398131845589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9669801959952530842460785 7252351469964398131845589)
                    ·
                      refine ⟨169976987577290581215131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7252351469964398131845589 169976987577290581215131)
                      ·
                        rfl

theorem cell23_331029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_331029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331029 prefixEnd_331029 := by exact prefixLift 331029
  have htrace : WordTrace (prefixWord ++ tailWord_331029) baseStart_331029 baseEnd_331029 := by
    simpa [prefixWord, tailWord_331029, baseEnd_331029] using wordTrace_append hprefix tailTrace_331029
  have hstable : (prefixWord ++ tailWord_331029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331029).length < 2 ^ (prefixWord ++ tailWord_331029).sum := by decide
  have hdescent : baseEnd_331029 < baseStart_331029 := by decide
  rcases family_descends (prefixWord ++ tailWord_331029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331040 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_331040 : Nat := 118140960795 + 331040 * 2 ^ 59
def prefixEnd_331040 : Nat := 4983230072969 + 3 ^ 40 * 331040 * 2
def baseEnd_331040 : Nat := 56660878621496679392527

theorem tailTrace_331040 : CollatzResearch.WordTrace tailWord_331040 prefixEnd_331040 56660878621496679392527 := by
  unfold tailWord_331040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037010360353045987979287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8049347147137394650639049 6037010360353045987979287)
  ·
    refine ⟨9055515540529568981968931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037010360353045987979287 9055515540529568981968931)
    ·
      refine ⟨13583273310794353472953397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9055515540529568981968931 13583273310794353472953397)
      ·
        refine ⟨1273431872886970638089381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13583273310794353472953397 1273431872886970638089381)
        ·
          refine ⟨238768476166306994641759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1273431872886970638089381 238768476166306994641759)
          ·
            refine ⟨358152714249460491962639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238768476166306994641759 358152714249460491962639)
            ·
              refine ⟨537229071374190737943959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358152714249460491962639 537229071374190737943959)
              ·
                refine ⟨805843607061286106915939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537229071374190737943959 805843607061286106915939)
                ·
                  refine ⟨1208765410591929160373909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805843607061286106915939 1208765410591929160373909)
                  ·
                    refine ⟨56660878621496679392527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1208765410591929160373909 56660878621496679392527)
                    ·
                      rfl

theorem cell23_331040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_331040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331040 prefixEnd_331040 := by exact prefixLift 331040
  have htrace : WordTrace (prefixWord ++ tailWord_331040) baseStart_331040 baseEnd_331040 := by
    simpa [prefixWord, tailWord_331040, baseEnd_331040] using wordTrace_append hprefix tailTrace_331040
  have hstable : (prefixWord ++ tailWord_331040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331040).length < 2 ^ (prefixWord ++ tailWord_331040).sum := by decide
  have hdescent : baseEnd_331040 < baseStart_331040 := by decide
  rcases family_descends (prefixWord ++ tailWord_331040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331043 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 4]
def baseStart_331043 : Nat := 118140960795 + 331043 * 2 ^ 59
def prefixEnd_331043 : Nat := 4983230072969 + 3 ^ 40 * 331043 * 2
def baseEnd_331043 : Nat := 169984176306453526440067

theorem tailTrace_331043 : CollatzResearch.WordTrace tailWord_331043 prefixEnd_331043 169984176306453526440067 := by
  unfold tailWord_331043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074130139695223488317783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8049420093130148992211855 12074130139695223488317783)
  ·
    refine ⟨18111195209542835232476675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12074130139695223488317783 18111195209542835232476675)
    ·
      refine ⟨27166792814314252848715013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18111195209542835232476675 27166792814314252848715013)
      ·
        refine ⟨5093773652683922409134065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27166792814314252848715013 5093773652683922409134065)
        ·
          refine ⟨3820330239512941806850549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093773652683922409134065 3820330239512941806850549)
          ·
            refine ⟨358155959954338294392239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3820330239512941806850549 358155959954338294392239)
            ·
              refine ⟨537233939931507441588359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358155959954338294392239 537233939931507441588359)
              ·
                refine ⟨805850909897261162382539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537233939931507441588359 805850909897261162382539)
                ·
                  refine ⟨1208776364845891743573809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805850909897261162382539 1208776364845891743573809)
                  ·
                    refine ⟨906582273634418807680357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208776364845891743573809 906582273634418807680357)
                    ·
                      refine ⟨169984176306453526440067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 906582273634418807680357 169984176306453526440067)
                      ·
                        rfl

theorem cell23_331043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_331043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331043 prefixEnd_331043 := by exact prefixLift 331043
  have htrace : WordTrace (prefixWord ++ tailWord_331043) baseStart_331043 baseEnd_331043 := by
    simpa [prefixWord, tailWord_331043, baseEnd_331043] using wordTrace_append hprefix tailTrace_331043
  have hstable : (prefixWord ++ tailWord_331043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331043).length < 2 ^ (prefixWord ++ tailWord_331043).sum := by decide
  have hdescent : baseEnd_331043 < baseStart_331043 := by decide
  rcases family_descends (prefixWord ++ tailWord_331043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331050 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_331050 : Nat := 118140960795 + 331050 * 2 ^ 59
def prefixEnd_331050 : Nat := 4983230072969 + 3 ^ 40 * 331050 * 2
def baseEnd_331050 : Nat := 169987770671034999052535

theorem tailTrace_331050 : CollatzResearch.WordTrace tailWord_331050 prefixEnd_331050 169987770671034999052535 := by
  unfold tailWord_331050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018596362667465920955651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8049590300446575789215069 3018596362667465920955651)
  ·
    refine ⟨4527894544001198881433477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018596362667465920955651 4527894544001198881433477)
    ·
      refine ⟨848980227000224790268777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4527894544001198881433477 848980227000224790268777)
      ·
        refine ⟨636735170250168592701583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848980227000224790268777 636735170250168592701583)
        ·
          refine ⟨955102755375252889052375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636735170250168592701583 955102755375252889052375)
          ·
            refine ⟨1432654133062879333578563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955102755375252889052375 1432654133062879333578563)
            ·
              refine ⟨2148981199594319000367845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432654133062879333578563 2148981199594319000367845)
              ·
                refine ⟨402933974923934812568971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148981199594319000367845 402933974923934812568971)
                ·
                  refine ⟨604400962385902218853457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402933974923934812568971 604400962385902218853457)
                  ·
                    refine ⟨453300721789426664140093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604400962385902218853457 453300721789426664140093)
                    ·
                      refine ⟨169987770671034999052535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453300721789426664140093 169987770671034999052535)
                      ·
                        rfl

theorem cell23_331050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_331050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331050 prefixEnd_331050 := by exact prefixLift 331050
  have htrace : WordTrace (prefixWord ++ tailWord_331050) baseStart_331050 baseEnd_331050 := by
    simpa [prefixWord, tailWord_331050, baseEnd_331050] using wordTrace_append hprefix tailTrace_331050
  have hstable : (prefixWord ++ tailWord_331050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331050).length < 2 ^ (prefixWord ++ tailWord_331050).sum := by decide
  have hdescent : baseEnd_331050 < baseStart_331050 := by decide
  rcases family_descends (prefixWord ++ tailWord_331050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331053 : List Nat := [1, 5, 3, 1, 1, 2, 1, 9]
def baseStart_331053 : Nat := 118140960795 + 331053 * 2 ^ 59
def prefixEnd_331053 : Nat := 4983230072969 + 3 ^ 40 * 331053 * 2
def baseEnd_331053 : Nat := 6295900411592536567223

theorem tailTrace_331053 : CollatzResearch.WordTrace tailWord_331053 prefixEnd_331053 6295900411592536567223 := by
  unfold tailWord_331053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12074494869658995196181813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8049663246439330130787875 12074494869658995196181813)
  ·
    refine ⟨1131983894030530799642045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12074494869658995196181813 1131983894030530799642045)
    ·
      refine ⟨424493960261449049865767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1131983894030530799642045 424493960261449049865767)
      ·
        refine ⟨636740940392173574798651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424493960261449049865767 636740940392173574798651)
        ·
          refine ⟨955111410588260362197977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636740940392173574798651 955111410588260362197977)
          ·
            refine ⟨716333557941195271648483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955111410588260362197977 716333557941195271648483)
            ·
              refine ⟨1074500336911792907472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716333557941195271648483 1074500336911792907472725)
              ·
                refine ⟨6295900411592536567223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1074500336911792907472725 6295900411592536567223)
                ·
                  rfl

theorem cell23_331053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 9].length) (baseStart_331053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331053 prefixEnd_331053 := by exact prefixLift 331053
  have htrace : WordTrace (prefixWord ++ tailWord_331053) baseStart_331053 baseEnd_331053 := by
    simpa [prefixWord, tailWord_331053, baseEnd_331053] using wordTrace_append hprefix tailTrace_331053
  have hstable : (prefixWord ++ tailWord_331053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331053).length < 2 ^ (prefixWord ++ tailWord_331053).sum := by decide
  have hdescent : baseEnd_331053 < baseStart_331053 := by decide
  rcases family_descends (prefixWord ++ tailWord_331053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331086 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_331086 : Nat := 118140960795 + 331086 * 2 ^ 59
def prefixEnd_331086 : Nat := 4983230072969 + 3 ^ 40 * 331086 * 2
def baseEnd_331086 : Nat := 170006255974596858202369

theorem tailTrace_331086 : CollatzResearch.WordTrace tailWord_331086 prefixEnd_331086 170006255974596858202369 := by
  unfold tailWord_331086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509462309817430229016639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8050465652359627888088741 1509462309817430229016639)
  ·
    refine ⟨2264193464726145343524959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509462309817430229016639 2264193464726145343524959)
    ·
      refine ⟨3396290197089218015287439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264193464726145343524959 3396290197089218015287439)
      ·
        refine ⟨5094435295633827022931159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396290197089218015287439 5094435295633827022931159)
        ·
          refine ⟨7641652943450740534396739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094435295633827022931159 7641652943450740534396739)
          ·
            refine ⟨11462479415176110801595109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7641652943450740534396739 11462479415176110801595109)
            ·
              refine ⟨2149214890345520775299083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11462479415176110801595109 2149214890345520775299083)
              ·
                refine ⟨3223822335518281162948625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149214890345520775299083 3223822335518281162948625)
                ·
                  refine ⟨2417866751638710872211469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223822335518281162948625 2417866751638710872211469)
                  ·
                    refine ⟨906700031864516577079301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2417866751638710872211469 906700031864516577079301)
                    ·
                      refine ⟨170006255974596858202369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 906700031864516577079301 170006255974596858202369)
                      ·
                        rfl

theorem cell23_331086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_331086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331086 prefixEnd_331086 := by exact prefixLift 331086
  have htrace : WordTrace (prefixWord ++ tailWord_331086) baseStart_331086 baseEnd_331086 := by
    simpa [prefixWord, tailWord_331086, baseEnd_331086] using wordTrace_append hprefix tailTrace_331086
  have hstable : (prefixWord ++ tailWord_331086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331086).length < 2 ^ (prefixWord ++ tailWord_331086).sum := by decide
  have hdescent : baseEnd_331086 < baseStart_331086 := by decide
  rcases family_descends (prefixWord ++ tailWord_331086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331101 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_331101 : Nat := 118140960795 + 331101 * 2 ^ 59
def prefixEnd_331101 : Nat := 4983230072969 + 3 ^ 40 * 331101 * 2
def baseEnd_331101 : Nat := 170013958184414299514801

theorem tailTrace_331101 : CollatzResearch.WordTrace tailWord_331101 prefixEnd_331101 170013958184414299514801 := by
  unfold tailWord_331101
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076245573485099393929157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050830382323399595952771 12076245573485099393929157)
  ·
    refine ⟨2264296045028456136361717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12076245573485099393929157 2264296045028456136361717)
    ·
      refine ⟨212277754221417762783911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2264296045028456136361717 212277754221417762783911)
      ·
        refine ⟨318416631332126644175867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212277754221417762783911 318416631332126644175867)
        ·
          refine ⟨477624946998189966263801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318416631332126644175867 477624946998189966263801)
          ·
            refine ⟨358218710248642474697851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477624946998189966263801 358218710248642474697851)
            ·
              refine ⟨537328065372963712046777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358218710248642474697851 537328065372963712046777)
              ·
                refine ⟨402996049029722784035083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537328065372963712046777 402996049029722784035083)
                ·
                  refine ⟨604494073544584176052625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402996049029722784035083 604494073544584176052625)
                  ·
                    refine ⟨453370555158438132039469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604494073544584176052625 453370555158438132039469)
                    ·
                      refine ⟨170013958184414299514801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453370555158438132039469 170013958184414299514801)
                      ·
                        rfl

theorem cell23_331101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_331101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331101 prefixEnd_331101 := by exact prefixLift 331101
  have htrace : WordTrace (prefixWord ++ tailWord_331101) baseStart_331101 baseEnd_331101 := by
    simpa [prefixWord, tailWord_331101, baseEnd_331101] using wordTrace_append hprefix tailTrace_331101
  have hstable : (prefixWord ++ tailWord_331101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331101).length < 2 ^ (prefixWord ++ tailWord_331101).sum := by decide
  have hdescent : baseEnd_331101 < baseStart_331101 := by decide
  rcases family_descends (prefixWord ++ tailWord_331101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331103 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 1, 4, 2]
def baseStart_331103 : Nat := 118140960795 + 331103 * 2 ^ 59
def prefixEnd_331103 : Nat := 4983230072969 + 3 ^ 40 * 331103 * 2
def baseEnd_331103 : Nat := 170014985145723291689791

theorem tailTrace_331103 : CollatzResearch.WordTrace tailWord_331103 prefixEnd_331103 170014985145723291689791 := by
  unfold tailWord_331103
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076318519477853735501963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050879012985235823667975 12076318519477853735501963)
  ·
    refine ⟨18114477779216780603252945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12076318519477853735501963 18114477779216780603252945)
    ·
      refine ⟨13585858334412585452439709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18114477779216780603252945 13585858334412585452439709)
      ·
        refine ⟨5094696875404719544664891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13585858334412585452439709 5094696875404719544664891)
        ·
          refine ⟨7642045313107079316997337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094696875404719544664891 7642045313107079316997337)
          ·
            refine ⟨5731533984830309487748003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642045313107079316997337 5731533984830309487748003)
            ·
              refine ⟨8597300977245464231622005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731533984830309487748003 8597300977245464231622005)
              ·
                refine ⟨805996966616762271714563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8597300977245464231622005 805996966616762271714563)
                ·
                  refine ⟨1208995449925143407571845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805996966616762271714563 1208995449925143407571845)
                  ·
                    refine ⟨226686646860964388919721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1208995449925143407571845 226686646860964388919721)
                    ·
                      refine ⟨170014985145723291689791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226686646860964388919721 170014985145723291689791)
                      ·
                        rfl

theorem cell23_331103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_331103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331103 prefixEnd_331103 := by exact prefixLift 331103
  have htrace : WordTrace (prefixWord ++ tailWord_331103) baseStart_331103 baseEnd_331103 := by
    simpa [prefixWord, tailWord_331103, baseEnd_331103] using wordTrace_append hprefix tailTrace_331103
  have hstable : (prefixWord ++ tailWord_331103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331103).length < 2 ^ (prefixWord ++ tailWord_331103).sum := by decide
  have hdescent : baseEnd_331103 < baseStart_331103 := by decide
  rcases family_descends (prefixWord ++ tailWord_331103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331107 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 1, 3, 2]
def baseStart_331107 : Nat := 118140960795 + 331107 * 2 ^ 59
def prefixEnd_331107 : Nat := 4983230072969 + 3 ^ 40 * 331107 * 2
def baseEnd_331107 : Nat := 170017039068341276039773

theorem tailTrace_331107 : CollatzResearch.WordTrace tailWord_331107 prefixEnd_331107 170017039068341276039773 := by
  unfold tailWord_331107
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076464411463362418647575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050976274308908279098383 12076464411463362418647575)
  ·
    refine ⟨18114696617195043627971363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12076464411463362418647575 18114696617195043627971363)
    ·
      refine ⟨27172044925792565441957045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18114696617195043627971363 27172044925792565441957045)
      ·
        refine ⟨2547379211793053010183473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27172044925792565441957045 2547379211793053010183473)
        ·
          refine ⟨1910534408844789757637605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2547379211793053010183473 1910534408844789757637605)
          ·
            refine ⟨358225201658398079557051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1910534408844789757637605 358225201658398079557051)
            ·
              refine ⟨537337802487597119335577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358225201658398079557051 537337802487597119335577)
              ·
                refine ⟨403003351865697839501683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537337802487597119335577 403003351865697839501683)
                ·
                  refine ⟨604505027798546759252525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403003351865697839501683 604505027798546759252525)
                  ·
                    refine ⟨226689385424455034719697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 604505027798546759252525 226689385424455034719697)
                    ·
                      refine ⟨170017039068341276039773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226689385424455034719697 170017039068341276039773)
                      ·
                        rfl

theorem cell23_331107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_331107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331107 prefixEnd_331107 := by exact prefixLift 331107
  have htrace : WordTrace (prefixWord ++ tailWord_331107) baseStart_331107 baseEnd_331107 := by
    simpa [prefixWord, tailWord_331107, baseEnd_331107] using wordTrace_append hprefix tailTrace_331107
  have hstable : (prefixWord ++ tailWord_331107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331107).length < 2 ^ (prefixWord ++ tailWord_331107).sum := by decide
  have hdescent : baseEnd_331107 < baseStart_331107 := by decide
  rcases family_descends (prefixWord ++ tailWord_331107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331136 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_331136 : Nat := 118140960795 + 331136 * 2 ^ 59
def prefixEnd_331136 : Nat := 4983230072969 + 3 ^ 40 * 331136 * 2
def baseEnd_331136 : Nat := 170031930007321662577139

theorem tailTrace_331136 : CollatzResearch.WordTrace tailWord_331136 prefixEnd_331136 170031930007321662577139 := by
  unfold tailWord_331136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038761064179150185726631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8051681418905533580968841 6038761064179150185726631)
  ·
    refine ⟨9058141596268725278589947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6038761064179150185726631 9058141596268725278589947)
    ·
      refine ⟨13587212394403087917884921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9058141596268725278589947 13587212394403087917884921)
      ·
        refine ⟨10190409295802315938413691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13587212394403087917884921 10190409295802315938413691)
        ·
          refine ⟨15285613943703473907620537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10190409295802315938413691 15285613943703473907620537)
          ·
            refine ⟨11464210457777605430715403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15285613943703473907620537 11464210457777605430715403)
            ·
              refine ⟨17196315686666408146073105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11464210457777605430715403 17196315686666408146073105)
              ·
                refine ⟨12897236764999806109554829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17196315686666408146073105 12897236764999806109554829)
                ·
                  refine ⟨4836463786874927291083061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12897236764999806109554829 4836463786874927291083061)
                  ·
                    refine ⟨453418480019524433539037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4836463786874927291083061 453418480019524433539037)
                    ·
                      refine ⟨170031930007321662577139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453418480019524433539037 170031930007321662577139)
                      ·
                        rfl

theorem cell23_331136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_331136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331136 prefixEnd_331136 := by exact prefixLift 331136
  have htrace : WordTrace (prefixWord ++ tailWord_331136) baseStart_331136 baseEnd_331136 := by
    simpa [prefixWord, tailWord_331136, baseEnd_331136] using wordTrace_append hprefix tailTrace_331136
  have hstable : (prefixWord ++ tailWord_331136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331136).length < 2 ^ (prefixWord ++ tailWord_331136).sum := by decide
  have hdescent : baseEnd_331136 < baseStart_331136 := by decide
  rcases family_descends (prefixWord ++ tailWord_331136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331150 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_331150 : Nat := 118140960795 + 331150 * 2 ^ 59
def prefixEnd_331150 : Nat := 4983230072969 + 3 ^ 40 * 331150 * 2
def baseEnd_331150 : Nat := 170039118736484607802075

theorem tailTrace_331150 : CollatzResearch.WordTrace tailWord_331150 prefixEnd_331150 170039118736484607802075 := by
  unfold tailWord_331150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509754093788447595307863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8052021833538387174975269 1509754093788447595307863)
  ·
    refine ⟨2264631140682671392961795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509754093788447595307863 2264631140682671392961795)
    ·
      refine ⟨3396946711024007089442693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264631140682671392961795 3396946711024007089442693)
      ·
        refine ⟨636927508317001329270505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3396946711024007089442693 636927508317001329270505)
        ·
          refine ⟨477695631237750996952879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636927508317001329270505 477695631237750996952879)
          ·
            refine ⟨716543446856626495429319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477695631237750996952879 716543446856626495429319)
            ·
              refine ⟨1074815170284939743143979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716543446856626495429319 1074815170284939743143979)
              ·
                refine ⟨1612222755427409614715969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074815170284939743143979 1612222755427409614715969)
                ·
                  refine ⟨1209167066570557211036977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612222755427409614715969 1209167066570557211036977)
                  ·
                    refine ⟨906875299927917908277733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1209167066570557211036977 906875299927917908277733)
                    ·
                      refine ⟨170039118736484607802075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 906875299927917908277733 170039118736484607802075)
                      ·
                        rfl

theorem cell23_331150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_331150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331150 prefixEnd_331150 := by exact prefixLift 331150
  have htrace : WordTrace (prefixWord ++ tailWord_331150) baseStart_331150 baseEnd_331150 := by
    simpa [prefixWord, tailWord_331150, baseEnd_331150] using wordTrace_append hprefix tailTrace_331150
  have hstable : (prefixWord ++ tailWord_331150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331150).length < 2 ^ (prefixWord ++ tailWord_331150).sum := by decide
  have hdescent : baseEnd_331150 < baseStart_331150 := by decide
  rcases family_descends (prefixWord ++ tailWord_331150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331154 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_331154 : Nat := 118140960795 + 331154 * 2 ^ 59
def prefixEnd_331154 : Nat := 4983230072969 + 3 ^ 40 * 331154 * 2
def baseEnd_331154 : Nat := 170041172659102592152057

theorem tailTrace_331154 : CollatzResearch.WordTrace tailWord_331154 prefixEnd_331154 170041172659102592152057 := by
  unfold tailWord_331154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3019544660573272361402129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8052119094862059630405677 3019544660573272361402129)
  ·
    refine ⟨2264658495429954271051597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3019544660573272361402129 2264658495429954271051597)
    ·
      refine ⟨849246935786232851644349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2264658495429954271051597 849246935786232851644349)
      ·
        refine ⟨318467600919837319366631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 849246935786232851644349 318467600919837319366631)
        ·
          refine ⟨477701401379755979049947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318467600919837319366631 477701401379755979049947)
          ·
            refine ⟨716552102069633968574921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477701401379755979049947 716552102069633968574921)
            ·
              refine ⟨537414076552225476431191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716552102069633968574921 537414076552225476431191)
              ·
                refine ⟨806121114828338214646787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537414076552225476431191 806121114828338214646787)
                ·
                  refine ⟨1209181672242507321970181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806121114828338214646787 1209181672242507321970181)
                  ·
                    refine ⟨226721563545470122869409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209181672242507321970181 226721563545470122869409)
                    ·
                      refine ⟨170041172659102592152057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226721563545470122869409 170041172659102592152057)
                      ·
                        rfl

theorem cell23_331154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_331154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331154 prefixEnd_331154 := by exact prefixLift 331154
  have htrace : WordTrace (prefixWord ++ tailWord_331154) baseStart_331154 baseEnd_331154 := by
    simpa [prefixWord, tailWord_331154, baseEnd_331154] using wordTrace_append hprefix tailTrace_331154
  have hstable : (prefixWord ++ tailWord_331154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331154).length < 2 ^ (prefixWord ++ tailWord_331154).sum := by decide
  have hdescent : baseEnd_331154 < baseStart_331154 := by decide
  rcases family_descends (prefixWord ++ tailWord_331154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331203 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 3, 4]
def baseStart_331203 : Nat := 118140960795 + 331203 * 2 ^ 59
def prefixEnd_331203 : Nat := 4983230072969 + 3 ^ 40 * 331203 * 2
def baseEnd_331203 : Nat := 56688777737057633479777

theorem tailTrace_331203 : CollatzResearch.WordTrace tailWord_331203 prefixEnd_331203 56688777737057633479777 := by
  unfold tailWord_331203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079965819115570814142263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8053310546077047209428175 12079965819115570814142263)
  ·
    refine ⟨18119948728673356221213395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12079965819115570814142263 18119948728673356221213395)
    ·
      refine ⟨27179923093010034331820093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18119948728673356221213395 27179923093010034331820093)
      ·
        refine ⟨10192471159878762874432535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27179923093010034331820093 10192471159878762874432535)
        ·
          refine ⟨15288706739818144311648803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192471159878762874432535 15288706739818144311648803)
          ·
            refine ⟨22933060109727216467473205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15288706739818144311648803 22933060109727216467473205)
            ·
              refine ⟨2149974385286926543825613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22933060109727216467473205 2149974385286926543825613)
              ·
                refine ⟨806240394482597453934605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149974385286926543825613 806240394482597453934605)
                ·
                  refine ⟨302340147930974045225477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806240394482597453934605 302340147930974045225477)
                  ·
                    refine ⟨56688777737057633479777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302340147930974045225477 56688777737057633479777)
                    ·
                      rfl

theorem cell23_331203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 4].length) (baseStart_331203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331203 prefixEnd_331203 := by exact prefixLift 331203
  have htrace : WordTrace (prefixWord ++ tailWord_331203) baseStart_331203 baseEnd_331203 := by
    simpa [prefixWord, tailWord_331203, baseEnd_331203] using wordTrace_append hprefix tailTrace_331203
  have hstable : (prefixWord ++ tailWord_331203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331203).length < 2 ^ (prefixWord ++ tailWord_331203).sum := by decide
  have hdescent : baseEnd_331203 < baseStart_331203 := by decide
  rcases family_descends (prefixWord ++ tailWord_331203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331210 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_331210 : Nat := 118140960795 + 331210 * 2 ^ 59
def prefixEnd_331210 : Nat := 4983230072969 + 3 ^ 40 * 331210 * 2
def baseEnd_331210 : Nat := 170069927575754373051799

theorem tailTrace_331210 : CollatzResearch.WordTrace tailWord_331210 prefixEnd_331210 170069927575754373051799 := by
  unfold tailWord_331210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020055282522552752411771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8053480753393474006431389 3020055282522552752411771)
  ·
    refine ⟨4530082923783829128617657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3020055282522552752411771 4530082923783829128617657)
    ·
      refine ⟨3397562192837871846463243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4530082923783829128617657 3397562192837871846463243)
      ·
        refine ⟨5096343289256807769694865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397562192837871846463243 5096343289256807769694865)
        ·
          refine ⟨3822257466942605827271149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096343289256807769694865 3822257466942605827271149)
          ·
            refine ⟨1433346550103477185226681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3822257466942605827271149 1433346550103477185226681)
            ·
              refine ⟨1075009912577607888920011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433346550103477185226681 1075009912577607888920011)
              ·
                refine ⟨1612514868866411833380017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075009912577607888920011 1612514868866411833380017)
                ·
                  refine ⟨1209386151649808875035013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612514868866411833380017 1209386151649808875035013)
                  ·
                    refine ⟨226759903434339164069065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209386151649808875035013 226759903434339164069065)
                    ·
                      refine ⟨170069927575754373051799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226759903434339164069065 170069927575754373051799)
                      ·
                        rfl

theorem cell23_331210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_331210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331210 prefixEnd_331210 := by exact prefixLift 331210
  have htrace : WordTrace (prefixWord ++ tailWord_331210) baseStart_331210 baseEnd_331210 := by
    simpa [prefixWord, tailWord_331210, baseEnd_331210] using wordTrace_append hprefix tailTrace_331210
  have hstable : (prefixWord ++ tailWord_331210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331210).length < 2 ^ (prefixWord ++ tailWord_331210).sum := by decide
  have hdescent : baseEnd_331210 < baseStart_331210 := by decide
  rcases family_descends (prefixWord ++ tailWord_331210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331297 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_331297 : Nat := 118140960795 + 331297 * 2 ^ 59
def prefixEnd_331297 : Nat := 4983230072969 + 3 ^ 40 * 331297 * 2
def baseEnd_331297 : Nat := 56704866797565177554633

theorem tailTrace_331297 : CollatzResearch.WordTrace tailWord_331297 prefixEnd_331297 56704866797565177554633 := by
  unfold tailWord_331297
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083394280775024868064145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8055596187183349912042763 12083394280775024868064145)
  ·
    refine ⟨9062545710581268651048109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12083394280775024868064145 9062545710581268651048109)
    ·
      refine ⟨3398454641467975744143041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9062545710581268651048109 3398454641467975744143041)
      ·
        refine ⟨2548840981100981808107281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3398454641467975744143041 2548840981100981808107281)
        ·
          refine ⟨1911630735825736356080461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2548840981100981808107281 1911630735825736356080461)
          ·
            refine ⟨716861525934651133530173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1911630735825736356080461 716861525934651133530173)
            ·
              refine ⟨268823072225494175073815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 716861525934651133530173 268823072225494175073815)
              ·
                refine ⟨403234608338241262610723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268823072225494175073815 403234608338241262610723)
                ·
                  refine ⟨604851912507361893916085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403234608338241262610723 604851912507361893916085)
                  ·
                    refine ⟨56704866797565177554633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 604851912507361893916085 56704866797565177554633)
                    ·
                      rfl

theorem cell23_331297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_331297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331297 prefixEnd_331297 := by exact prefixLift 331297
  have htrace : WordTrace (prefixWord ++ tailWord_331297) baseStart_331297 baseEnd_331297 := by
    simpa [prefixWord, tailWord_331297, baseEnd_331297] using wordTrace_append hprefix tailTrace_331297
  have hstable : (prefixWord ++ tailWord_331297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331297).length < 2 ^ (prefixWord ++ tailWord_331297).sum := by decide
  have hdescent : baseEnd_331297 < baseStart_331297 := by decide
  rcases family_descends (prefixWord ++ tailWord_331297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331313 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_331313 : Nat := 118140960795 + 331313 * 2 ^ 59
def prefixEnd_331313 : Nat := 4983230072969 + 3 ^ 40 * 331313 * 2
def baseEnd_331313 : Nat := 170122816083167470063825

theorem tailTrace_331313 : CollatzResearch.WordTrace tailWord_331313 prefixEnd_331313 170122816083167470063825 := by
  unfold tailWord_331313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083977848717059600646593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8055985232478039733764395 12083977848717059600646593)
  ·
    refine ⟨9062983386537794700484945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12083977848717059600646593 9062983386537794700484945)
    ·
      refine ⟨6797237539903346025363709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9062983386537794700484945 6797237539903346025363709)
      ·
        refine ⟨2548964077463754759511391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6797237539903346025363709 2548964077463754759511391)
        ·
          refine ⟨3823446116195632139267087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548964077463754759511391 3823446116195632139267087)
          ·
            refine ⟨5735169174293448208900631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823446116195632139267087 5735169174293448208900631)
            ·
              refine ⟨8602753761440172313350947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735169174293448208900631 8602753761440172313350947)
              ·
                refine ⟨12904130642160258470026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602753761440172313350947 12904130642160258470026421)
                ·
                  refine ⟨1209762247702524231564977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12904130642160258470026421 1209762247702524231564977)
                  ·
                    refine ⟨907321685776893173673733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1209762247702524231564977 907321685776893173673733)
                    ·
                      refine ⟨170122816083167470063825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 907321685776893173673733 170122816083167470063825)
                      ·
                        rfl

theorem cell23_331313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_331313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331313 prefixEnd_331313 := by exact prefixLift 331313
  have htrace : WordTrace (prefixWord ++ tailWord_331313) baseStart_331313 baseEnd_331313 := by
    simpa [prefixWord, tailWord_331313, baseEnd_331313] using wordTrace_append hprefix tailTrace_331313
  have hstable : (prefixWord ++ tailWord_331313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331313).length < 2 ^ (prefixWord ++ tailWord_331313).sum := by decide
  have hdescent : baseEnd_331313 < baseStart_331313 := by decide
  rcases family_descends (prefixWord ++ tailWord_331313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331320 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_331320 : Nat := 118140960795 + 331320 * 2 ^ 59
def prefixEnd_331320 : Nat := 4983230072969 + 3 ^ 40 * 331320 * 2
def baseEnd_331320 : Nat := 170126410447748942676293

theorem tailTrace_331320 : CollatzResearch.WordTrace tailWord_331320 prefixEnd_331320 170126410447748942676293 := by
  unfold tailWord_331320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042116579845849898075707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8056155439794466530767609 6042116579845849898075707)
  ·
    refine ⟨9063174869768774847113561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6042116579845849898075707 9063174869768774847113561)
    ·
      refine ⟨6797381152326581135335171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9063174869768774847113561 6797381152326581135335171)
      ·
        refine ⟨10196071728489871703002757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6797381152326581135335171 10196071728489871703002757)
        ·
          refine ⟨1911763449091850944313017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10196071728489871703002757 1911763449091850944313017)
          ·
            refine ⟨1433822586818888208234763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911763449091850944313017 1433822586818888208234763)
            ·
              refine ⟨2150733880228332312352145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433822586818888208234763 2150733880228332312352145)
              ·
                refine ⟨1613050410171249234264109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150733880228332312352145 1613050410171249234264109)
                ·
                  refine ⟨604893903814218462849041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1613050410171249234264109 604893903814218462849041)
                  ·
                    refine ⟨453670427860663847136781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604893903814218462849041 453670427860663847136781)
                    ·
                      refine ⟨170126410447748942676293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453670427860663847136781 170126410447748942676293)
                      ·
                        rfl

theorem cell23_331320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_331320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331320 prefixEnd_331320 := by exact prefixLift 331320
  have htrace : WordTrace (prefixWord ++ tailWord_331320) baseStart_331320 baseEnd_331320 := by
    simpa [prefixWord, tailWord_331320, baseEnd_331320] using wordTrace_append hprefix tailTrace_331320
  have hstable : (prefixWord ++ tailWord_331320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331320).length < 2 ^ (prefixWord ++ tailWord_331320).sum := by decide
  have hdescent : baseEnd_331320 < baseStart_331320 := by decide
  rcases family_descends (prefixWord ++ tailWord_331320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331340 : List Nat := [2, 2, 1, 3, 1, 4, 3, 7]
def baseStart_331340 : Nat := 118140960795 + 331340 * 2 ^ 59
def prefixEnd_331340 : Nat := 4983230072969 + 3 ^ 40 * 331340 * 2
def baseEnd_331340 : Nat := 6301358520771809793563

theorem tailTrace_331340 : CollatzResearch.WordTrace tailWord_331340 prefixEnd_331340 6301358520771809793563 := by
  unfold tailWord_331340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042481309809621605939737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8056641746412828807919649 6042481309809621605939737)
  ·
    refine ⟨4531860982357216204454803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6042481309809621605939737 4531860982357216204454803)
    ·
      refine ⟨6797791473535824306682205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531860982357216204454803 6797791473535824306682205)
      ·
        refine ⟨2549171802575934115005827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6797791473535824306682205 2549171802575934115005827)
        ·
          refine ⟨3823757703863901172508741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549171802575934115005827 3823757703863901172508741)
          ·
            refine ⟨716954569474481469845389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3823757703863901172508741 716954569474481469845389)
            ·
              refine ⟨268857963552930551192021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 716954569474481469845389 268857963552930551192021)
              ·
                refine ⟨6301358520771809793563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 268857963552930551192021 6301358520771809793563)
                ·
                  rfl

theorem cell23_331340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 7].length) (baseStart_331340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331340 prefixEnd_331340 := by exact prefixLift 331340
  have htrace : WordTrace (prefixWord ++ tailWord_331340) baseStart_331340 baseEnd_331340 := by
    simpa [prefixWord, tailWord_331340, baseEnd_331340] using wordTrace_append hprefix tailTrace_331340
  have hstable : (prefixWord ++ tailWord_331340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331340).length < 2 ^ (prefixWord ++ tailWord_331340).sum := by decide
  have hdescent : baseEnd_331340 < baseStart_331340 := by decide
  rcases family_descends (prefixWord ++ tailWord_331340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331351 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_331351 : Nat := 118140960795 + 331351 * 2 ^ 59
def prefixEnd_331351 : Nat := 4983230072969 + 3 ^ 40 * 331351 * 2
def baseEnd_331351 : Nat := 170142328348038321388651

theorem tailTrace_331351 : CollatzResearch.WordTrace tailWord_331351 prefixEnd_331351 170142328348038321388651 := by
  unfold tailWord_331351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085363822579392090529907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8056909215052928060353271 12085363822579392090529907)
  ·
    refine ⟨18128045733869088135794861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12085363822579392090529907 18128045733869088135794861)
    ·
      refine ⟨6798017150200908050923073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18128045733869088135794861 6798017150200908050923073)
      ·
        refine ⟨5098512862650681038192305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6798017150200908050923073 5098512862650681038192305)
        ·
          refine ⟨3823884646988010778644229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5098512862650681038192305 3823884646988010778644229)
          ·
            refine ⟨716978371310252020995793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3823884646988010778644229 716978371310252020995793)
            ·
              refine ⟨537733778482689015746845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716978371310252020995793 537733778482689015746845)
              ·
                refine ⟨201650166931008380905067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537733778482689015746845 201650166931008380905067)
                ·
                  refine ⟨302475250396512571357601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201650166931008380905067 302475250396512571357601)
                  ·
                    refine ⟨226856437797384428518201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302475250396512571357601 226856437797384428518201)
                    ·
                      refine ⟨170142328348038321388651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226856437797384428518201 170142328348038321388651)
                      ·
                        rfl

theorem cell23_331351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_331351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331351 prefixEnd_331351 := by exact prefixLift 331351
  have htrace : WordTrace (prefixWord ++ tailWord_331351) baseStart_331351 baseEnd_331351 := by
    simpa [prefixWord, tailWord_331351, baseEnd_331351] using wordTrace_append hprefix tailTrace_331351
  have hstable : (prefixWord ++ tailWord_331351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331351).length < 2 ^ (prefixWord ++ tailWord_331351).sum := by decide
  have hdescent : baseEnd_331351 < baseStart_331351 := by decide
  rcases family_descends (prefixWord ++ tailWord_331351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331357 : List Nat := [1, 4, 4, 2, 1, 1, 10]
def baseStart_331357 : Nat := 118140960795 + 331357 * 2 ^ 59
def prefixEnd_331357 : Nat := 4983230072969 + 3 ^ 40 * 331357 * 2
def baseEnd_331357 : Nat := 2100560607802040714983

theorem tailTrace_331357 : CollatzResearch.WordTrace tailWord_331357 prefixEnd_331357 2100560607802040714983 := by
  unfold tailWord_331357
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085582660557655115248325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8057055107038436743498883 12085582660557655115248325)
  ·
    refine ⟨2266046748854560334109061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12085582660557655115248325 2266046748854560334109061)
    ·
      refine ⟨424883765410230062645449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2266046748854560334109061 424883765410230062645449)
      ·
        refine ⟨318662824057672546984087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424883765410230062645449 318662824057672546984087)
        ·
          refine ⟨477994236086508820476131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318662824057672546984087 477994236086508820476131)
          ·
            refine ⟨716991354129763230714197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477994236086508820476131 716991354129763230714197)
            ·
              refine ⟨2100560607802040714983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 716991354129763230714197 2100560607802040714983)
              ·
                rfl

theorem cell23_331357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 10].length) (baseStart_331357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331357 prefixEnd_331357 := by exact prefixLift 331357
  have htrace : WordTrace (prefixWord ++ tailWord_331357) baseStart_331357 baseEnd_331357 := by
    simpa [prefixWord, tailWord_331357, baseEnd_331357] using wordTrace_append hprefix tailTrace_331357
  have hstable : (prefixWord ++ tailWord_331357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331357).length < 2 ^ (prefixWord ++ tailWord_331357).sum := by decide
  have hdescent : baseEnd_331357 < baseStart_331357 := by decide
  rcases family_descends (prefixWord ++ tailWord_331357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331413 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 9]
def baseStart_331413 : Nat := 118140960795 + 331413 * 2 ^ 59
def prefixEnd_331413 : Nat := 4983230072969 + 3 ^ 40 * 331413 * 2
def baseEnd_331413 : Nat := 18908240460957453201485

theorem tailTrace_331413 : CollatzResearch.WordTrace tailWord_331413 prefixEnd_331413 18908240460957453201485 := by
  unfold tailWord_331413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087625148354776679286893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8058416765569851119524595 12087625148354776679286893)
  ·
    refine ⟨4532859430633041254732585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12087625148354776679286893 4532859430633041254732585)
    ·
      refine ⟨3399644572974780941049439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532859430633041254732585 3399644572974780941049439)
      ·
        refine ⟨5099466859462171411574159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399644572974780941049439 5099466859462171411574159)
        ·
          refine ⟨7649200289193257117361239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099466859462171411574159 7649200289193257117361239)
          ·
            refine ⟨11473800433789885676041859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649200289193257117361239 11473800433789885676041859)
            ·
              refine ⟨17210700650684828514062789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473800433789885676041859 17210700650684828514062789)
              ·
                refine ⟨3227006372003405346386773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17210700650684828514062789 3227006372003405346386773)
                ·
                  refine ⟨18908240460957453201485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3227006372003405346386773 18908240460957453201485)
                  ·
                    rfl

theorem cell23_331413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_331413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331413 prefixEnd_331413 := by exact prefixLift 331413
  have htrace : WordTrace (prefixWord ++ tailWord_331413) baseStart_331413 baseEnd_331413 := by
    simpa [prefixWord, tailWord_331413, baseEnd_331413] using wordTrace_append hprefix tailTrace_331413
  have hstable : (prefixWord ++ tailWord_331413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331413).length < 2 ^ (prefixWord ++ tailWord_331413).sum := by decide
  have hdescent : baseEnd_331413 < baseStart_331413 := by decide
  rcases family_descends (prefixWord ++ tailWord_331413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331424 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2]
def baseStart_331424 : Nat := 118140960795 + 331424 * 2 ^ 59
def prefixEnd_331424 : Nat := 4983230072969 + 3 ^ 40 * 331424 * 2
def baseEnd_331424 : Nat := 170179812435816535775815

theorem tailTrace_331424 : CollatzResearch.WordTrace tailWord_331424 prefixEnd_331424 170179812435816535775815 := by
  unfold tailWord_331424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044013175657462778968663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8058684234209950371958217 6044013175657462778968663)
  ·
    refine ⟨9066019763486194168452995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044013175657462778968663 9066019763486194168452995)
    ·
      refine ⟨13599029645229291252679493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066019763486194168452995 13599029645229291252679493)
      ·
        refine ⟨2549818058480492109877405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13599029645229291252679493 2549818058480492109877405)
        ·
          refine ⟨956181771930184541204027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2549818058480492109877405 956181771930184541204027)
          ·
            refine ⟨1434272657895276811806041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956181771930184541204027 1434272657895276811806041)
            ·
              refine ⟨1075704493421457608854531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434272657895276811806041 1075704493421457608854531)
              ·
                refine ⟨1613556740132186413281797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075704493421457608854531 1613556740132186413281797)
                ·
                  refine ⟨302541888774784952490337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613556740132186413281797 302541888774784952490337)
                  ·
                    refine ⟨226906416581088714367753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302541888774784952490337 226906416581088714367753)
                    ·
                      refine ⟨170179812435816535775815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226906416581088714367753 170179812435816535775815)
                      ·
                        rfl

theorem cell23_331424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_331424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331424 prefixEnd_331424 := by exact prefixLift 331424
  have htrace : WordTrace (prefixWord ++ tailWord_331424) baseStart_331424 baseEnd_331424 := by
    simpa [prefixWord, tailWord_331424, baseEnd_331424] using wordTrace_append hprefix tailTrace_331424
  have hstable : (prefixWord ++ tailWord_331424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331424).length < 2 ^ (prefixWord ++ tailWord_331424).sum := by decide
  have hdescent : baseEnd_331424 < baseStart_331424 := by decide
  rcases family_descends (prefixWord ++ tailWord_331424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331440 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_331440 : Nat := 118140960795 + 331440 * 2 ^ 59
def prefixEnd_331440 : Nat := 4983230072969 + 3 ^ 40 * 331440 * 2
def baseEnd_331440 : Nat := 170188028126288473175741

theorem tailTrace_331440 : CollatzResearch.WordTrace tailWord_331440 prefixEnd_331440 170188028126288473175741 := by
  unfold tailWord_331440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044304959628480145259887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8059073279504640193679849 6044304959628480145259887)
  ·
    refine ⟨9066457439442720217889831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6044304959628480145259887 9066457439442720217889831)
    ·
      refine ⟨13599686159164080326834747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9066457439442720217889831 13599686159164080326834747)
      ·
        refine ⟨20399529238746120490252121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13599686159164080326834747 20399529238746120490252121)
        ·
          refine ⟨15299646929059590367689091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20399529238746120490252121 15299646929059590367689091)
          ·
            refine ⟨22949470393589385551533637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299646929059590367689091 22949470393589385551533637)
            ·
              refine ⟨4303025698798009790912557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22949470393589385551533637 4303025698798009790912557)
              ·
                refine ⟨1613634637049253671592209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4303025698798009790912557 1613634637049253671592209)
                ·
                  refine ⟨1210225977786940253694157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613634637049253671592209 1210225977786940253694157)
                  ·
                    refine ⟨453834741670102595135309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210225977786940253694157 453834741670102595135309)
                    ·
                      refine ⟨170188028126288473175741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453834741670102595135309 170188028126288473175741)
                      ·
                        rfl

theorem cell23_331440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_331440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331440 prefixEnd_331440 := by exact prefixLift 331440
  have htrace : WordTrace (prefixWord ++ tailWord_331440) baseStart_331440 baseEnd_331440 := by
    simpa [prefixWord, tailWord_331440, baseEnd_331440] using wordTrace_append hprefix tailTrace_331440
  have hstable : (prefixWord ++ tailWord_331440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331440).length < 2 ^ (prefixWord ++ tailWord_331440).sum := by decide
  have hdescent : baseEnd_331440 < baseStart_331440 := by decide
  rcases family_descends (prefixWord ++ tailWord_331440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331470 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_331470 : Nat := 118140960795 + 331470 * 2 ^ 59
def prefixEnd_331470 : Nat := 4983230072969 + 3 ^ 40 * 331470 * 2
def baseEnd_331470 : Nat := 170203432545923355800603

theorem tailTrace_331470 : CollatzResearch.WordTrace tailWord_331470 prefixEnd_331470 170203432545923355800603 := by
  unfold tailWord_331470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511213013643534426763983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8059802739432183609407909 1511213013643534426763983)
  ·
    refine ⟨2266819520465301640145975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511213013643534426763983 2266819520465301640145975)
    ·
      refine ⟨3400229280697952460218963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266819520465301640145975 3400229280697952460218963)
      ·
        refine ⟨5100343921046928690328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400229280697952460218963 5100343921046928690328445)
        ·
          refine ⟨1912628970392598258873167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100343921046928690328445 1912628970392598258873167)
          ·
            refine ⟨2868943455588897388309751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912628970392598258873167 2868943455588897388309751)
            ·
              refine ⟨4303415183383346082464627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868943455588897388309751 4303415183383346082464627)
              ·
                refine ⟨6455122775075019123696941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303415183383346082464627 6455122775075019123696941)
                ·
                  refine ⟨2420671040653132171386353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6455122775075019123696941 2420671040653132171386353)
                  ·
                    refine ⟨1815503280489849128539765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420671040653132171386353 1815503280489849128539765)
                    ·
                      refine ⟨170203432545923355800603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1815503280489849128539765 170203432545923355800603)
                      ·
                        rfl

theorem cell23_331470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_331470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331470 prefixEnd_331470 := by exact prefixLift 331470
  have htrace : WordTrace (prefixWord ++ tailWord_331470) baseStart_331470 baseEnd_331470 := by
    simpa [prefixWord, tailWord_331470, baseEnd_331470] using wordTrace_append hprefix tailTrace_331470
  have hstable : (prefixWord ++ tailWord_331470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331470).length < 2 ^ (prefixWord ++ tailWord_331470).sum := by decide
  have hdescent : baseEnd_331470 < baseStart_331470 := by decide
  rcases family_descends (prefixWord ++ tailWord_331470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331517 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_331517 : Nat := 118140960795 + 331517 * 2 ^ 59
def prefixEnd_331517 : Nat := 4983230072969 + 3 ^ 40 * 331517 * 2
def baseEnd_331517 : Nat := 170227566136684671912887

theorem tailTrace_331517 : CollatzResearch.WordTrace tailWord_331517 prefixEnd_331517 170227566136684671912887 := by
  unfold tailWord_331517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091418339978002441072805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8060945559985334960715203 12091418339978002441072805)
  ·
    refine ⟨2267140938745875457701151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12091418339978002441072805 2267140938745875457701151)
    ·
      refine ⟨3400711408118813186551727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267140938745875457701151 3400711408118813186551727)
      ·
        refine ⟨5101067112178219779827591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400711408118813186551727 5101067112178219779827591)
        ·
          refine ⟨7651600668267329669741387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101067112178219779827591 7651600668267329669741387)
          ·
            refine ⟨11477401002400994504612081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651600668267329669741387 11477401002400994504612081)
            ·
              refine ⟨8608050751800745878459061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11477401002400994504612081 8608050751800745878459061)
              ·
                refine ⟨807004757981319926105537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8608050751800745878459061 807004757981319926105537)
                ·
                  refine ⟨605253568485989944579153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807004757981319926105537 605253568485989944579153)
                  ·
                    refine ⟨453940176364492458434365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605253568485989944579153 453940176364492458434365)
                    ·
                      refine ⟨170227566136684671912887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453940176364492458434365 170227566136684671912887)
                      ·
                        rfl

theorem cell23_331517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_331517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331517 prefixEnd_331517 := by exact prefixLift 331517
  have htrace : WordTrace (prefixWord ++ tailWord_331517) baseStart_331517 baseEnd_331517 := by
    simpa [prefixWord, tailWord_331517, baseEnd_331517] using wordTrace_append hprefix tailTrace_331517
  have hstable : (prefixWord ++ tailWord_331517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331517).length < 2 ^ (prefixWord ++ tailWord_331517).sum := by decide
  have hdescent : baseEnd_331517 < baseStart_331517 := by decide
  rcases family_descends (prefixWord ++ tailWord_331517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331526 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_331526 : Nat := 118140960795 + 331526 * 2 ^ 59
def prefixEnd_331526 : Nat := 4983230072969 + 3 ^ 40 * 331526 * 2
def baseEnd_331526 : Nat := 170232187462575136700347

theorem tailTrace_331526 : CollatzResearch.WordTrace tailWord_331526 prefixEnd_331526 170232187462575136700347 := by
  unfold tailWord_331526
  simp only [CollatzResearch.WordTrace]
  refine ⟨377867081154543655567201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8061164397963597985433621 377867081154543655567201)
  ·
    refine ⟨283400310865907741675401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377867081154543655567201 283400310865907741675401)
    ·
      refine ⟨212550233149430806256551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283400310865907741675401 212550233149430806256551)
      ·
        refine ⟨318825349724146209384827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212550233149430806256551 318825349724146209384827)
        ·
          refine ⟨478238024586219314077241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318825349724146209384827 478238024586219314077241)
          ·
            refine ⟨358678518439664485557931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478238024586219314077241 358678518439664485557931)
            ·
              refine ⟨538017777659496728336897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358678518439664485557931 538017777659496728336897)
              ·
                refine ⟨403513333244622546252673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538017777659496728336897 403513333244622546252673)
                ·
                  refine ⟨302634999933466909689505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403513333244622546252673 302634999933466909689505)
                  ·
                    refine ⟨226976249950100182267129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302634999933466909689505 226976249950100182267129)
                    ·
                      refine ⟨170232187462575136700347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226976249950100182267129 170232187462575136700347)
                      ·
                        rfl

theorem cell23_331526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_331526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331526 prefixEnd_331526 := by exact prefixLift 331526
  have htrace : WordTrace (prefixWord ++ tailWord_331526) baseStart_331526 baseEnd_331526 := by
    simpa [prefixWord, tailWord_331526, baseEnd_331526] using wordTrace_append hprefix tailTrace_331526
  have hstable : (prefixWord ++ tailWord_331526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331526).length < 2 ^ (prefixWord ++ tailWord_331526).sum := by decide
  have hdescent : baseEnd_331526 < baseStart_331526 := by decide
  rcases family_descends (prefixWord ++ tailWord_331526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331547 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 3]
def baseStart_331547 : Nat := 118140960795 + 331547 * 2 ^ 59
def prefixEnd_331547 : Nat := 4983230072969 + 3 ^ 40 * 331547 * 2
def baseEnd_331547 : Nat := 170242970556319554537749

theorem tailTrace_331547 : CollatzResearch.WordTrace tailWord_331547 prefixEnd_331547 170242970556319554537749 := by
  unfold tailWord_331547
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092512529869317564664895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8061675019912878376443263 12092512529869317564664895)
  ·
    refine ⟨18138768794803976346997343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092512529869317564664895 18138768794803976346997343)
    ·
      refine ⟨27208153192205964520496015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138768794803976346997343 27208153192205964520496015)
      ·
        refine ⟨40812229788308946780744023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27208153192205964520496015 40812229788308946780744023)
        ·
          refine ⟨61218344682463420171116035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40812229788308946780744023 61218344682463420171116035)
          ·
            refine ⟨91827517023695130256674053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61218344682463420171116035 91827517023695130256674053)
            ·
              refine ⟨17217659441942836923126385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91827517023695130256674053 17217659441942836923126385)
              ·
                refine ⟨12913244581457127692344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17217659441942836923126385 12913244581457127692344789)
                ·
                  refine ⟨302654169877901430289331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12913244581457127692344789 302654169877901430289331)
                  ·
                    refine ⟨453981254816852145433997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302654169877901430289331 453981254816852145433997)
                    ·
                      refine ⟨170242970556319554537749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 453981254816852145433997 170242970556319554537749)
                      ·
                        rfl

theorem cell23_331547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 3].length) (baseStart_331547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331547 prefixEnd_331547 := by exact prefixLift 331547
  have htrace : WordTrace (prefixWord ++ tailWord_331547) baseStart_331547 baseEnd_331547 := by
    simpa [prefixWord, tailWord_331547, baseEnd_331547] using wordTrace_append hprefix tailTrace_331547
  have hstable : (prefixWord ++ tailWord_331547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331547).length < 2 ^ (prefixWord ++ tailWord_331547).sum := by decide
  have hdescent : baseEnd_331547 < baseStart_331547 := by decide
  rcases family_descends (prefixWord ++ tailWord_331547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331554 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_331554 : Nat := 118140960795 + 331554 * 2 ^ 59
def prefixEnd_331554 : Nat := 4983230072969 + 3 ^ 40 * 331554 * 2
def baseEnd_331554 : Nat := 18916284991211225238913

theorem tailTrace_331554 : CollatzResearch.WordTrace tailWord_331554 prefixEnd_331554 18916284991211225238913 := by
  unfold tailWord_331554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023191960210989440042429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8061845227229305173446477 3023191960210989440042429)
  ·
    refine ⟨1133696985079121040015911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3023191960210989440042429 1133696985079121040015911)
    ·
      refine ⟨1700545477618681560023867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133696985079121040015911 1700545477618681560023867)
      ·
        refine ⟨2550818216428022340035801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700545477618681560023867 2550818216428022340035801)
        ·
          refine ⟨1913113662321016755026851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550818216428022340035801 1913113662321016755026851)
          ·
            refine ⟨2869670493481525132540277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913113662321016755026851 2869670493481525132540277)
            ·
              refine ⟨269031608763892981175651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2869670493481525132540277 269031608763892981175651)
              ·
                refine ⟨403547413145839471763477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269031608763892981175651 403547413145839471763477)
                ·
                  refine ⟨18916284991211225238913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 403547413145839471763477 18916284991211225238913)
                  ·
                    rfl

theorem cell23_331554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_331554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331554 prefixEnd_331554 := by exact prefixLift 331554
  have htrace : WordTrace (prefixWord ++ tailWord_331554) baseStart_331554 baseEnd_331554 := by
    simpa [prefixWord, tailWord_331554, baseEnd_331554] using wordTrace_append hprefix tailTrace_331554
  have hstable : (prefixWord ++ tailWord_331554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331554).length < 2 ^ (prefixWord ++ tailWord_331554).sum := by decide
  have hdescent : baseEnd_331554 < baseStart_331554 := by decide
  rcases family_descends (prefixWord ++ tailWord_331554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331564 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_331564 : Nat := 118140960795 + 331564 * 2 ^ 59
def prefixEnd_331564 : Nat := 4983230072969 + 3 ^ 40 * 331564 * 2
def baseEnd_331564 : Nat := 170251699727445988025171

theorem tailTrace_331564 : CollatzResearch.WordTrace tailWord_331564 prefixEnd_331564 170251699727445988025171 := by
  unfold tailWord_331564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046566285403864734016873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8062088380538486312022497 6046566285403864734016873)
  ·
    refine ⟨4534924714052898550512655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6046566285403864734016873 4534924714052898550512655)
    ·
      refine ⟨6802387071079347825768983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534924714052898550512655 6802387071079347825768983)
      ·
        refine ⟨10203580606619021738653475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802387071079347825768983 10203580606619021738653475)
        ·
          refine ⟨15305370909928532607980213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203580606619021738653475 15305370909928532607980213)
          ·
            refine ⟨1434878522805799931998145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15305370909928532607980213 1434878522805799931998145)
            ·
              refine ⟨1076158892104349948998609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434878522805799931998145 1076158892104349948998609)
              ·
                refine ⟨807119169078262461748957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076158892104349948998609 807119169078262461748957)
                ·
                  refine ⟨302669688404348423155859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807119169078262461748957 302669688404348423155859)
                  ·
                    refine ⟨454004532606522634733789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302669688404348423155859 454004532606522634733789)
                    ·
                      refine ⟨170251699727445988025171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454004532606522634733789 170251699727445988025171)
                      ·
                        rfl

theorem cell23_331564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_331564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331564 prefixEnd_331564 := by exact prefixLift 331564
  have htrace : WordTrace (prefixWord ++ tailWord_331564) baseStart_331564 baseEnd_331564 := by
    simpa [prefixWord, tailWord_331564, baseEnd_331564] using wordTrace_append hprefix tailTrace_331564
  have hstable : (prefixWord ++ tailWord_331564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331564).length < 2 ^ (prefixWord ++ tailWord_331564).sum := by decide
  have hdescent : baseEnd_331564 < baseStart_331564 := by decide
  rcases family_descends (prefixWord ++ tailWord_331564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331617 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_331617 : Nat := 118140960795 + 331617 * 2 ^ 59
def prefixEnd_331617 : Nat := 4983230072969 + 3 ^ 40 * 331617 * 2
def baseEnd_331617 : Nat := 170278914202134280662427

theorem tailTrace_331617 : CollatzResearch.WordTrace tailWord_331617 prefixEnd_331617 170278914202134280662427 := by
  unfold tailWord_331617
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095065639615719519713105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8063377093077146346475403 12095065639615719519713105)
  ·
    refine ⟨9071299229711789639784829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12095065639615719519713105 9071299229711789639784829)
    ·
      refine ⟨3401737211141921114919311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9071299229711789639784829 3401737211141921114919311)
      ·
        refine ⟨5102605816712881672378967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401737211141921114919311 5102605816712881672378967)
        ·
          refine ⟨7653908725069322508568451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102605816712881672378967 7653908725069322508568451)
          ·
            refine ⟨11480863087603983762852677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7653908725069322508568451 11480863087603983762852677)
            ·
              refine ⟨2152661828925746955534877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11480863087603983762852677 2152661828925746955534877)
              ·
                refine ⟨807248185847155108325579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152661828925746955534877 807248185847155108325579)
                ·
                  refine ⟨1210872278770732662488369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807248185847155108325579 1210872278770732662488369)
                  ·
                    refine ⟨908154209078049496866277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210872278770732662488369 908154209078049496866277)
                    ·
                      refine ⟨170278914202134280662427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908154209078049496866277 170278914202134280662427)
                      ·
                        rfl

theorem cell23_331617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_331617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331617 prefixEnd_331617 := by exact prefixLift 331617
  have htrace : WordTrace (prefixWord ++ tailWord_331617) baseStart_331617 baseEnd_331617 := by
    simpa [prefixWord, tailWord_331617, baseEnd_331617] using wordTrace_append hprefix tailTrace_331617
  have hstable : (prefixWord ++ tailWord_331617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331617).length < 2 ^ (prefixWord ++ tailWord_331617).sum := by decide
  have hdescent : baseEnd_331617 < baseStart_331617 := by decide
  rcases family_descends (prefixWord ++ tailWord_331617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331624 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_331624 : Nat := 118140960795 + 331624 * 2 ^ 59
def prefixEnd_331624 : Nat := 4983230072969 + 3 ^ 40 * 331624 * 2
def baseEnd_331624 : Nat := 170282508566715753274895

theorem tailTrace_331624 : CollatzResearch.WordTrace tailWord_331624 prefixEnd_331624 170282508566715753274895 := by
  unfold tailWord_331624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047660475295179857608963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8063547300393573143478617 6047660475295179857608963)
  ·
    refine ⟨9071490712942769786413445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047660475295179857608963 9071490712942769786413445)
    ·
      refine ⟨1700904508676769334952521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9071490712942769786413445 1700904508676769334952521)
      ·
        refine ⟨1275678381507577001214391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700904508676769334952521 1275678381507577001214391)
        ·
          refine ⟨1913517572261365501821587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275678381507577001214391 1913517572261365501821587)
          ·
            refine ⟨2870276358392048252732381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913517572261365501821587 2870276358392048252732381)
            ·
              refine ⟨1076353634397018094774643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2870276358392048252732381 1076353634397018094774643)
              ·
                refine ⟨1614530451595527142161965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076353634397018094774643 1614530451595527142161965)
                ·
                  refine ⟨605448919348322678310737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1614530451595527142161965 605448919348322678310737)
                  ·
                    refine ⟨454086689511242008733053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605448919348322678310737 454086689511242008733053)
                    ·
                      refine ⟨170282508566715753274895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454086689511242008733053 170282508566715753274895)
                      ·
                        rfl

theorem cell23_331624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_331624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331624 prefixEnd_331624 := by exact prefixLift 331624
  have htrace : WordTrace (prefixWord ++ tailWord_331624) baseStart_331624 baseEnd_331624 := by
    simpa [prefixWord, tailWord_331624, baseEnd_331624] using wordTrace_append hprefix tailTrace_331624
  have hstable : (prefixWord ++ tailWord_331624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331624).length < 2 ^ (prefixWord ++ tailWord_331624).sum := by decide
  have hdescent : baseEnd_331624 < baseStart_331624 := by decide
  rcases family_descends (prefixWord ++ tailWord_331624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331641 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 1, 2, 3]
def baseStart_331641 : Nat := 118140960795 + 331641 * 2 ^ 59
def prefixEnd_331641 : Nat := 4983230072969 + 3 ^ 40 * 331641 * 2
def baseEnd_331641 : Nat := 170291237737842186762317

theorem tailTrace_331641 : CollatzResearch.WordTrace tailWord_331641 prefixEnd_331641 170291237737842186762317 := by
  unfold tailWord_331641
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095940991528771618586777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8063960661019181079057851 12095940991528771618586777)
  ·
    refine ⟨9071955743646578713940083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12095940991528771618586777 9071955743646578713940083)
    ·
      refine ⟨13607933615469868070910125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071955743646578713940083 13607933615469868070910125)
      ·
        refine ⟨5102975105801200526591297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13607933615469868070910125 5102975105801200526591297)
        ·
          refine ⟨3827231329350900394943473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102975105801200526591297 3827231329350900394943473)
          ·
            refine ⟨2870423497013175296207605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3827231329350900394943473 2870423497013175296207605)
            ·
              refine ⟨269102202844985184019463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2870423497013175296207605 269102202844985184019463)
              ·
                refine ⟨403653304267477776029195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269102202844985184019463 403653304267477776029195)
                ·
                  refine ⟨605479956401216664043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403653304267477776029195 605479956401216664043793)
                  ·
                    refine ⟨454109967300912498032845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605479956401216664043793 454109967300912498032845)
                    ·
                      refine ⟨170291237737842186762317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454109967300912498032845 170291237737842186762317)
                      ·
                        rfl

theorem cell23_331641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_331641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331641 prefixEnd_331641 := by exact prefixLift 331641
  have htrace : WordTrace (prefixWord ++ tailWord_331641) baseStart_331641 baseEnd_331641 := by
    simpa [prefixWord, tailWord_331641, baseEnd_331641] using wordTrace_append hprefix tailTrace_331641
  have hstable : (prefixWord ++ tailWord_331641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331641).length < 2 ^ (prefixWord ++ tailWord_331641).sum := by decide
  have hdescent : baseEnd_331641 < baseStart_331641 := by decide
  rcases family_descends (prefixWord ++ tailWord_331641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331649 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_331649 : Nat := 118140960795 + 331649 * 2 ^ 59
def prefixEnd_331649 : Nat := 4983230072969 + 3 ^ 40 * 331649 * 2
def baseEnd_331649 : Nat := 170295345583078155462281

theorem tailTrace_331649 : CollatzResearch.WordTrace tailWord_331649 prefixEnd_331649 170295345583078155462281 := by
  unfold tailWord_331649
  simp only [CollatzResearch.WordTrace]
  refine ⟨12096232775499788984878001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064155183666525989918667 12096232775499788984878001)
  ·
    refine ⟨9072174581624841738658501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12096232775499788984878001 9072174581624841738658501)
    ·
      refine ⟨1701032734054657825998469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9072174581624841738658501 1701032734054657825998469)
      ·
        refine ⟨318943637635248342374713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1701032734054657825998469 318943637635248342374713)
        ·
          refine ⟨239207728226436256781035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318943637635248342374713 239207728226436256781035)
          ·
            refine ⟨358811592339654385171553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239207728226436256781035 358811592339654385171553)
            ·
              refine ⟨269108694254740788878665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358811592339654385171553 269108694254740788878665)
              ·
                refine ⟨201831520691055591658999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269108694254740788878665 201831520691055591658999)
                ·
                  refine ⟨302747281036583387488499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201831520691055591658999 302747281036583387488499)
                  ·
                    refine ⟨454120921554875081232749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302747281036583387488499 454120921554875081232749)
                    ·
                      refine ⟨170295345583078155462281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454120921554875081232749 170295345583078155462281)
                      ·
                        rfl

theorem cell23_331649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_331649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331649 prefixEnd_331649 := by exact prefixLift 331649
  have htrace : WordTrace (prefixWord ++ tailWord_331649) baseStart_331649 baseEnd_331649 := by
    simpa [prefixWord, tailWord_331649, baseEnd_331649] using wordTrace_append hprefix tailTrace_331649
  have hstable : (prefixWord ++ tailWord_331649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331649).length < 2 ^ (prefixWord ++ tailWord_331649).sum := by decide
  have hdescent : baseEnd_331649 < baseStart_331649 := by decide
  rcases family_descends (prefixWord ++ tailWord_331649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331655 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_331655 : Nat := 118140960795 + 331655 * 2 ^ 59
def prefixEnd_331655 : Nat := 4983230072969 + 3 ^ 40 * 331655 * 2
def baseEnd_331655 : Nat := 170298426467005131987253

theorem tailTrace_331655 : CollatzResearch.WordTrace tailWord_331655 prefixEnd_331655 170298426467005131987253 := by
  unfold tailWord_331655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12096451613478052009596419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064301075652034673064279 12096451613478052009596419)
  ·
    refine ⟨18144677420217078014394629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12096451613478052009596419 18144677420217078014394629)
    ·
      refine ⟨3402127016290702127698993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18144677420217078014394629 3402127016290702127698993)
      ·
        refine ⟨2551595262218026595774245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402127016290702127698993 2551595262218026595774245)
        ·
          refine ⟨478424111665879986707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2551595262218026595774245 478424111665879986707671)
          ·
            refine ⟨717636167498819980061507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478424111665879986707671 717636167498819980061507)
            ·
              refine ⟨1076454251248229970092261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717636167498819980061507 1076454251248229970092261)
              ·
                refine ⟨201835172109043119392299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1076454251248229970092261 201835172109043119392299)
                ·
                  refine ⟨302752758163564679088449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201835172109043119392299 302752758163564679088449)
                  ·
                    refine ⟨227064568622673509316337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302752758163564679088449 227064568622673509316337)
                    ·
                      refine ⟨170298426467005131987253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227064568622673509316337 170298426467005131987253)
                      ·
                        rfl

theorem cell23_331655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_331655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331655 prefixEnd_331655 := by exact prefixLift 331655
  have htrace : WordTrace (prefixWord ++ tailWord_331655) baseStart_331655 baseEnd_331655 := by
    simpa [prefixWord, tailWord_331655, baseEnd_331655] using wordTrace_append hprefix tailTrace_331655
  have hstable : (prefixWord ++ tailWord_331655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331655).length < 2 ^ (prefixWord ++ tailWord_331655).sum := by decide
  have hdescent : baseEnd_331655 < baseStart_331655 := by decide
  rcases family_descends (prefixWord ++ tailWord_331655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2]
def baseStart_331664 : Nat := 118140960795 + 331664 * 2 ^ 59
def prefixEnd_331664 : Nat := 4983230072969 + 3 ^ 40 * 331664 * 2
def baseEnd_331664 : Nat := 170303047792895596774711

theorem tailTrace_331664 : CollatzResearch.WordTrace tailWord_331664 prefixEnd_331664 170303047792895596774711 := by
  unfold tailWord_331664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048389935222723273337023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8064519913630297697782697 6048389935222723273337023)
  ·
    refine ⟨9072584902834084910005535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6048389935222723273337023 9072584902834084910005535)
    ·
      refine ⟨13608877354251127365008303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9072584902834084910005535 13608877354251127365008303)
      ·
        refine ⟨20413316031376691047512455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13608877354251127365008303 20413316031376691047512455)
        ·
          refine ⟨30619974047065036571268683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20413316031376691047512455 30619974047065036571268683)
          ·
            refine ⟨45929961070597554856903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30619974047065036571268683 45929961070597554856903025)
            ·
              refine ⟨34447470802948166142677269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45929961070597554856903025 34447470802948166142677269)
              ·
                refine ⟨1614725193888195287937997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34447470802948166142677269 1614725193888195287937997)
                ·
                  refine ⟨605521947708073232976749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1614725193888195287937997 605521947708073232976749)
                  ·
                    refine ⟨227070730390527462366281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 605521947708073232976749 227070730390527462366281)
                    ·
                      refine ⟨170303047792895596774711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227070730390527462366281 170303047792895596774711)
                      ·
                        rfl

theorem cell23_331664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2].length) (baseStart_331664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331664 prefixEnd_331664 := by exact prefixLift 331664
  have htrace : WordTrace (prefixWord ++ tailWord_331664) baseStart_331664 baseEnd_331664 := by
    simpa [prefixWord, tailWord_331664, baseEnd_331664] using wordTrace_append hprefix tailTrace_331664
  have hstable : (prefixWord ++ tailWord_331664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331664).length < 2 ^ (prefixWord ++ tailWord_331664).sum := by decide
  have hdescent : baseEnd_331664 < baseStart_331664 := by decide
  rcases family_descends (prefixWord ++ tailWord_331664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331671 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_331671 : Nat := 118140960795 + 331671 * 2 ^ 59
def prefixEnd_331671 : Nat := 4983230072969 + 3 ^ 40 * 331671 * 2
def baseEnd_331671 : Nat := 170306642157477069387179

theorem tailTrace_331671 : CollatzResearch.WordTrace tailWord_331671 prefixEnd_331671 170306642157477069387179 := by
  unfold tailWord_331671
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097035181420086742178867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064690120946724494785911 12097035181420086742178867)
  ·
    refine ⟨18145552772130130113268301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097035181420086742178867 18145552772130130113268301)
    ·
      refine ⟨6804582289548798792475613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18145552772130130113268301 6804582289548798792475613)
      ·
        refine ⟨2551718358580799547178355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6804582289548798792475613 2551718358580799547178355)
        ·
          refine ⟨3827577537871199320767533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551718358580799547178355 3827577537871199320767533)
          ·
            refine ⟨1435341576701699745287825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3827577537871199320767533 1435341576701699745287825)
            ·
              refine ⟨1076506182526274808965869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435341576701699745287825 1076506182526274808965869)
              ·
                refine ⟨403689818447353053362201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076506182526274808965869 403689818447353053362201)
                ·
                  refine ⟨302767363835514790021651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403689818447353053362201 302767363835514790021651)
                  ·
                    refine ⟨454151045753272185032477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302767363835514790021651 454151045753272185032477)
                    ·
                      refine ⟨170306642157477069387179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454151045753272185032477 170306642157477069387179)
                      ·
                        rfl

theorem cell23_331671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_331671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331671 prefixEnd_331671 := by exact prefixLift 331671
  have htrace : WordTrace (prefixWord ++ tailWord_331671) baseStart_331671 baseEnd_331671 := by
    simpa [prefixWord, tailWord_331671, baseEnd_331671] using wordTrace_append hprefix tailTrace_331671
  have hstable : (prefixWord ++ tailWord_331671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331671).length < 2 ^ (prefixWord ++ tailWord_331671).sum := by decide
  have hdescent : baseEnd_331671 < baseStart_331671 := by decide
  rcases family_descends (prefixWord ++ tailWord_331671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331678 : List Nat := [4, 3, 1, 3, 1, 1, 3, 7]
def baseStart_331678 : Nat := 118140960795 + 331678 * 2 ^ 59
def prefixEnd_331678 : Nat := 4983230072969 + 3 ^ 40 * 331678 * 2
def baseEnd_331678 : Nat := 6307786537854020074061

theorem tailTrace_331678 : CollatzResearch.WordTrace tailWord_331678 prefixEnd_331678 6307786537854020074061 := by
  unfold tailWord_331678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512161311549340867210461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8064860328263151291789125 1512161311549340867210461)
  ·
    refine ⟨567060491831002825203923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1512161311549340867210461 567060491831002825203923)
    ·
      refine ⟨850590737746504237805885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567060491831002825203923 850590737746504237805885)
      ·
        refine ⟨318971526654939089177207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 850590737746504237805885 318971526654939089177207)
        ·
          refine ⟨478457289982408633765811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318971526654939089177207 478457289982408633765811)
          ·
            refine ⟨717685934973612950648717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478457289982408633765811 717685934973612950648717)
            ·
              refine ⟨269132225615104856493269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717685934973612950648717 269132225615104856493269)
              ·
                refine ⟨6307786537854020074061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 269132225615104856493269 6307786537854020074061)
                ·
                  rfl

theorem cell23_331678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_331678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331678 prefixEnd_331678 := by exact prefixLift 331678
  have htrace : WordTrace (prefixWord ++ tailWord_331678) baseStart_331678 baseEnd_331678 := by
    simpa [prefixWord, tailWord_331678, baseEnd_331678] using wordTrace_append hprefix tailTrace_331678
  have hstable : (prefixWord ++ tailWord_331678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331678).length < 2 ^ (prefixWord ++ tailWord_331678).sum := by decide
  have hdescent : baseEnd_331678 < baseStart_331678 := by decide
  rcases family_descends (prefixWord ++ tailWord_331678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331707 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_331707 : Nat := 118140960795 + 331707 * 2 ^ 59
def prefixEnd_331707 : Nat := 4983230072969 + 3 ^ 40 * 331707 * 2
def baseEnd_331707 : Nat := 170325127461038928537013

theorem tailTrace_331707 : CollatzResearch.WordTrace tailWord_331707 prefixEnd_331707 170325127461038928537013 := by
  unfold tailWord_331707
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098348209289664890489375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8065565472859776593659583 12098348209289664890489375)
  ·
    refine ⟨18147522313934497335734063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098348209289664890489375 18147522313934497335734063)
    ·
      refine ⟨27221283470901746003601095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18147522313934497335734063 27221283470901746003601095)
      ·
        refine ⟨40831925206352619005401643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27221283470901746003601095 40831925206352619005401643)
        ·
          refine ⟨61247887809528928508102465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40831925206352619005401643 61247887809528928508102465)
          ·
            refine ⟨45935915857146696381076849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61247887809528928508102465 45935915857146696381076849)
            ·
              refine ⟨34451936892860022285807637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45935915857146696381076849 34451936892860022285807637)
              ·
                refine ⟨1614934541852813544647233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34451936892860022285807637 1614934541852813544647233)
                ·
                  refine ⟨1211200906389610158485425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614934541852813544647233 1211200906389610158485425)
                  ·
                    refine ⟨908400679792207618864069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211200906389610158485425 908400679792207618864069)
                    ·
                      refine ⟨170325127461038928537013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908400679792207618864069 170325127461038928537013)
                      ·
                        rfl

theorem cell23_331707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_331707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331707 prefixEnd_331707 := by exact prefixLift 331707
  have htrace : WordTrace (prefixWord ++ tailWord_331707) baseStart_331707 baseEnd_331707 := by
    simpa [prefixWord, tailWord_331707, baseEnd_331707] using wordTrace_append hprefix tailTrace_331707
  have hstable : (prefixWord ++ tailWord_331707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331707).length < 2 ^ (prefixWord ++ tailWord_331707).sum := by decide
  have hdescent : baseEnd_331707 < baseStart_331707 := by decide
  rcases family_descends (prefixWord ++ tailWord_331707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331711 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 4, 2, 2]
def baseStart_331711 : Nat := 118140960795 + 331711 * 2 ^ 59
def prefixEnd_331711 : Nat := 4983230072969 + 3 ^ 40 * 331711 * 2
def baseEnd_331711 : Nat := 170327181383656912886995

theorem tailTrace_331711 : CollatzResearch.WordTrace tailWord_331711 prefixEnd_331711 170327181383656912886995 := by
  unfold tailWord_331711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098494101275173573634987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8065662734183449049089991 12098494101275173573634987)
  ·
    refine ⟨18147741151912760360452481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098494101275173573634987 18147741151912760360452481)
    ·
      refine ⟨13610805863934570270339361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18147741151912760360452481 13610805863934570270339361)
      ·
        refine ⟨10208104397950927702754521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13610805863934570270339361 10208104397950927702754521)
        ·
          refine ⟨7656078298463195777065891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10208104397950927702754521 7656078298463195777065891)
          ·
            refine ⟨11484117447694793665598837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656078298463195777065891 11484117447694793665598837)
            ·
              refine ⟨1076636010721386906149891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11484117447694793665598837 1076636010721386906149891)
              ·
                refine ⟨1614954016082080359224837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076636010721386906149891 1614954016082080359224837)
                ·
                  refine ⟨302803878015390067354657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614954016082080359224837 302803878015390067354657)
                  ·
                    refine ⟨227102908511542550515993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302803878015390067354657 227102908511542550515993)
                    ·
                      refine ⟨170327181383656912886995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227102908511542550515993 170327181383656912886995)
                      ·
                        rfl

theorem cell23_331711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_331711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331711 prefixEnd_331711 := by exact prefixLift 331711
  have htrace : WordTrace (prefixWord ++ tailWord_331711) baseStart_331711 baseEnd_331711 := by
    simpa [prefixWord, tailWord_331711, baseEnd_331711] using wordTrace_append hprefix tailTrace_331711
  have hstable : (prefixWord ++ tailWord_331711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331711).length < 2 ^ (prefixWord ++ tailWord_331711).sum := by decide
  have hdescent : baseEnd_331711 < baseStart_331711 := by decide
  rcases family_descends (prefixWord ++ tailWord_331711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331724 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_331724 : Nat := 118140960795 + 331724 * 2 ^ 59
def prefixEnd_331724 : Nat := 4983230072969 + 3 ^ 40 * 331724 * 2
def baseEnd_331724 : Nat := 170333856632165362024435

theorem tailTrace_331724 : CollatzResearch.WordTrace tailWord_331724 prefixEnd_331724 170333856632165362024435 := by
  unfold tailWord_331724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049484125114038396929113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8065978833485384529238817 6049484125114038396929113)
  ·
    refine ⟨4537113093835528797696835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6049484125114038396929113 4537113093835528797696835)
    ·
      refine ⟨6805669640753293196545253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537113093835528797696835 6805669640753293196545253)
      ·
        refine ⟨1276063057641242474352235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6805669640753293196545253 1276063057641242474352235)
        ·
          refine ⟨1914094586461863711528353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276063057641242474352235 1914094586461863711528353)
          ·
            refine ⟨1435570939846397783646265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1914094586461863711528353 1435570939846397783646265)
            ·
              refine ⟨1076678204884798337734699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435570939846397783646265 1076678204884798337734699)
              ·
                refine ⟨1615017307327197506602049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076678204884798337734699 1615017307327197506602049)
                ·
                  refine ⟨1211262980495398129951537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615017307327197506602049 1211262980495398129951537)
                  ·
                    refine ⟨908447235371548597463653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211262980495398129951537 908447235371548597463653)
                    ·
                      refine ⟨170333856632165362024435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908447235371548597463653 170333856632165362024435)
                      ·
                        rfl

theorem cell23_331724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_331724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331724 prefixEnd_331724 := by exact prefixLift 331724
  have htrace : WordTrace (prefixWord ++ tailWord_331724) baseStart_331724 baseEnd_331724 := by
    simpa [prefixWord, tailWord_331724, baseEnd_331724] using wordTrace_append hprefix tailTrace_331724
  have hstable : (prefixWord ++ tailWord_331724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331724).length < 2 ^ (prefixWord ++ tailWord_331724).sum := by decide
  have hdescent : baseEnd_331724 < baseStart_331724 := by decide
  rcases family_descends (prefixWord ++ tailWord_331724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331767 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_331767 : Nat := 118140960795 + 331767 * 2 ^ 59
def prefixEnd_331767 : Nat := 4983230072969 + 3 ^ 40 * 331767 * 2
def baseEnd_331767 : Nat := 170355936300308693786737

theorem tailTrace_331767 : CollatzResearch.WordTrace tailWord_331767 prefixEnd_331767 170355936300308693786737 := by
  unfold tailWord_331767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12100536589072295137673555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8067024392714863425115703 12100536589072295137673555)
  ·
    refine ⟨18150804883608442706510333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12100536589072295137673555 18150804883608442706510333)
    ·
      refine ⟨6806551831353166014941375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18150804883608442706510333 6806551831353166014941375)
      ·
        refine ⟨10209827747029749022412063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806551831353166014941375 10209827747029749022412063)
        ·
          refine ⟨15314741620544623533618095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209827747029749022412063 15314741620544623533618095)
          ·
            refine ⟨22972112430816935300427143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15314741620544623533618095 22972112430816935300427143)
            ·
              refine ⟨34458168646225402950640715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22972112430816935300427143 34458168646225402950640715)
              ·
                refine ⟨51687252969338104425961073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34458168646225402950640715 51687252969338104425961073)
                ·
                  refine ⟨38765439727003578319470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51687252969338104425961073 38765439727003578319470805)
                  ·
                    refine ⟨908564993601646366862597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38765439727003578319470805 908564993601646366862597)
                    ·
                      refine ⟨170355936300308693786737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908564993601646366862597 170355936300308693786737)
                      ·
                        rfl

theorem cell23_331767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_331767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331767 prefixEnd_331767 := by exact prefixLift 331767
  have htrace : WordTrace (prefixWord ++ tailWord_331767) baseStart_331767 baseEnd_331767 := by
    simpa [prefixWord, tailWord_331767, baseEnd_331767] using wordTrace_append hprefix tailTrace_331767
  have hstable : (prefixWord ++ tailWord_331767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331767).length < 2 ^ (prefixWord ++ tailWord_331767).sum := by decide
  have hdescent : baseEnd_331767 < baseStart_331767 := by decide
  rcases family_descends (prefixWord ++ tailWord_331767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331784 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_331784 : Nat := 118140960795 + 331784 * 2 ^ 59
def prefixEnd_331784 : Nat := 4983230072969 + 3 ^ 40 * 331784 * 2
def baseEnd_331784 : Nat := 170364665471435127274159

theorem tailTrace_331784 : CollatzResearch.WordTrace tailWord_331784 prefixEnd_331784 170364665471435127274159 := by
  unfold tailWord_331784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050578315005353520521203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8067437753340471360694937 6050578315005353520521203)
  ·
    refine ⟨9075867472508030280781805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6050578315005353520521203 9075867472508030280781805)
    ·
      refine ⟨3403450302190511355293177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9075867472508030280781805 3403450302190511355293177)
      ·
        refine ⟨2552587726642883516469883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403450302190511355293177 2552587726642883516469883)
        ·
          refine ⟨3828881589964325274704825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552587726642883516469883 3828881589964325274704825)
          ·
            refine ⟨2871661192473243956028619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828881589964325274704825 2871661192473243956028619)
            ·
              refine ⟨4307491788709865934042929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871661192473243956028619 4307491788709865934042929)
              ·
                refine ⟨3230618841532399450532197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307491788709865934042929 3230618841532399450532197)
                ·
                  refine ⟨605741032787324896974787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3230618841532399450532197 605741032787324896974787)
                  ·
                    refine ⟨908611549180987345462181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605741032787324896974787 908611549180987345462181)
                    ·
                      refine ⟨170364665471435127274159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908611549180987345462181 170364665471435127274159)
                      ·
                        rfl

theorem cell23_331784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_331784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331784 prefixEnd_331784 := by exact prefixLift 331784
  have htrace : WordTrace (prefixWord ++ tailWord_331784) baseStart_331784 baseEnd_331784 := by
    simpa [prefixWord, tailWord_331784, baseEnd_331784] using wordTrace_append hprefix tailTrace_331784
  have hstable : (prefixWord ++ tailWord_331784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331784).length < 2 ^ (prefixWord ++ tailWord_331784).sum := by decide
  have hdescent : baseEnd_331784 < baseStart_331784 := by decide
  rcases family_descends (prefixWord ++ tailWord_331784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331824 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 6]
def baseStart_331824 : Nat := 118140960795 + 331824 * 2 ^ 59
def prefixEnd_331824 : Nat := 4983230072969 + 3 ^ 40 * 331824 * 2
def baseEnd_331824 : Nat := 18931689410846107863775

theorem tailTrace_331824 : CollatzResearch.WordTrace tailWord_331824 prefixEnd_331824 18931689410846107863775 := by
  unfold tailWord_331824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051307774932896936249263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8068410366577195914999017 6051307774932896936249263)
  ·
    refine ⟨9076961662399345404373895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6051307774932896936249263 9076961662399345404373895)
    ·
      refine ⟨13615442493599018106560843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9076961662399345404373895 13615442493599018106560843)
      ·
        refine ⟨20423163740398527159841265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13615442493599018106560843 20423163740398527159841265)
        ·
          refine ⟨15317372805298895369880949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20423163740398527159841265 15317372805298895369880949)
          ·
            refine ⟨1436003700496771440926339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15317372805298895369880949 1436003700496771440926339)
            ·
              refine ⟨2154005550745157161389509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436003700496771440926339 2154005550745157161389509)
              ·
                refine ⟨403876040764716967760533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2154005550745157161389509 403876040764716967760533)
                ·
                  refine ⟨18931689410846107863775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 403876040764716967760533 18931689410846107863775)
                  ·
                    rfl

theorem cell23_331824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_331824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331824 prefixEnd_331824 := by exact prefixLift 331824
  have htrace : WordTrace (prefixWord ++ tailWord_331824) baseStart_331824 baseEnd_331824 := by
    simpa [prefixWord, tailWord_331824, baseEnd_331824] using wordTrace_append hprefix tailTrace_331824
  have hstable : (prefixWord ++ tailWord_331824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331824).length < 2 ^ (prefixWord ++ tailWord_331824).sum := by decide
  have hdescent : baseEnd_331824 < baseStart_331824 := by decide
  rcases family_descends (prefixWord ++ tailWord_331824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331834 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_331834 : Nat := 118140960795 + 331834 * 2 ^ 59
def prefixEnd_331834 : Nat := 4983230072969 + 3 ^ 40 * 331834 * 2
def baseEnd_331834 : Nat := 170390339504159931648929

theorem tailTrace_331834 : CollatzResearch.WordTrace tailWord_331834 prefixEnd_331834 170390339504159931648929 := by
  unfold tailWord_331834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025745069957391395090639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8068653519886377053575037 3025745069957391395090639)
  ·
    refine ⟨4538617604936087092635959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025745069957391395090639 4538617604936087092635959)
    ·
      refine ⟨6807926407404130638953939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538617604936087092635959 6807926407404130638953939)
      ·
        refine ⟨10211889611106195958430909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807926407404130638953939 10211889611106195958430909)
        ·
          refine ⟨3829458604164823484411591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10211889611106195958430909 3829458604164823484411591)
          ·
            refine ⟨5744187906247235226617387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829458604164823484411591 5744187906247235226617387)
            ·
              refine ⟨8616281859370852839926081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744187906247235226617387 8616281859370852839926081)
              ·
                refine ⟨6462211394528139629944561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8616281859370852839926081 6462211394528139629944561)
                ·
                  refine ⟨4846658545896104722458421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6462211394528139629944561 4846658545896104722458421)
                  ·
                    refine ⟨454374238677759817730477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4846658545896104722458421 454374238677759817730477)
                    ·
                      refine ⟨170390339504159931648929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454374238677759817730477 170390339504159931648929)
                      ·
                        rfl

theorem cell23_331834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_331834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331834 prefixEnd_331834 := by exact prefixLift 331834
  have htrace : WordTrace (prefixWord ++ tailWord_331834) baseStart_331834 baseEnd_331834 := by
    simpa [prefixWord, tailWord_331834, baseEnd_331834] using wordTrace_append hprefix tailTrace_331834
  have hstable : (prefixWord ++ tailWord_331834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331834).length < 2 ^ (prefixWord ++ tailWord_331834).sum := by decide
  have hdescent : baseEnd_331834 < baseStart_331834 := by decide
  rcases family_descends (prefixWord ++ tailWord_331834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331841 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 6]
def baseStart_331841 : Nat := 118140960795 + 331841 * 2 ^ 59
def prefixEnd_331841 : Nat := 4983230072969 + 3 ^ 40 * 331841 * 2
def baseEnd_331841 : Nat := 18932659318749044917933

theorem tailTrace_331841 : CollatzResearch.WordTrace tailWord_331841 prefixEnd_331841 18932659318749044917933 := by
  unfold tailWord_331841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103235590804205775867377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068823727202803850578251 12103235590804205775867377)
  ·
    refine ⟨9077426693103154331900533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12103235590804205775867377 9077426693103154331900533)
    ·
      refine ⟨851008752478420718615675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9077426693103154331900533 851008752478420718615675)
      ·
        refine ⟨1276513128717631077923513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851008752478420718615675 1276513128717631077923513)
        ·
          refine ⟨957384846538223308442635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276513128717631077923513 957384846538223308442635)
          ·
            refine ⟨1436077269807334962663953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957384846538223308442635 1436077269807334962663953)
            ·
              refine ⟨1077057952355501221997965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436077269807334962663953 1077057952355501221997965)
              ·
                refine ⟨403896732133312958249237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1077057952355501221997965 403896732133312958249237)
                ·
                  refine ⟨18932659318749044917933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 403896732133312958249237 18932659318749044917933)
                  ·
                    rfl

theorem cell23_331841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_331841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331841 prefixEnd_331841 := by exact prefixLift 331841
  have htrace : WordTrace (prefixWord ++ tailWord_331841) baseStart_331841 baseEnd_331841 := by
    simpa [prefixWord, tailWord_331841, baseEnd_331841] using wordTrace_append hprefix tailTrace_331841
  have hstable : (prefixWord ++ tailWord_331841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331841).length < 2 ^ (prefixWord ++ tailWord_331841).sum := by decide
  have hdescent : baseEnd_331841 < baseStart_331841 := by decide
  rcases family_descends (prefixWord ++ tailWord_331841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331851 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 3]
def baseStart_331851 : Nat := 118140960795 + 331851 * 2 ^ 59
def prefixEnd_331851 : Nat := 4983230072969 + 3 ^ 40 * 331851 * 2
def baseEnd_331851 : Nat := 170399068675286365136351

theorem tailTrace_331851 : CollatzResearch.WordTrace tailWord_331851 prefixEnd_331851 170399068675286365136351 := by
  unfold tailWord_331851
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103600320767977483731407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8069066880511984989154271 12103600320767977483731407)
  ·
    refine ⟨18155400481151966225597111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12103600320767977483731407 18155400481151966225597111)
    ·
      refine ⟨27233100721727949338395667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18155400481151966225597111 27233100721727949338395667)
      ·
        refine ⟨40849651082591924007593501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27233100721727949338395667 40849651082591924007593501)
        ·
          refine ⟨15318619155971971502847563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40849651082591924007593501 15318619155971971502847563)
          ·
            refine ⟨22977928733957957254271345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15318619155971971502847563 22977928733957957254271345)
            ·
              refine ⟨17233446550468467940703509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22977928733957957254271345 17233446550468467940703509)
              ·
                refine ⟨807817807053209434720477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17233446550468467940703509 807817807053209434720477)
                ·
                  refine ⟨302931677644953538020179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807817807053209434720477 302931677644953538020179)
                  ·
                    refine ⟨454397516467430307030269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302931677644953538020179 454397516467430307030269)
                    ·
                      refine ⟨170399068675286365136351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454397516467430307030269 170399068675286365136351)
                      ·
                        rfl

theorem cell23_331851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 3].length) (baseStart_331851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331851 prefixEnd_331851 := by exact prefixLift 331851
  have htrace : WordTrace (prefixWord ++ tailWord_331851) baseStart_331851 baseEnd_331851 := by
    simpa [prefixWord, tailWord_331851, baseEnd_331851] using wordTrace_append hprefix tailTrace_331851
  have hstable : (prefixWord ++ tailWord_331851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331851).length < 2 ^ (prefixWord ++ tailWord_331851).sum := by decide
  have hdescent : baseEnd_331851 < baseStart_331851 := by decide
  rcases family_descends (prefixWord ++ tailWord_331851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331862 : List Nat := [5, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_331862 : Nat := 118140960795 + 331862 * 2 ^ 59
def prefixEnd_331862 : Nat := 4983230072969 + 3 ^ 40 * 331862 * 2
def baseEnd_331862 : Nat := 56801572320828607366267

theorem tailTrace_331862 : CollatzResearch.WordTrace tailWord_331862 prefixEnd_331862 56801572320828607366267 := by
  unfold tailWord_331862
  simp only [CollatzResearch.WordTrace]
  refine ⟨756500095233007897648865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8069334349152084241587893 756500095233007897648865)
  ·
    refine ⟨567375071424755923236649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756500095233007897648865 567375071424755923236649)
    ·
      refine ⟨425531303568566942427487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567375071424755923236649 425531303568566942427487)
      ·
        refine ⟨638296955352850413641231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425531303568566942427487 638296955352850413641231)
        ·
          refine ⟨957445433029275620461847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638296955352850413641231 957445433029275620461847)
          ·
            refine ⟨1436168149543913430692771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957445433029275620461847 1436168149543913430692771)
            ·
              refine ⟨2154252224315870146039157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436168149543913430692771 2154252224315870146039157)
              ·
                refine ⟨201961146029612826191171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2154252224315870146039157 201961146029612826191171)
                ·
                  refine ⟨302941719044419239286757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201961146029612826191171 302941719044419239286757)
                  ·
                    refine ⟨56801572320828607366267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302941719044419239286757 56801572320828607366267)
                    ·
                      rfl

theorem cell23_331862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_331862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331862 prefixEnd_331862 := by exact prefixLift 331862
  have htrace : WordTrace (prefixWord ++ tailWord_331862) baseStart_331862 baseEnd_331862 := by
    simpa [prefixWord, tailWord_331862, baseEnd_331862] using wordTrace_append hprefix tailTrace_331862
  have hstable : (prefixWord ++ tailWord_331862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331862).length < 2 ^ (prefixWord ++ tailWord_331862).sum := by decide
  have hdescent : baseEnd_331862 < baseStart_331862 := by decide
  rcases family_descends (prefixWord ++ tailWord_331862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331885 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_331885 : Nat := 118140960795 + 331885 * 2 ^ 59
def prefixEnd_331885 : Nat := 4983230072969 + 3 ^ 40 * 331885 * 2
def baseEnd_331885 : Nat := 170416527017539232111195

theorem tailTrace_331885 : CollatzResearch.WordTrace tailWord_331885 prefixEnd_331885 170416527017539232111195 := by
  unfold tailWord_331885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104840402644801290469109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8069893601763200860312739 12104840402644801290469109)
  ·
    refine ⟨1134828787747950120981479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12104840402644801290469109 1134828787747950120981479)
    ·
      refine ⟨1702243181621925181472219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134828787747950120981479 1702243181621925181472219)
      ·
        refine ⟨2553364772432887772208329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702243181621925181472219 2553364772432887772208329)
        ·
          refine ⟨1915023579324665829156247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553364772432887772208329 1915023579324665829156247)
          ·
            refine ⟨2872535368986998743734371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915023579324665829156247 2872535368986998743734371)
            ·
              refine ⟨4308803053480498115601557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872535368986998743734371 4308803053480498115601557)
              ·
                refine ⟨201975143131898349168823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4308803053480498115601557 201975143131898349168823)
                ·
                  refine ⟨302962714697847523753235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201975143131898349168823 302962714697847523753235)
                  ·
                    refine ⟨454444072046771285629853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302962714697847523753235 454444072046771285629853)
                    ·
                      refine ⟨170416527017539232111195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454444072046771285629853 170416527017539232111195)
                      ·
                        rfl

theorem cell23_331885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_331885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331885 prefixEnd_331885 := by exact prefixLift 331885
  have htrace : WordTrace (prefixWord ++ tailWord_331885) baseStart_331885 baseEnd_331885 := by
    simpa [prefixWord, tailWord_331885, baseEnd_331885] using wordTrace_append hprefix tailTrace_331885
  have hstable : (prefixWord ++ tailWord_331885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331885).length < 2 ^ (prefixWord ++ tailWord_331885).sum := by decide
  have hdescent : baseEnd_331885 < baseStart_331885 := by decide
  rcases family_descends (prefixWord ++ tailWord_331885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331901 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_331901 : Nat := 118140960795 + 331901 * 2 ^ 59
def prefixEnd_331901 : Nat := 4983230072969 + 3 ^ 40 * 331901 * 2
def baseEnd_331901 : Nat := 56808247569337056503707

theorem tailTrace_331901 : CollatzResearch.WordTrace tailWord_331901 prefixEnd_331901 56808247569337056503707 := by
  unfold tailWord_331901
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105423970586836023051557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8070282647057890682034371 12105423970586836023051557)
  ·
    refine ⟨2269766994485031754322167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12105423970586836023051557 2269766994485031754322167)
    ·
      refine ⟨3404650491727547631483251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269766994485031754322167 3404650491727547631483251)
      ·
        refine ⟨5106975737591321447224877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404650491727547631483251 5106975737591321447224877)
        ·
          refine ⟨1915115901596745542709329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5106975737591321447224877 1915115901596745542709329)
          ·
            refine ⟨1436336926197559157031997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915115901596745542709329 1436336926197559157031997)
            ·
              refine ⟨538626347324084683886999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1436336926197559157031997 538626347324084683886999)
              ·
                refine ⟨807939520986127025830499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538626347324084683886999 807939520986127025830499)
                ·
                  refine ⟨1211909281479190538745749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807939520986127025830499 1211909281479190538745749)
                  ·
                    refine ⟨56808247569337056503707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1211909281479190538745749 56808247569337056503707)
                    ·
                      rfl

theorem cell23_331901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_331901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331901 prefixEnd_331901 := by exact prefixLift 331901
  have htrace : WordTrace (prefixWord ++ tailWord_331901) baseStart_331901 baseEnd_331901 := by
    simpa [prefixWord, tailWord_331901, baseEnd_331901] using wordTrace_append hprefix tailTrace_331901
  have hstable : (prefixWord ++ tailWord_331901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331901).length < 2 ^ (prefixWord ++ tailWord_331901).sum := by decide
  have hdescent : baseEnd_331901 < baseStart_331901 := by decide
  rcases family_descends (prefixWord ++ tailWord_331901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331908 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_331908 : Nat := 118140960795 + 331908 * 2 ^ 59
def prefixEnd_331908 : Nat := 4983230072969 + 3 ^ 40 * 331908 * 2
def baseEnd_331908 : Nat := 170428337072592642123589

theorem tailTrace_331908 : CollatzResearch.WordTrace tailWord_331908 prefixEnd_331908 170428337072592642123589 := by
  unfold tailWord_331908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052839640780738109278189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8070452854374317479037585 6052839640780738109278189)
  ·
    refine ⟨2269814865292776790979321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6052839640780738109278189 2269814865292776790979321)
    ·
      refine ⟨1702361148969582593234491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269814865292776790979321 1702361148969582593234491)
      ·
        refine ⟨2553541723454373889851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702361148969582593234491 2553541723454373889851737)
        ·
          refine ⟨1915156292590780417388803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553541723454373889851737 1915156292590780417388803)
          ·
            refine ⟨2872734438886170626083205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915156292590780417388803 2872734438886170626083205)
            ·
              refine ⟨538637707291156992390601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2872734438886170626083205 538637707291156992390601)
              ·
                refine ⟨403978280468367744292951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538637707291156992390601 403978280468367744292951)
                ·
                  refine ⟨605967420702551616439427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403978280468367744292951 605967420702551616439427)
                  ·
                    refine ⟨908951131053827424659141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605967420702551616439427 908951131053827424659141)
                    ·
                      refine ⟨170428337072592642123589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 908951131053827424659141 170428337072592642123589)
                      ·
                        rfl

theorem cell23_331908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_331908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331908 prefixEnd_331908 := by exact prefixLift 331908
  have htrace : WordTrace (prefixWord ++ tailWord_331908) baseStart_331908 baseEnd_331908 := by
    simpa [prefixWord, tailWord_331908, baseEnd_331908] using wordTrace_append hprefix tailTrace_331908
  have hstable : (prefixWord ++ tailWord_331908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331908).length < 2 ^ (prefixWord ++ tailWord_331908).sum := by decide
  have hdescent : baseEnd_331908 < baseStart_331908 := by decide
  rcases family_descends (prefixWord ++ tailWord_331908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331911 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_331911 : Nat := 118140960795 + 331911 * 2 ^ 59
def prefixEnd_331911 : Nat := 4983230072969 + 3 ^ 40 * 331911 * 2
def baseEnd_331911 : Nat := 170429877514556130386075

theorem tailTrace_331911 : CollatzResearch.WordTrace tailWord_331911 prefixEnd_331911 170429877514556130386075 := by
  unfold tailWord_331911
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105788700550607730915587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8070525800367071820610391 12105788700550607730915587)
  ·
    refine ⟨18158683050825911596373381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12105788700550607730915587 18158683050825911596373381)
    ·
      refine ⟨3404753072029858424320009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18158683050825911596373381 3404753072029858424320009)
      ·
        refine ⟨2553564804022393818240007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3404753072029858424320009 2553564804022393818240007)
        ·
          refine ⟨3830347206033590727360011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553564804022393818240007 3830347206033590727360011)
          ·
            refine ⟨5745520809050386091040017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830347206033590727360011 5745520809050386091040017)
            ·
              refine ⟨4309140606787789568280013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745520809050386091040017 4309140606787789568280013)
              ·
                refine ⟨1615927727545421088105005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4309140606787789568280013 1615927727545421088105005)
                ·
                  refine ⟨605972897829532908039377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1615927727545421088105005 605972897829532908039377)
                  ·
                    refine ⟨454479673372149681029533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605972897829532908039377 454479673372149681029533)
                    ·
                      refine ⟨170429877514556130386075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454479673372149681029533 170429877514556130386075)
                      ·
                        rfl

theorem cell23_331911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_331911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331911 prefixEnd_331911 := by exact prefixLift 331911
  have htrace : WordTrace (prefixWord ++ tailWord_331911) baseStart_331911 baseEnd_331911 := by
    simpa [prefixWord, tailWord_331911, baseEnd_331911] using wordTrace_append hprefix tailTrace_331911
  have hstable : (prefixWord ++ tailWord_331911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331911).length < 2 ^ (prefixWord ++ tailWord_331911).sum := by decide
  have hdescent : baseEnd_331911 < baseStart_331911 := by decide
  rcases family_descends (prefixWord ++ tailWord_331911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331928 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_331928 : Nat := 118140960795 + 331928 * 2 ^ 59
def prefixEnd_331928 : Nat := 4983230072969 + 3 ^ 40 * 331928 * 2
def baseEnd_331928 : Nat := 170438606685682563873497

theorem tailTrace_331928 : CollatzResearch.WordTrace tailWord_331928 prefixEnd_331928 170438606685682563873497 := by
  unfold tailWord_331928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053204370744509817142219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8070939160992679756189625 6053204370744509817142219)
  ·
    refine ⟨9079806556116764725713329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6053204370744509817142219 9079806556116764725713329)
    ·
      refine ⟨6809854917087573544284997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9079806556116764725713329 6809854917087573544284997)
      ·
        refine ⟨1276847796953920039553437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6809854917087573544284997 1276847796953920039553437)
        ·
          refine ⟨478817923857720014832539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276847796953920039553437 478817923857720014832539)
          ·
            refine ⟨718226885786580022248809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478817923857720014832539 718226885786580022248809)
            ·
              refine ⟨538670164339935016686607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718226885786580022248809 538670164339935016686607)
              ·
                refine ⟨808005246509902525029911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538670164339935016686607 808005246509902525029911)
                ·
                  refine ⟨1212007869764853787544867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808005246509902525029911 1212007869764853787544867)
                  ·
                    refine ⟨1818011804647280681317301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1212007869764853787544867 1818011804647280681317301)
                    ·
                      refine ⟨170438606685682563873497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1818011804647280681317301 170438606685682563873497)
                      ·
                        rfl

theorem cell23_331928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_331928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331928 prefixEnd_331928 := by exact prefixLift 331928
  have htrace : WordTrace (prefixWord ++ tailWord_331928) baseStart_331928 baseEnd_331928 := by
    simpa [prefixWord, tailWord_331928, baseEnd_331928] using wordTrace_append hprefix tailTrace_331928
  have hstable : (prefixWord ++ tailWord_331928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331928).length < 2 ^ (prefixWord ++ tailWord_331928).sum := by decide
  have hdescent : baseEnd_331928 < baseStart_331928 := by decide
  rcases family_descends (prefixWord ++ tailWord_331928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331951 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 2, 7, 2]
def baseStart_331951 : Nat := 118140960795 + 331951 * 2 ^ 59
def prefixEnd_331951 : Nat := 4983230072969 + 3 ^ 40 * 331951 * 2
def baseEnd_331951 : Nat := 170450416740735973885891

theorem tailTrace_331951 : CollatzResearch.WordTrace tailWord_331951 prefixEnd_331951 170450416740735973885891 := by
  unfold tailWord_331951
  simp only [CollatzResearch.WordTrace]
  refine ⟨12107247620405694562371707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8071498413603796374914471 12107247620405694562371707)
  ·
    refine ⟨18160871430608541843557561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12107247620405694562371707 18160871430608541843557561)
    ·
      refine ⟨13620653572956406382668171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18160871430608541843557561 13620653572956406382668171)
      ·
        refine ⟨20430980359434609574002257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13620653572956406382668171 20430980359434609574002257)
        ·
          refine ⟨15323235269575957180501693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20430980359434609574002257 15323235269575957180501693)
          ·
            refine ⟨5746213226090983942688135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15323235269575957180501693 5746213226090983942688135)
            ·
              refine ⟨8619319839136475914032203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746213226090983942688135 8619319839136475914032203)
              ·
                refine ⟨12928979758704713871048305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8619319839136475914032203 12928979758704713871048305)
                ·
                  refine ⟨9696734819028535403286229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12928979758704713871048305 9696734819028535403286229)
                  ·
                    refine ⟨227267222320981298514521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9696734819028535403286229 227267222320981298514521)
                    ·
                      refine ⟨170450416740735973885891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227267222320981298514521 170450416740735973885891)
                      ·
                        rfl

theorem cell23_331951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7, 2].length) (baseStart_331951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331951 prefixEnd_331951 := by exact prefixLift 331951
  have htrace : WordTrace (prefixWord ++ tailWord_331951) baseStart_331951 baseEnd_331951 := by
    simpa [prefixWord, tailWord_331951, baseEnd_331951] using wordTrace_append hprefix tailTrace_331951
  have hstable : (prefixWord ++ tailWord_331951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331951).length < 2 ^ (prefixWord ++ tailWord_331951).sum := by decide
  have hdescent : baseEnd_331951 < baseStart_331951 := by decide
  rcases family_descends (prefixWord ++ tailWord_331951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331956 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_331956 : Nat := 118140960795 + 331956 * 2 ^ 59
def prefixEnd_331956 : Nat := 4983230072969 + 3 ^ 40 * 331956 * 2
def baseEnd_331956 : Nat := 56817661381336151441123

theorem tailTrace_331956 : CollatzResearch.WordTrace tailWord_331956 prefixEnd_331956 56817661381336151441123 := by
  unfold tailWord_331956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053714992693790208151861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8071619990258386944202481 6053714992693790208151861)
  ·
    refine ⟨567535780565042832014237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6053714992693790208151861 567535780565042832014237)
    ·
      refine ⟨212825917711891062005339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 567535780565042832014237 212825917711891062005339)
      ·
        refine ⟨319238876567836593008009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212825917711891062005339 319238876567836593008009)
        ·
          refine ⟨239429157425877444756007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319238876567836593008009 239429157425877444756007)
          ·
            refine ⟨359143736138816167134011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239429157425877444756007 359143736138816167134011)
            ·
              refine ⟨538715604208224250701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359143736138816167134011 538715604208224250701017)
              ·
                refine ⟨404036703156168188025763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538715604208224250701017 404036703156168188025763)
                ·
                  refine ⟨606055054734252282038645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404036703156168188025763 606055054734252282038645)
                  ·
                    refine ⟨56817661381336151441123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 606055054734252282038645 56817661381336151441123)
                    ·
                      rfl

theorem cell23_331956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_331956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_331956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_331956 prefixEnd_331956 := by exact prefixLift 331956
  have htrace : WordTrace (prefixWord ++ tailWord_331956) baseStart_331956 baseEnd_331956 := by
    simpa [prefixWord, tailWord_331956, baseEnd_331956] using wordTrace_append hprefix tailTrace_331956
  have hstable : (prefixWord ++ tailWord_331956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331956).length < 2 ^ (prefixWord ++ tailWord_331956).sum := by decide
  have hdescent : baseEnd_331956 < baseStart_331956 := by decide
  rcases family_descends (prefixWord ++ tailWord_331956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332001 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_332001 : Nat := 118140960795 + 332001 * 2 ^ 59
def prefixEnd_332001 : Nat := 4983230072969 + 3 ^ 40 * 332001 * 2
def baseEnd_332001 : Nat := 170476090773460778260661

theorem tailTrace_332001 : CollatzResearch.WordTrace tailWord_332001 prefixEnd_332001 170476090773460778260661 := by
  unfold tailWord_332001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109071270224553101691857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8072714180149702067794571 12109071270224553101691857)
  ·
    refine ⟨9081803452668414826268893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12109071270224553101691857 9081803452668414826268893)
    ·
      refine ⟨3405676294750655559850835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9081803452668414826268893 3405676294750655559850835)
      ·
        refine ⟨5108514442125983339776253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405676294750655559850835 5108514442125983339776253)
        ·
          refine ⟨1915692915797243752416095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5108514442125983339776253 1915692915797243752416095)
          ·
            refine ⟨2873539373695865628624143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915692915797243752416095 2873539373695865628624143)
            ·
              refine ⟨4310309060543798442936215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873539373695865628624143 4310309060543798442936215)
              ·
                refine ⟨6465463590815697664404323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310309060543798442936215 6465463590815697664404323)
                ·
                  refine ⟨9698195386223546496606485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465463590815697664404323 9698195386223546496606485)
                  ·
                    refine ⟨454602908729228742028429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9698195386223546496606485 454602908729228742028429)
                    ·
                      refine ⟨170476090773460778260661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454602908729228742028429 170476090773460778260661)
                      ·
                        rfl

theorem cell23_332001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_332001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332001 prefixEnd_332001 := by exact prefixLift 332001
  have htrace : WordTrace (prefixWord ++ tailWord_332001) baseStart_332001 baseEnd_332001 := by
    simpa [prefixWord, tailWord_332001, baseEnd_332001] using wordTrace_append hprefix tailTrace_332001
  have hstable : (prefixWord ++ tailWord_332001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332001).length < 2 ^ (prefixWord ++ tailWord_332001).sum := by decide
  have hdescent : baseEnd_332001 < baseStart_332001 := by decide
  rcases family_descends (prefixWord ++ tailWord_332001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332011 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_332011 : Nat := 118140960795 + 332011 * 2 ^ 59
def prefixEnd_332011 : Nat := 4983230072969 + 3 ^ 40 * 332011 * 2
def baseEnd_332011 : Nat := 170481225580005739135615

theorem tailTrace_332011 : CollatzResearch.WordTrace tailWord_332011 prefixEnd_332011 170481225580005739135615 := by
  unfold tailWord_332011
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109436000188324809555887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8072957333458883206370591 12109436000188324809555887)
  ·
    refine ⟨18164154000282487214333831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109436000188324809555887 18164154000282487214333831)
    ·
      refine ⟨27246231000423730821500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18164154000282487214333831 27246231000423730821500747)
      ·
        refine ⟨40869346500635596232251121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27246231000423730821500747 40869346500635596232251121)
        ·
          refine ⟨30652009875476697174188341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40869346500635596232251121 30652009875476697174188341)
          ·
            refine ⟨2873625925825940360080157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30652009875476697174188341 2873625925825940360080157)
            ·
              refine ⟨1077609722184727635030059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2873625925825940360080157 1077609722184727635030059)
              ·
                refine ⟨1616414583277091452545089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077609722184727635030059 1616414583277091452545089)
                ·
                  refine ⟨1212310937457818589408817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1616414583277091452545089 1212310937457818589408817)
                  ·
                    refine ⟨909233203093363942056613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1212310937457818589408817 909233203093363942056613)
                    ·
                      refine ⟨170481225580005739135615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 909233203093363942056613 170481225580005739135615)
                      ·
                        rfl

theorem cell23_332011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_332011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332011 prefixEnd_332011 := by exact prefixLift 332011
  have htrace : WordTrace (prefixWord ++ tailWord_332011) baseStart_332011 baseEnd_332011 := by
    simpa [prefixWord, tailWord_332011, baseEnd_332011] using wordTrace_append hprefix tailTrace_332011
  have hstable : (prefixWord ++ tailWord_332011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332011).length < 2 ^ (prefixWord ++ tailWord_332011).sum := by decide
  have hdescent : baseEnd_332011 < baseStart_332011 := by decide
  rcases family_descends (prefixWord ++ tailWord_332011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332015 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 1, 4, 2]
def baseStart_332015 : Nat := 118140960795 + 332015 * 2 ^ 59
def prefixEnd_332015 : Nat := 4983230072969 + 3 ^ 40 * 332015 * 2
def baseEnd_332015 : Nat := 170483279502623723485597

theorem tailTrace_332015 : CollatzResearch.WordTrace tailWord_332015 prefixEnd_332015 170483279502623723485597 := by
  unfold tailWord_332015
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109581892173833492701499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8073054594782555661800999 12109581892173833492701499)
  ·
    refine ⟨18164372838260750239052249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109581892173833492701499 18164372838260750239052249)
    ·
      refine ⟨13623279628695562679289187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18164372838260750239052249 13623279628695562679289187)
      ·
        refine ⟨20434919443043344018933781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13623279628695562679289187 20434919443043344018933781)
        ·
          refine ⟨957886848892656750887521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20434919443043344018933781 957886848892656750887521)
          ·
            refine ⟨718415136669492563165641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957886848892656750887521 718415136669492563165641)
            ·
              refine ⟨538811352502119422374231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718415136669492563165641 538811352502119422374231)
              ·
                refine ⟨808217028753179133561347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538811352502119422374231 808217028753179133561347)
                ·
                  refine ⟨1212325543129768700342021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808217028753179133561347 1212325543129768700342021)
                  ·
                    refine ⟨227311039336831631314129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212325543129768700342021 227311039336831631314129)
                    ·
                      refine ⟨170483279502623723485597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227311039336831631314129 170483279502623723485597)
                      ·
                        rfl

theorem cell23_332015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4, 2].length) (baseStart_332015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332015 prefixEnd_332015 := by exact prefixLift 332015
  have htrace : WordTrace (prefixWord ++ tailWord_332015) baseStart_332015 baseEnd_332015 := by
    simpa [prefixWord, tailWord_332015, baseEnd_332015] using wordTrace_append hprefix tailTrace_332015
  have hstable : (prefixWord ++ tailWord_332015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332015).length < 2 ^ (prefixWord ++ tailWord_332015).sum := by decide
  have hdescent : baseEnd_332015 < baseStart_332015 := by decide
  rcases family_descends (prefixWord ++ tailWord_332015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332031 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_332031 : Nat := 118140960795 + 332031 * 2 ^ 59
def prefixEnd_332031 : Nat := 4983230072969 + 3 ^ 40 * 332031 * 2
def baseEnd_332031 : Nat := 170491495193095660885523

theorem tailTrace_332031 : CollatzResearch.WordTrace tailWord_332031 prefixEnd_332031 170491495193095660885523 := by
  unfold tailWord_332031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110165460115868225283947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8073443640077245483522631 12110165460115868225283947)
  ·
    refine ⟨18165248190173802337925921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12110165460115868225283947 18165248190173802337925921)
    ·
      refine ⟨13623936142630351753444441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18165248190173802337925921 13623936142630351753444441)
      ·
        refine ⟨10217952106972763815083331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13623936142630351753444441 10217952106972763815083331)
        ·
          refine ⟨15326928160459145722624997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10217952106972763815083331 15326928160459145722624997)
          ·
            refine ⟨2873799030086089822992187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15326928160459145722624997 2873799030086089822992187)
            ·
              refine ⟨4310698545129134734488281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873799030086089822992187 4310698545129134734488281)
              ·
                refine ⟨3233023908846851050866211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310698545129134734488281 3233023908846851050866211)
                ·
                  refine ⟨4849535863270276576299317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233023908846851050866211 4849535863270276576299317)
                  ·
                    refine ⟨454643987181588429028061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4849535863270276576299317 454643987181588429028061)
                    ·
                      refine ⟨170491495193095660885523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 454643987181588429028061 170491495193095660885523)
                      ·
                        rfl

theorem cell23_332031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_332031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332031 prefixEnd_332031 := by exact prefixLift 332031
  have htrace : WordTrace (prefixWord ++ tailWord_332031) baseStart_332031 baseEnd_332031 := by
    simpa [prefixWord, tailWord_332031, baseEnd_332031] using wordTrace_append hprefix tailTrace_332031
  have hstable : (prefixWord ++ tailWord_332031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332031).length < 2 ^ (prefixWord ++ tailWord_332031).sum := by decide
  have hdescent : baseEnd_332031 < baseStart_332031 := by decide
  rcases family_descends (prefixWord ++ tailWord_332031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332036 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_332036 : Nat := 118140960795 + 332036 * 2 ^ 59
def prefixEnd_332036 : Nat := 4983230072969 + 3 ^ 40 * 332036 * 2
def baseEnd_332036 : Nat := 170494062596368141323001

theorem tailTrace_332036 : CollatzResearch.WordTrace tailWord_332036 prefixEnd_332036 170494062596368141323001 := by
  unfold tailWord_332036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055173912548877039607981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8073565216731836052810641 6055173912548877039607981)
  ·
    refine ⟨2270690217205828889852993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6055173912548877039607981 2270690217205828889852993)
    ·
      refine ⟨1703017662904371667389745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2270690217205828889852993 1703017662904371667389745)
      ·
        refine ⟨1277263247178278750542309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1703017662904371667389745 1277263247178278750542309)
        ·
          refine ⟨239486858845927265726683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1277263247178278750542309 239486858845927265726683)
          ·
            refine ⟨359230288268890898590025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239486858845927265726683 359230288268890898590025)
            ·
              refine ⟨269422716201668173942519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359230288268890898590025 269422716201668173942519)
              ·
                refine ⟨404134074302502260913779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269422716201668173942519 404134074302502260913779)
                ·
                  refine ⟨606201111453753391370669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404134074302502260913779 606201111453753391370669)
                  ·
                    refine ⟨227325416795157521764001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 606201111453753391370669 227325416795157521764001)
                    ·
                      refine ⟨170494062596368141323001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227325416795157521764001 170494062596368141323001)
                      ·
                        rfl

theorem cell23_332036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_332036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332036 prefixEnd_332036 := by exact prefixLift 332036
  have htrace : WordTrace (prefixWord ++ tailWord_332036) baseStart_332036 baseEnd_332036 := by
    simpa [prefixWord, tailWord_332036, baseEnd_332036] using wordTrace_append hprefix tailTrace_332036
  have hstable : (prefixWord ++ tailWord_332036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332036).length < 2 ^ (prefixWord ++ tailWord_332036).sum := by decide
  have hdescent : baseEnd_332036 < baseStart_332036 := by decide
  rcases family_descends (prefixWord ++ tailWord_332036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332051 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 2, 5]
def baseStart_332051 : Nat := 118140960795 + 332051 * 2 ^ 59
def prefixEnd_332051 : Nat := 4983230072969 + 3 ^ 40 * 332051 * 2
def baseEnd_332051 : Nat := 56833921602061860878477

theorem tailTrace_332051 : CollatzResearch.WordTrace tailWord_332051 prefixEnd_332051 56833921602061860878477 := by
  unfold tailWord_332051
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110894920043411641012007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8073929946695607760674671 12110894920043411641012007)
  ·
    refine ⟨18166342380065117461518011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12110894920043411641012007 18166342380065117461518011)
    ·
      refine ⟨27249513570097676192277017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18166342380065117461518011 27249513570097676192277017)
      ·
        refine ⟨20437135177573257144207763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27249513570097676192277017 20437135177573257144207763)
        ·
          refine ⟨30655702766359885716311645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437135177573257144207763 30655702766359885716311645)
          ·
            refine ⟨11495888537384957143616867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30655702766359885716311645 11495888537384957143616867)
            ·
              refine ⟨17243832806077435715425301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495888537384957143616867 17243832806077435715425301)
              ·
                refine ⟨808304662784879799160561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17243832806077435715425301 808304662784879799160561)
                ·
                  refine ⟨606228497088659849370421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808304662784879799160561 606228497088659849370421)
                  ·
                    refine ⟨56833921602061860878477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 606228497088659849370421 56833921602061860878477)
                    ·
                      rfl

theorem cell23_332051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].length) (baseStart_332051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332051 prefixEnd_332051 := by exact prefixLift 332051
  have htrace : WordTrace (prefixWord ++ tailWord_332051) baseStart_332051 baseEnd_332051 := by
    simpa [prefixWord, tailWord_332051, baseEnd_332051] using wordTrace_append hprefix tailTrace_332051
  have hstable : (prefixWord ++ tailWord_332051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332051).length < 2 ^ (prefixWord ++ tailWord_332051).sum := by decide
  have hdescent : baseEnd_332051 < baseStart_332051 := by decide
  rcases family_descends (prefixWord ++ tailWord_332051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332088 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_332088 : Nat := 118140960795 + 332088 * 2 ^ 59
def prefixEnd_332088 : Nat := 4983230072969 + 3 ^ 40 * 332088 * 2
def baseEnd_332088 : Nat := 170520763590401937872761

theorem tailTrace_332088 : CollatzResearch.WordTrace tailWord_332088 prefixEnd_332088 170520763590401937872761 := by
  unfold tailWord_332088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056122210454683480054459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8074829613939577973405945 6056122210454683480054459)
  ·
    refine ⟨9084183315682025220081689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6056122210454683480054459 9084183315682025220081689)
    ·
      refine ⟨6813137486761518915061267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9084183315682025220081689 6813137486761518915061267)
      ·
        refine ⟨10219706230142278372591901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813137486761518915061267 10219706230142278372591901)
        ·
          refine ⟨3832389836303354389721963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10219706230142278372591901 3832389836303354389721963)
          ·
            refine ⟨5748584754455031584582945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832389836303354389721963 5748584754455031584582945)
            ·
              refine ⟨4311438565841273688437209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748584754455031584582945 4311438565841273688437209)
              ·
                refine ⟨3233578924380955266327907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311438565841273688437209 3233578924380955266327907)
                ·
                  refine ⟨4850368386571432899491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233578924380955266327907 4850368386571432899491861)
                  ·
                    refine ⟨227361018120535917163681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4850368386571432899491861 227361018120535917163681)
                    ·
                      refine ⟨170520763590401937872761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227361018120535917163681 170520763590401937872761)
                      ·
                        rfl

theorem cell23_332088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_332088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332088 prefixEnd_332088 := by exact prefixLift 332088
  have htrace : WordTrace (prefixWord ++ tailWord_332088) baseStart_332088 baseEnd_332088 := by
    simpa [prefixWord, tailWord_332088, baseEnd_332088] using wordTrace_append hprefix tailTrace_332088
  have hstable : (prefixWord ++ tailWord_332088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332088).length < 2 ^ (prefixWord ++ tailWord_332088).sum := by decide
  have hdescent : baseEnd_332088 < baseStart_332088 := by decide
  rcases family_descends (prefixWord ++ tailWord_332088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332151 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_332151 : Nat := 118140960795 + 332151 * 2 ^ 59
def prefixEnd_332151 : Nat := 4983230072969 + 3 ^ 40 * 332151 * 2
def baseEnd_332151 : Nat := 170553112871635191384971

theorem tailTrace_332151 : CollatzResearch.WordTrace tailWord_332151 prefixEnd_332151 170553112871635191384971 := by
  unfold tailWord_332151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114542219681128719652307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076361479787419146434871 12114542219681128719652307)
  ·
    refine ⟨18171813329521693079478461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12114542219681128719652307 18171813329521693079478461)
    ·
      refine ⟨6814429998570634904804423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18171813329521693079478461 6814429998570634904804423)
      ·
        refine ⟨10221644997855952357206635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814429998570634904804423 10221644997855952357206635)
        ·
          refine ⟨15332467496783928535809953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10221644997855952357206635 15332467496783928535809953)
          ·
            refine ⟨11499350622587946401857465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15332467496783928535809953 11499350622587946401857465)
            ·
              refine ⟨8624512966940959801393099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11499350622587946401857465 8624512966940959801393099)
              ·
                refine ⟨12936769450411439702089649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624512966940959801393099 12936769450411439702089649)
                ·
                  refine ⟨9702577087808579776567237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12936769450411439702089649 9702577087808579776567237)
                  ·
                    refine ⟨1819233203964108708106357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9702577087808579776567237 1819233203964108708106357)
                    ·
                      refine ⟨170553112871635191384971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1819233203964108708106357 170553112871635191384971)
                      ·
                        rfl

theorem cell23_332151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_332151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332151 prefixEnd_332151 := by exact prefixLift 332151
  have htrace : WordTrace (prefixWord ++ tailWord_332151) baseStart_332151 baseEnd_332151 := by
    simpa [prefixWord, tailWord_332151, baseEnd_332151] using wordTrace_append hprefix tailTrace_332151
  have hstable : (prefixWord ++ tailWord_332151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332151).length < 2 ^ (prefixWord ++ tailWord_332151).sum := by decide
  have hdescent : baseEnd_332151 < baseStart_332151 := by decide
  rcases family_descends (prefixWord ++ tailWord_332151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332199 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_332199 : Nat := 118140960795 + 332199 * 2 ^ 59
def prefixEnd_332199 : Nat := 4983230072969 + 3 ^ 40 * 332199 * 2
def baseEnd_332199 : Nat := 170577759943051003584751

theorem tailTrace_332199 : CollatzResearch.WordTrace tailWord_332199 prefixEnd_332199 170577759943051003584751 := by
  unfold tailWord_332199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116292923507232917399651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8077528615671488611599767 12116292923507232917399651)
  ·
    refine ⟨18174439385260849376099477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12116292923507232917399651 18174439385260849376099477)
    ·
      refine ⟨851926846184102314504663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18174439385260849376099477 851926846184102314504663)
      ·
        refine ⟨1277890269276153471756995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851926846184102314504663 1277890269276153471756995)
        ·
          refine ⟨1916835403914230207635493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277890269276153471756995 1916835403914230207635493)
          ·
            refine ⟨359406638233918163931655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1916835403914230207635493 359406638233918163931655)
            ·
              refine ⟨539109957350877245897483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359406638233918163931655 539109957350877245897483)
              ·
                refine ⟨808664936026315868846225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539109957350877245897483 808664936026315868846225)
                ·
                  refine ⟨606498702019736901634669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808664936026315868846225 606498702019736901634669)
                  ·
                    refine ⟨227437013257401338113001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 606498702019736901634669 227437013257401338113001)
                    ·
                      refine ⟨170577759943051003584751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227437013257401338113001 170577759943051003584751)
                      ·
                        rfl

theorem cell23_332199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_332199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332199 prefixEnd_332199 := by exact prefixLift 332199
  have htrace : WordTrace (prefixWord ++ tailWord_332199) baseStart_332199 baseEnd_332199 := by
    simpa [prefixWord, tailWord_332199, baseEnd_332199] using wordTrace_append hprefix tailTrace_332199
  have hstable : (prefixWord ++ tailWord_332199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332199).length < 2 ^ (prefixWord ++ tailWord_332199).sum := by decide
  have hdescent : baseEnd_332199 < baseStart_332199 := by decide
  rcases family_descends (prefixWord ++ tailWord_332199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332201 : List Nat := [1, 2, 1, 1, 1, 1, 3, 13]
def baseStart_332201 : Nat := 118140960795 + 332201 * 2 ^ 59
def prefixEnd_332201 : Nat := 4983230072969 + 3 ^ 40 * 332201 * 2
def baseEnd_332201 : Nat := 6317732848309629472583

theorem tailTrace_332201 : CollatzResearch.WordTrace tailWord_332201 prefixEnd_332201 6317732848309629472583 := by
  unfold tailWord_332201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116365869499987258972457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8077577246333324839314971 12116365869499987258972457)
  ·
    refine ⟨9087274402124990444229343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12116365869499987258972457 9087274402124990444229343)
    ·
      refine ⟨13630911603187485666344015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087274402124990444229343 13630911603187485666344015)
      ·
        refine ⟨20446367404781228499516023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13630911603187485666344015 20446367404781228499516023)
        ·
          refine ⟨30669551107171842749274035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20446367404781228499516023 30669551107171842749274035)
          ·
            refine ⟨46004326660757764123911053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30669551107171842749274035 46004326660757764123911053)
            ·
              refine ⟨17251622497784161546466645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46004326660757764123911053 17251622497784161546466645)
              ·
                refine ⟨6317732848309629472583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 17251622497784161546466645 6317732848309629472583)
                ·
                  rfl

theorem cell23_332201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 13].length) (baseStart_332201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332201 prefixEnd_332201 := by exact prefixLift 332201
  have htrace : WordTrace (prefixWord ++ tailWord_332201) baseStart_332201 baseEnd_332201 := by
    simpa [prefixWord, tailWord_332201, baseEnd_332201] using wordTrace_append hprefix tailTrace_332201
  have hstable : (prefixWord ++ tailWord_332201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332201).length < 2 ^ (prefixWord ++ tailWord_332201).sum := by decide
  have hdescent : baseEnd_332201 < baseStart_332201 := by decide
  rcases family_descends (prefixWord ++ tailWord_332201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332222 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_332222 : Nat := 118140960795 + 332222 * 2 ^ 59
def prefixEnd_332222 : Nat := 4983230072969 + 3 ^ 40 * 332222 * 2
def baseEnd_332222 : Nat := 56863189999368137865715

theorem tailTrace_332222 : CollatzResearch.WordTrace tailWord_332222 prefixEnd_332222 56863189999368137865715 := by
  unfold tailWord_332222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514641475302988480685865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8078087868282605230324613 1514641475302988480685865)
  ·
    refine ⟨1135981106477241360514399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1514641475302988480685865 1135981106477241360514399)
    ·
      refine ⟨1703971659715862040771599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135981106477241360514399 1703971659715862040771599)
      ·
        refine ⟨2555957489573793061157399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703971659715862040771599 2555957489573793061157399)
        ·
          refine ⟨3833936234360689591736099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555957489573793061157399 3833936234360689591736099)
          ·
            refine ⟨5750904351541034387604149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833936234360689591736099 5750904351541034387604149)
            ·
              refine ⟨539147282956971973837889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5750904351541034387604149 539147282956971973837889)
              ·
                refine ⟨404360462217728980378417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539147282956971973837889 404360462217728980378417)
                ·
                  refine ⟨303270346663296735283813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404360462217728980378417 303270346663296735283813)
                  ·
                    refine ⟨56863189999368137865715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303270346663296735283813 56863189999368137865715)
                    ·
                      rfl

theorem cell23_332222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_332222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332222 prefixEnd_332222 := by exact prefixLift 332222
  have htrace : WordTrace (prefixWord ++ tailWord_332222) baseStart_332222 baseEnd_332222 := by
    simpa [prefixWord, tailWord_332222, baseEnd_332222] using wordTrace_append hprefix tailTrace_332222
  have hstable : (prefixWord ++ tailWord_332222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332222).length < 2 ^ (prefixWord ++ tailWord_332222).sum := by decide
  have hdescent : baseEnd_332222 < baseStart_332222 := by decide
  rcases family_descends (prefixWord ++ tailWord_332222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332242 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_332242 : Nat := 118140960795 + 332242 * 2 ^ 59
def prefixEnd_332242 : Nat := 4983230072969 + 3 ^ 40 * 332242 * 2
def baseEnd_332242 : Nat := 170599839611194335347053

theorem tailTrace_332242 : CollatzResearch.WordTrace tailWord_332242 prefixEnd_332242 170599839611194335347053 := by
  unfold tailWord_332242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029465315587862815303745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8078574174900967507476653 3029465315587862815303745)
  ·
    refine ⟨2272098986690897111477809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3029465315587862815303745 2272098986690897111477809)
    ·
      refine ⟨1704074240018172833608357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2272098986690897111477809 1704074240018172833608357)
      ·
        refine ⟨319513920003407406301567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1704074240018172833608357 319513920003407406301567)
        ·
          refine ⟨479270880005111109452351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319513920003407406301567 479270880005111109452351)
          ·
            refine ⟨718906320007666664178527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479270880005111109452351 718906320007666664178527)
            ·
              refine ⟨1078359480011499996267791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718906320007666664178527 1078359480011499996267791)
              ·
                refine ⟨1617539220017249994401687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078359480011499996267791 1617539220017249994401687)
                ·
                  refine ⟨2426308830025874991602531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617539220017249994401687 2426308830025874991602531)
                  ·
                    refine ⟨3639463245038812487403797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426308830025874991602531 3639463245038812487403797)
                    ·
                      refine ⟨170599839611194335347053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3639463245038812487403797 170599839611194335347053)
                      ·
                        rfl

theorem cell23_332242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_332242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332242 prefixEnd_332242 := by exact prefixLift 332242
  have htrace : WordTrace (prefixWord ++ tailWord_332242) baseStart_332242 baseEnd_332242 := by
    simpa [prefixWord, tailWord_332242, baseEnd_332242] using wordTrace_append hprefix tailTrace_332242
  have hstable : (prefixWord ++ tailWord_332242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332242).length < 2 ^ (prefixWord ++ tailWord_332242).sum := by decide
  have hdescent : baseEnd_332242 < baseStart_332242 := by decide
  rcases family_descends (prefixWord ++ tailWord_332242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332272 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2]
def baseStart_332272 : Nat := 118140960795 + 332272 * 2 ^ 59
def prefixEnd_332272 : Nat := 4983230072969 + 3 ^ 40 * 332272 * 2
def baseEnd_332272 : Nat := 170615244030829217971915

theorem tailTrace_332272 : CollatzResearch.WordTrace tailWord_332272 prefixEnd_332272 170615244030829217971915 := by
  unfold tailWord_332272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059477726121383192403535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8079303634828510923204713 6059477726121383192403535)
  ·
    refine ⟨9089216589182074788605303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6059477726121383192403535 9089216589182074788605303)
    ·
      refine ⟨13633824883773112182907955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089216589182074788605303 13633824883773112182907955)
      ·
        refine ⟨20450737325659668274361933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633824883773112182907955 20450737325659668274361933)
        ·
          refine ⟨7669026497122375602885725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20450737325659668274361933 7669026497122375602885725)
          ·
            refine ⟨2875884936420890851082147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7669026497122375602885725 2875884936420890851082147)
            ·
              refine ⟨4313827404631336276623221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875884936420890851082147 4313827404631336276623221)
              ·
                refine ⟨404421319184187775933427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4313827404631336276623221 404421319184187775933427)
                ·
                  refine ⟨606631978776281663900141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404421319184187775933427 606631978776281663900141)
                  ·
                    refine ⟨227486992041105623962553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 606631978776281663900141 227486992041105623962553)
                    ·
                      refine ⟨170615244030829217971915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227486992041105623962553 170615244030829217971915)
                      ·
                        rfl

theorem cell23_332272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 3, 2].length) (baseStart_332272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332272 prefixEnd_332272 := by exact prefixLift 332272
  have htrace : WordTrace (prefixWord ++ tailWord_332272) baseStart_332272 baseEnd_332272 := by
    simpa [prefixWord, tailWord_332272, baseEnd_332272] using wordTrace_append hprefix tailTrace_332272
  have hstable : (prefixWord ++ tailWord_332272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332272).length < 2 ^ (prefixWord ++ tailWord_332272).sum := by decide
  have hdescent : baseEnd_332272 < baseStart_332272 := by decide
  rcases family_descends (prefixWord ++ tailWord_332272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332368 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_332368 : Nat := 118140960795 + 332368 * 2 ^ 59
def prefixEnd_332368 : Nat := 4983230072969 + 3 ^ 40 * 332368 * 2
def baseEnd_332368 : Nat := 56888179391220280790491

theorem tailTrace_332368 : CollatzResearch.WordTrace tailWord_332368 prefixEnd_332368 56888179391220280790491 := by
  unfold tailWord_332368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061228429947487390150879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8081637906596649853534505 6061228429947487390150879)
  ·
    refine ⟨9091842644921231085226319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6061228429947487390150879 9091842644921231085226319)
    ·
      refine ⟨13637763967381846627839479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9091842644921231085226319 13637763967381846627839479)
      ·
        refine ⟨20456645951072769941759219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637763967381846627839479 20456645951072769941759219)
        ·
          refine ⟨30684968926609154912638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20456645951072769941759219 30684968926609154912638829)
          ·
            refine ⟨11506863347478433092239561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30684968926609154912638829 11506863347478433092239561)
            ·
              refine ⟨8630147510608824819179671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11506863347478433092239561 8630147510608824819179671)
              ·
                refine ⟨12945221265913237228769507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8630147510608824819179671 12945221265913237228769507)
                ·
                  refine ⟨19417831898869855843154261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12945221265913237228769507 19417831898869855843154261)
                  ·
                    refine ⟨56888179391220280790491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 19417831898869855843154261 56888179391220280790491)
                    ·
                      rfl

theorem cell23_332368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_332368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332368 prefixEnd_332368 := by exact prefixLift 332368
  have htrace : WordTrace (prefixWord ++ tailWord_332368) baseStart_332368 baseEnd_332368 := by
    simpa [prefixWord, tailWord_332368, baseEnd_332368] using wordTrace_append hprefix tailTrace_332368
  have hstable : (prefixWord ++ tailWord_332368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332368).length < 2 ^ (prefixWord ++ tailWord_332368).sum := by decide
  have hdescent : baseEnd_332368 < baseStart_332368 := by decide
  rcases family_descends (prefixWord ++ tailWord_332368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332372 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_332372 : Nat := 118140960795 + 332372 * 2 ^ 59
def prefixEnd_332372 : Nat := 4983230072969 + 3 ^ 40 * 332372 * 2
def baseEnd_332372 : Nat := 56888864032092942240485

theorem tailTrace_332372 : CollatzResearch.WordTrace tailWord_332372 prefixEnd_332372 56888864032092942240485 := by
  unfold tailWord_332372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061301375940241731723685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8081735167920322308964913 6061301375940241731723685)
  ·
    refine ⟨1136494007988795324698191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6061301375940241731723685 1136494007988795324698191)
    ·
      refine ⟨1704741011983192987047287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136494007988795324698191 1704741011983192987047287)
      ·
        refine ⟨2557111517974789480570931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704741011983192987047287 2557111517974789480570931)
        ·
          refine ⟨3835667276962184220856397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557111517974789480570931 3835667276962184220856397)
          ·
            refine ⟨1438375228860819082821149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3835667276962184220856397 1438375228860819082821149)
            ·
              refine ⟨539390710822807156057931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1438375228860819082821149 539390710822807156057931)
              ·
                refine ⟨809086066234210734086897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539390710822807156057931 809086066234210734086897)
                ·
                  refine ⟨606814549675658050565173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809086066234210734086897 606814549675658050565173)
                  ·
                    refine ⟨56888864032092942240485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 606814549675658050565173 56888864032092942240485)
                    ·
                      rfl

theorem cell23_332372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_332372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332372 prefixEnd_332372 := by exact prefixLift 332372
  have htrace : WordTrace (prefixWord ++ tailWord_332372) baseStart_332372 baseEnd_332372 := by
    simpa [prefixWord, tailWord_332372, baseEnd_332372] using wordTrace_append hprefix tailTrace_332372
  have hstable : (prefixWord ++ tailWord_332372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332372).length < 2 ^ (prefixWord ++ tailWord_332372).sum := by decide
  have hdescent : baseEnd_332372 < baseStart_332372 := by decide
  rcases family_descends (prefixWord ++ tailWord_332372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332375 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_332375 : Nat := 118140960795 + 332375 * 2 ^ 59
def prefixEnd_332375 : Nat := 4983230072969 + 3 ^ 40 * 332375 * 2
def baseEnd_332375 : Nat := 170668132538242314983941

theorem tailTrace_332375 : CollatzResearch.WordTrace tailWord_332375 prefixEnd_332375 170668132538242314983941 := by
  unfold tailWord_332375
  simp only [CollatzResearch.WordTrace]
  refine ⟨12122712170869614975806579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8081808113913076650537719 12122712170869614975806579)
  ·
    refine ⟨18184068256304422463709869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12122712170869614975806579 18184068256304422463709869)
    ·
      refine ⟨6819025596114158423891201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18184068256304422463709869 6819025596114158423891201)
      ·
        refine ⟨5114269197085618817918401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6819025596114158423891201 5114269197085618817918401)
        ·
          refine ⟨3835701897814214113438801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5114269197085618817918401 3835701897814214113438801)
          ·
            refine ⟨2876776423360660585079101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3835701897814214113438801 2876776423360660585079101)
            ·
              refine ⟨1078791158760247719404663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876776423360660585079101 1078791158760247719404663)
              ·
                refine ⟨1618186738140371579106995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078791158760247719404663 1618186738140371579106995)
                ·
                  refine ⟨2427280107210557368660493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618186738140371579106995 2427280107210557368660493)
                  ·
                    refine ⟨910230040203959013247685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2427280107210557368660493 910230040203959013247685)
                    ·
                      refine ⟨170668132538242314983941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 910230040203959013247685 170668132538242314983941)
                      ·
                        rfl

theorem cell23_332375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_332375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332375 prefixEnd_332375 := by exact prefixLift 332375
  have htrace : WordTrace (prefixWord ++ tailWord_332375) baseStart_332375 baseEnd_332375 := by
    simpa [prefixWord, tailWord_332375, baseEnd_332375] using wordTrace_append hprefix tailTrace_332375
  have hstable : (prefixWord ++ tailWord_332375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332375).length < 2 ^ (prefixWord ++ tailWord_332375).sum := by decide
  have hdescent : baseEnd_332375 < baseStart_332375 := by decide
  rcases family_descends (prefixWord ++ tailWord_332375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332425 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_332425 : Nat := 118140960795 + 332425 * 2 ^ 59
def prefixEnd_332425 : Nat := 4983230072969 + 3 ^ 40 * 332425 * 2
def baseEnd_332425 : Nat := 170693806570967119358711

theorem tailTrace_332425 : CollatzResearch.WordTrace tailWord_332425 prefixEnd_332425 170693806570967119358711 := by
  unfold tailWord_332425
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124535820688473515126729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8083023880458982343417819 12124535820688473515126729)
  ·
    refine ⟨9093401865516355136345047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12124535820688473515126729 9093401865516355136345047)
    ·
      refine ⟨13640102798274532704517571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093401865516355136345047 13640102798274532704517571)
      ·
        refine ⟨20460154197411799056776357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13640102798274532704517571 20460154197411799056776357)
        ·
          refine ⟨3836278912014712323145567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20460154197411799056776357 3836278912014712323145567)
          ·
            refine ⟨5754418368022068484718351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836278912014712323145567 5754418368022068484718351)
            ·
              refine ⟨8631627552033102727077527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754418368022068484718351 8631627552033102727077527)
              ·
                refine ⟨12947441328049654090616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8631627552033102727077527 12947441328049654090616291)
                ·
                  refine ⟨19421161992074481135924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12947441328049654090616291 19421161992074481135924437)
                  ·
                    refine ⟨455183484189245651623229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19421161992074481135924437 455183484189245651623229)
                    ·
                      refine ⟨170693806570967119358711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 455183484189245651623229 170693806570967119358711)
                      ·
                        rfl

theorem cell23_332425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_332425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332425 prefixEnd_332425 := by exact prefixLift 332425
  have htrace : WordTrace (prefixWord ++ tailWord_332425) baseStart_332425 baseEnd_332425 := by
    simpa [prefixWord, tailWord_332425, baseEnd_332425] using wordTrace_append hprefix tailTrace_332425
  have hstable : (prefixWord ++ tailWord_332425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332425).length < 2 ^ (prefixWord ++ tailWord_332425).sum := by decide
  have hdescent : baseEnd_332425 < baseStart_332425 := by decide
  rcases family_descends (prefixWord ++ tailWord_332425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332479 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 1, 5]
def baseStart_332479 : Nat := 118140960795 + 332479 * 2 ^ 59
def prefixEnd_332479 : Nat := 4983230072969 + 3 ^ 40 * 332479 * 2
def baseEnd_332479 : Nat := 56907178175436636027821

theorem tailTrace_332479 : CollatzResearch.WordTrace tailWord_332479 prefixEnd_332479 56907178175436636027821 := by
  unfold tailWord_332479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126505362492840737592491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8084336908328560491728327 12126505362492840737592491)
  ·
    refine ⟨18189758043739261106388737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12126505362492840737592491 18189758043739261106388737)
    ·
      refine ⟨13642318532804445829791553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18189758043739261106388737 13642318532804445829791553)
      ·
        refine ⟨10231738899603334372343665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642318532804445829791553 10231738899603334372343665)
        ·
          refine ⟨7673804174702500779257749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10231738899603334372343665 7673804174702500779257749)
          ·
            refine ⟨359709570689179724027707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7673804174702500779257749 359709570689179724027707)
            ·
              refine ⟨539564356033769586041561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359709570689179724027707 539564356033769586041561)
              ·
                refine ⟨404673267025327189531171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539564356033769586041561 404673267025327189531171)
                ·
                  refine ⟨607009900537990784296757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404673267025327189531171 607009900537990784296757)
                  ·
                    refine ⟨56907178175436636027821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 607009900537990784296757 56907178175436636027821)
                    ·
                      rfl

theorem cell23_332479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_332479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332479 prefixEnd_332479 := by exact prefixLift 332479
  have htrace : WordTrace (prefixWord ++ tailWord_332479) baseStart_332479 baseEnd_332479 := by
    simpa [prefixWord, tailWord_332479, baseEnd_332479] using wordTrace_append hprefix tailTrace_332479
  have hstable : (prefixWord ++ tailWord_332479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332479).length < 2 ^ (prefixWord ++ tailWord_332479).sum := by decide
  have hdescent : baseEnd_332479 < baseStart_332479 := by decide
  rcases family_descends (prefixWord ++ tailWord_332479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332492 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_332492 : Nat := 118140960795 + 332492 * 2 ^ 59
def prefixEnd_332492 : Nat := 4983230072969 + 3 ^ 40 * 332492 * 2
def baseEnd_332492 : Nat := 56909403258272785740301

theorem tailTrace_332492 : CollatzResearch.WordTrace tailWord_332492 prefixEnd_332492 56909403258272785740301 := by
  unfold tailWord_332492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063489755722871978907865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8084653007630495971877153 6063489755722871978907865)
  ·
    refine ⟨4547617316792153984180899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6063489755722871978907865 4547617316792153984180899)
    ·
      refine ⟨6821425975188230976271349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547617316792153984180899 6821425975188230976271349)
      ·
        refine ⟨639508685173896654025439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6821425975188230976271349 639508685173896654025439)
        ·
          refine ⟨959263027760844981038159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639508685173896654025439 959263027760844981038159)
          ·
            refine ⟨1438894541641267471557239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959263027760844981038159 1438894541641267471557239)
            ·
              refine ⟨2158341812461901207335859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438894541641267471557239 2158341812461901207335859)
              ·
                refine ⟨3237512718692851811003789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158341812461901207335859 3237512718692851811003789)
                ·
                  refine ⟨1214067269509819429126421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3237512718692851811003789 1214067269509819429126421)
                  ·
                    refine ⟨56909403258272785740301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1214067269509819429126421 56909403258272785740301)
                    ·
                      rfl

theorem cell23_332492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_332492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332492 prefixEnd_332492 := by exact prefixLift 332492
  have htrace : WordTrace (prefixWord ++ tailWord_332492) baseStart_332492 baseEnd_332492 := by
    simpa [prefixWord, tailWord_332492, baseEnd_332492] using wordTrace_append hprefix tailTrace_332492
  have hstable : (prefixWord ++ tailWord_332492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332492).length < 2 ^ (prefixWord ++ tailWord_332492).sum := by decide
  have hdescent : baseEnd_332492 < baseStart_332492 := by decide
  rcases family_descends (prefixWord ++ tailWord_332492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332535 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 4, 7]
def baseStart_332535 : Nat := 118140960795 + 332535 * 2 ^ 59
def prefixEnd_332535 : Nat := 4983230072969 + 3 ^ 40 * 332535 * 2
def baseEnd_332535 : Nat := 56916763147653896327735

theorem tailTrace_332535 : CollatzResearch.WordTrace tailWord_332535 prefixEnd_332535 56916763147653896327735 := by
  unfold tailWord_332535
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128547850289962301631059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085698566859974867754039 12128547850289962301631059)
  ·
    refine ⟨18192821775434943452446589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128547850289962301631059 18192821775434943452446589)
    ·
      refine ⟨6822308165788103794667471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18192821775434943452446589 6822308165788103794667471)
      ·
        refine ⟨10233462248682155692001207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822308165788103794667471 10233462248682155692001207)
        ·
          refine ⟨15350193373023233538001811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233462248682155692001207 15350193373023233538001811)
          ·
            refine ⟨23025290059534850307002717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15350193373023233538001811 23025290059534850307002717)
            ·
              refine ⟨8634483772325568865126019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23025290059534850307002717 8634483772325568865126019)
              ·
                refine ⟨12951725658488353297689029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8634483772325568865126019 12951725658488353297689029)
                ·
                  refine ⟨2428448560966566243316693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12951725658488353297689029 2428448560966566243316693)
                  ·
                    refine ⟨56916763147653896327735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2428448560966566243316693 56916763147653896327735)
                    ·
                      rfl

theorem cell23_332535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_332535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332535 prefixEnd_332535 := by exact prefixLift 332535
  have htrace : WordTrace (prefixWord ++ tailWord_332535) baseStart_332535 baseEnd_332535 := by
    simpa [prefixWord, tailWord_332535, baseEnd_332535] using wordTrace_append hprefix tailTrace_332535
  have hstable : (prefixWord ++ tailWord_332535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332535).length < 2 ^ (prefixWord ++ tailWord_332535).sum := by decide
  have hdescent : baseEnd_332535 < baseStart_332535 := by decide
  rcases family_descends (prefixWord ++ tailWord_332535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_332592 : Nat := 118140960795 + 332592 * 2 ^ 59
def prefixEnd_332592 : Nat := 4983230072969 + 3 ^ 40 * 332592 * 2
def baseEnd_332592 : Nat := 170779557840267965970443

theorem tailTrace_332592 : CollatzResearch.WordTrace tailWord_332592 prefixEnd_332592 170779557840267965970443 := by
  unfold tailWord_332592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065313405541730518228015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8087084540722307357637353 6065313405541730518228015)
  ·
    refine ⟨9097970108312595777342023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6065313405541730518228015 9097970108312595777342023)
    ·
      refine ⟨13646955162468893666013035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097970108312595777342023 13646955162468893666013035)
      ·
        refine ⟨20470432743703340499019553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646955162468893666013035 20470432743703340499019553)
        ·
          refine ⟨15352824557777505374264665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20470432743703340499019553 15352824557777505374264665)
          ·
            refine ⟨11514618418333129030698499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15352824557777505374264665 11514618418333129030698499)
            ·
              refine ⟨17271927627499693546047749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11514618418333129030698499 17271927627499693546047749)
              ·
                refine ⟨3238486430156192539883953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17271927627499693546047749 3238486430156192539883953)
                ·
                  refine ⟨2428864822617144404912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238486430156192539883953 2428864822617144404912965)
                  ·
                    refine ⟨455412154240714575921181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428864822617144404912965 455412154240714575921181)
                    ·
                      refine ⟨170779557840267965970443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 455412154240714575921181 170779557840267965970443)
                      ·
                        rfl

theorem cell23_332592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_332592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332592 prefixEnd_332592 := by exact prefixLift 332592
  have htrace : WordTrace (prefixWord ++ tailWord_332592) baseStart_332592 baseEnd_332592 := by
    simpa [prefixWord, tailWord_332592, baseEnd_332592] using wordTrace_append hprefix tailTrace_332592
  have hstable : (prefixWord ++ tailWord_332592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332592).length < 2 ^ (prefixWord ++ tailWord_332592).sum := by decide
  have hdescent : baseEnd_332592 < baseStart_332592 := by decide
  rcases family_descends (prefixWord ++ tailWord_332592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332652 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_332652 : Nat := 118140960795 + 332652 * 2 ^ 59
def prefixEnd_332652 : Nat := 4983230072969 + 3 ^ 40 * 332652 * 2
def baseEnd_332652 : Nat := 170810366679537731220167

theorem tailTrace_332652 : CollatzResearch.WordTrace tailWord_332652 prefixEnd_332652 170810366679537731220167 := by
  unfold tailWord_332652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066407595433045641820105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8088543460577394189093473 6066407595433045641820105)
  ·
    refine ⟨4549805696574784231365079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066407595433045641820105 4549805696574784231365079)
    ·
      refine ⟨6824708544862176347047619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549805696574784231365079 6824708544862176347047619)
      ·
        refine ⟨10237062817293264520571429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824708544862176347047619 10237062817293264520571429)
        ·
          refine ⟨1919449278242487097607143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10237062817293264520571429 1919449278242487097607143)
          ·
            refine ⟨2879173917363730646410715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919449278242487097607143 2879173917363730646410715)
            ·
              refine ⟨4318760876045595969616073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879173917363730646410715 4318760876045595969616073)
              ·
                refine ⟨3239070657034196977212055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318760876045595969616073 3239070657034196977212055)
                ·
                  refine ⟨4858605985551295465818083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3239070657034196977212055 4858605985551295465818083)
                  ·
                    refine ⟨7287908978326943198727125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4858605985551295465818083 7287908978326943198727125)
                    ·
                      refine ⟨170810366679537731220167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7287908978326943198727125 170810366679537731220167)
                      ·
                        rfl

theorem cell23_332652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_332652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332652 prefixEnd_332652 := by exact prefixLift 332652
  have htrace : WordTrace (prefixWord ++ tailWord_332652) baseStart_332652 baseEnd_332652 := by
    simpa [prefixWord, tailWord_332652, baseEnd_332652] using wordTrace_append hprefix tailTrace_332652
  have hstable : (prefixWord ++ tailWord_332652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332652).length < 2 ^ (prefixWord ++ tailWord_332652).sum := by decide
  have hdescent : baseEnd_332652 < baseStart_332652 := by decide
  rcases family_descends (prefixWord ++ tailWord_332652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332674 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_332674 : Nat := 118140960795 + 332674 * 2 ^ 59
def prefixEnd_332674 : Nat := 4983230072969 + 3 ^ 40 * 332674 * 2
def baseEnd_332674 : Nat := 170821663253936645145067

theorem tailTrace_332674 : CollatzResearch.WordTrace tailWord_332674 prefixEnd_332674 170821663253936645145067 := by
  unfold tailWord_332674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033404399196597260235269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8089078397857592693960717 3033404399196597260235269)
  ·
    refine ⟨568763324849361986294113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3033404399196597260235269 568763324849361986294113)
    ·
      refine ⟨426572493637021489720585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568763324849361986294113 426572493637021489720585)
      ·
        refine ⟨319929370227766117290439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426572493637021489720585 319929370227766117290439)
        ·
          refine ⟨479894055341649175935659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319929370227766117290439 479894055341649175935659)
          ·
            refine ⟨719841083012473763903489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479894055341649175935659 719841083012473763903489)
            ·
              refine ⟨539880812259355322927617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719841083012473763903489 539880812259355322927617)
              ·
                refine ⟨404910609194516492195713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539880812259355322927617 404910609194516492195713)
                ·
                  refine ⟨303682956895887369146785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404910609194516492195713 303682956895887369146785)
                  ·
                    refine ⟨227762217671915526860089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303682956895887369146785 227762217671915526860089)
                    ·
                      refine ⟨170821663253936645145067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227762217671915526860089 170821663253936645145067)
                      ·
                        rfl

theorem cell23_332674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_332674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332674 prefixEnd_332674 := by exact prefixLift 332674
  have htrace : WordTrace (prefixWord ++ tailWord_332674) baseStart_332674 baseEnd_332674 := by
    simpa [prefixWord, tailWord_332674, baseEnd_332674] using wordTrace_append hprefix tailTrace_332674
  have hstable : (prefixWord ++ tailWord_332674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332674).length < 2 ^ (prefixWord ++ tailWord_332674).sum := by decide
  have hdescent : baseEnd_332674 < baseStart_332674 := by decide
  rcases family_descends (prefixWord ++ tailWord_332674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332689 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_332689 : Nat := 118140960795 + 332689 * 2 ^ 59
def prefixEnd_332689 : Nat := 4983230072969 + 3 ^ 40 * 332689 * 2
def baseEnd_332689 : Nat := 56943121821251362152499

theorem tailTrace_332689 : CollatzResearch.WordTrace tailWord_332689 prefixEnd_332689 56943121821251362152499 := by
  unfold tailWord_332689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134164691732046602737121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089443127821364401824747 12134164691732046602737121)
  ·
    refine ⟨9100623518799034952052841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12134164691732046602737121 9100623518799034952052841)
    ·
      refine ⟨6825467639099276214039631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9100623518799034952052841 6825467639099276214039631)
      ·
        refine ⟨10238201458648914321059447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825467639099276214039631 10238201458648914321059447)
        ·
          refine ⟨15357302187973371481589171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10238201458648914321059447 15357302187973371481589171)
          ·
            refine ⟨23035953281960057222383757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15357302187973371481589171 23035953281960057222383757)
            ·
              refine ⟨8638482480735021458393909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23035953281960057222383757 8638482480735021458393909)
              ·
                refine ⟨809857732568908261724429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8638482480735021458393909 809857732568908261724429)
                ·
                  refine ⟨303696649713340598146661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809857732568908261724429 303696649713340598146661)
                  ·
                    refine ⟨56943121821251362152499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303696649713340598146661 56943121821251362152499)
                    ·
                      rfl

theorem cell23_332689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_332689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332689 prefixEnd_332689 := by exact prefixLift 332689
  have htrace : WordTrace (prefixWord ++ tailWord_332689) baseStart_332689 baseEnd_332689 := by
    simpa [prefixWord, tailWord_332689, baseEnd_332689] using wordTrace_append hprefix tailTrace_332689
  have hstable : (prefixWord ++ tailWord_332689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332689).length < 2 ^ (prefixWord ++ tailWord_332689).sum := by decide
  have hdescent : baseEnd_332689 < baseStart_332689 := by decide
  rcases family_descends (prefixWord ++ tailWord_332689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332706 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_332706 : Nat := 118140960795 + 332706 * 2 ^ 59
def prefixEnd_332706 : Nat := 4983230072969 + 3 ^ 40 * 332706 * 2
def baseEnd_332706 : Nat := 56946031544960173314973

theorem tailTrace_332706 : CollatzResearch.WordTrace tailWord_332706 prefixEnd_332706 56946031544960173314973 := by
  unfold tailWord_332706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033696183167614626526493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8089856488446972337403981 3033696183167614626526493)
  ·
    refine ⟨1137636068687855484947435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3033696183167614626526493 1137636068687855484947435)
    ·
      refine ⟨1706454103031783227421153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137636068687855484947435 1706454103031783227421153)
      ·
        refine ⟨1279840577273837420565865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706454103031783227421153 1279840577273837420565865)
        ·
          refine ⟨959880432955378065424399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279840577273837420565865 959880432955378065424399)
          ·
            refine ⟨1439820649433067098136599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959880432955378065424399 1439820649433067098136599)
            ·
              refine ⟨2159730974149600647204899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439820649433067098136599 2159730974149600647204899)
              ·
                refine ⟨3239596461224400970807349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159730974149600647204899 3239596461224400970807349)
                ·
                  refine ⟨303712168239787591013189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3239596461224400970807349 303712168239787591013189)
                  ·
                    refine ⟨56946031544960173314973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303712168239787591013189 56946031544960173314973)
                    ·
                      rfl

theorem cell23_332706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_332706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332706 prefixEnd_332706 := by exact prefixLift 332706
  have htrace : WordTrace (prefixWord ++ tailWord_332706) baseStart_332706 baseEnd_332706 := by
    simpa [prefixWord, tailWord_332706, baseEnd_332706] using wordTrace_append hprefix tailTrace_332706
  have hstable : (prefixWord ++ tailWord_332706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332706).length < 2 ^ (prefixWord ++ tailWord_332706).sum := by decide
  have hdescent : baseEnd_332706 < baseStart_332706 := by decide
  rcases family_descends (prefixWord ++ tailWord_332706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332736 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 6]
def baseStart_332736 : Nat := 118140960795 + 332736 * 2 ^ 59
def prefixEnd_332736 : Nat := 4983230072969 + 3 ^ 40 * 332736 * 2
def baseEnd_332736 : Nat := 18983722117168378063309

theorem tailTrace_332736 : CollatzResearch.WordTrace tailWord_332736 prefixEnd_332736 18983722117168378063309 := by
  unfold tailWord_332736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6067939461280886814849031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8090585948374515753132041 6067939461280886814849031)
  ·
    refine ⟨9101909191921330222273547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6067939461280886814849031 9101909191921330222273547)
    ·
      refine ⟨13652863787881995333410321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9101909191921330222273547 13652863787881995333410321)
      ·
        refine ⟨10239647840911496500057741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13652863787881995333410321 10239647840911496500057741)
        ·
          refine ⟨3839867940341811187521653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10239647840911496500057741 3839867940341811187521653)
          ·
            refine ⟨359987619407044798830155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3839867940341811187521653 359987619407044798830155)
            ·
              refine ⟨539981429110567198245233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359987619407044798830155 539981429110567198245233)
              ·
                refine ⟨404986071832925398683925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539981429110567198245233 404986071832925398683925)
                ·
                  refine ⟨18983722117168378063309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 404986071832925398683925 18983722117168378063309)
                  ·
                    rfl

theorem cell23_332736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_332736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332736 prefixEnd_332736 := by exact prefixLift 332736
  have htrace : WordTrace (prefixWord ++ tailWord_332736) baseStart_332736 baseEnd_332736 := by
    simpa [prefixWord, tailWord_332736, baseEnd_332736] using wordTrace_append hprefix tailTrace_332736
  have hstable : (prefixWord ++ tailWord_332736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332736).length < 2 ^ (prefixWord ++ tailWord_332736).sum := by decide
  have hdescent : baseEnd_332736 < baseStart_332736 := by decide
  rcases family_descends (prefixWord ++ tailWord_332736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332740 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_332740 : Nat := 118140960795 + 332740 * 2 ^ 59
def prefixEnd_332740 : Nat := 4983230072969 + 3 ^ 40 * 332740 * 2
def baseEnd_332740 : Nat := 56951850992377795639921

theorem tailTrace_332740 : CollatzResearch.WordTrace tailWord_332740 prefixEnd_332740 56951850992377795639921 := by
  unfold tailWord_332740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068012407273641156421837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8090683209698188208562449 6068012407273641156421837)
  ·
    refine ⟨2275504652727615433658189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6068012407273641156421837 2275504652727615433658189)
    ·
      refine ⟨853314244772855787621821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2275504652727615433658189 853314244772855787621821)
      ·
        refine ⟨319992841789820920358183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 853314244772855787621821 319992841789820920358183)
        ·
          refine ⟨479989262684731380537275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319992841789820920358183 479989262684731380537275)
          ·
            refine ⟨719983894027097070805913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479989262684731380537275 719983894027097070805913)
            ·
              refine ⟨539987920520322803104435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719983894027097070805913 539987920520322803104435)
              ·
                refine ⟨809981880780484204656653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539987920520322803104435 809981880780484204656653)
                ·
                  refine ⟨303743205292681576746245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809981880780484204656653 303743205292681576746245)
                  ·
                    refine ⟨56951850992377795639921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303743205292681576746245 56951850992377795639921)
                    ·
                      rfl

theorem cell23_332740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_332740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332740 prefixEnd_332740 := by exact prefixLift 332740
  have htrace : WordTrace (prefixWord ++ tailWord_332740) baseStart_332740 baseEnd_332740 := by
    simpa [prefixWord, tailWord_332740, baseEnd_332740] using wordTrace_append hprefix tailTrace_332740
  have hstable : (prefixWord ++ tailWord_332740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332740).length < 2 ^ (prefixWord ++ tailWord_332740).sum := by decide
  have hdescent : baseEnd_332740 < baseStart_332740 := by decide
  rcases family_descends (prefixWord ++ tailWord_332740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332790 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_332790 : Nat := 118140960795 + 332790 * 2 ^ 59
def prefixEnd_332790 : Nat := 4983230072969 + 3 ^ 40 * 332790 * 2
def baseEnd_332790 : Nat := 170881227009858191294533

theorem tailTrace_332790 : CollatzResearch.WordTrace tailWord_332790 prefixEnd_332790 170881227009858191294533 := by
  unfold tailWord_332790
  simp only [CollatzResearch.WordTrace]
  refine ⟨758615529022883803260239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8091898976244093901442549 758615529022883803260239)
  ·
    refine ⟨1137923293534325704890359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758615529022883803260239 1137923293534325704890359)
    ·
      refine ⟨1706884940301488557335539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137923293534325704890359 1706884940301488557335539)
      ·
        refine ⟨2560327410452232836003309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706884940301488557335539 2560327410452232836003309)
        ·
          refine ⟨960122778919587313501241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2560327410452232836003309 960122778919587313501241)
          ·
            refine ⟨720092084189690485125931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960122778919587313501241 720092084189690485125931)
            ·
              refine ⟨1080138126284535727688897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720092084189690485125931 1080138126284535727688897)
              ·
                refine ⟨810103594713401795766673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080138126284535727688897 810103594713401795766673)
                ·
                  refine ⟨607577696035051346825005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810103594713401795766673 607577696035051346825005)
                  ·
                    refine ⟨227841636013144255059377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607577696035051346825005 227841636013144255059377)
                    ·
                      refine ⟨170881227009858191294533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227841636013144255059377 170881227009858191294533)
                      ·
                        rfl

theorem cell23_332790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_332790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332790 prefixEnd_332790 := by exact prefixLift 332790
  have htrace : WordTrace (prefixWord ++ tailWord_332790) baseStart_332790 baseEnd_332790 := by
    simpa [prefixWord, tailWord_332790, baseEnd_332790] using wordTrace_append hprefix tailTrace_332790
  have hstable : (prefixWord ++ tailWord_332790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332790).length < 2 ^ (prefixWord ++ tailWord_332790).sum := by decide
  have hdescent : baseEnd_332790 < baseStart_332790 := by decide
  rcases family_descends (prefixWord ++ tailWord_332790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332796 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_332796 : Nat := 118140960795 + 332796 * 2 ^ 59
def prefixEnd_332796 : Nat := 4983230072969 + 3 ^ 40 * 332796 * 2
def baseEnd_332796 : Nat := 56961435964595055939835

theorem tailTrace_332796 : CollatzResearch.WordTrace tailWord_332796 prefixEnd_332796 56961435964595055939835 := by
  unfold tailWord_332796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069033651172201938441121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8092044868229602584588161 6069033651172201938441121)
  ·
    refine ⟨4551775238379151453830841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6069033651172201938441121 4551775238379151453830841)
    ·
      refine ⟨3413831428784363590373131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551775238379151453830841 3413831428784363590373131)
      ·
        refine ⟨5120747143176545385559697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413831428784363590373131 5120747143176545385559697)
        ·
          refine ⟨3840560357382409039169773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120747143176545385559697 3840560357382409039169773)
          ·
            refine ⟨1440210134018403389688665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3840560357382409039169773 1440210134018403389688665)
            ·
              refine ⟨1080157600513802542266499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440210134018403389688665 1080157600513802542266499)
              ·
                refine ⟨1620236400770703813399749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080157600513802542266499 1620236400770703813399749)
                ·
                  refine ⟨303794325144506965012453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620236400770703813399749 303794325144506965012453)
                  ·
                    refine ⟨56961435964595055939835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303794325144506965012453 56961435964595055939835)
                    ·
                      rfl

theorem cell23_332796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_332796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332796 prefixEnd_332796 := by exact prefixLift 332796
  have htrace : WordTrace (prefixWord ++ tailWord_332796) baseStart_332796 baseEnd_332796 := by
    simpa [prefixWord, tailWord_332796, baseEnd_332796] using wordTrace_append hprefix tailTrace_332796
  have hstable : (prefixWord ++ tailWord_332796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332796).length < 2 ^ (prefixWord ++ tailWord_332796).sum := by decide
  have hdescent : baseEnd_332796 < baseStart_332796 := by decide
  rcases family_descends (prefixWord ++ tailWord_332796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332823 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_332823 : Nat := 118140960795 + 332823 * 2 ^ 59
def prefixEnd_332823 : Nat := 4983230072969 + 3 ^ 40 * 332823 * 2
def baseEnd_332823 : Nat := 170898171871456562181881

theorem tailTrace_332823 : CollatzResearch.WordTrace tailWord_332823 prefixEnd_332823 170898171871456562181881 := by
  unfold tailWord_332823
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139052073246587488115123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8092701382164391658743415 12139052073246587488115123)
  ·
    refine ⟨18208578109869881232172685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12139052073246587488115123 18208578109869881232172685)
    ·
      refine ⟨6828216791201205462064757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18208578109869881232172685 6828216791201205462064757)
      ·
        refine ⟨640145324175113012068571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6828216791201205462064757 640145324175113012068571)
        ·
          refine ⟨960217986262669518102857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640145324175113012068571 960217986262669518102857)
          ·
            refine ⟨720163489697002138577143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960217986262669518102857 720163489697002138577143)
            ·
              refine ⟨1080245234545503207865715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720163489697002138577143 1080245234545503207865715)
              ·
                refine ⟨1620367851818254811798573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080245234545503207865715 1620367851818254811798573)
                ·
                  refine ⟨607637944431845554424465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1620367851818254811798573 607637944431845554424465)
                  ·
                    refine ⟨455728458323884165818349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 607637944431845554424465 455728458323884165818349)
                    ·
                      refine ⟨170898171871456562181881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 455728458323884165818349 170898171871456562181881)
                      ·
                        rfl

theorem cell23_332823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_332823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332823 prefixEnd_332823 := by exact prefixLift 332823
  have htrace : WordTrace (prefixWord ++ tailWord_332823) baseStart_332823 baseEnd_332823 := by
    simpa [prefixWord, tailWord_332823, baseEnd_332823] using wordTrace_append hprefix tailTrace_332823
  have hstable : (prefixWord ++ tailWord_332823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332823).length < 2 ^ (prefixWord ++ tailWord_332823).sum := by decide
  have hdescent : baseEnd_332823 < baseStart_332823 := by decide
  rcases family_descends (prefixWord ++ tailWord_332823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332854 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_332854 : Nat := 118140960795 + 332854 * 2 ^ 59
def prefixEnd_332854 : Nat := 4983230072969 + 3 ^ 40 * 332854 * 2
def baseEnd_332854 : Nat := 170914089771745940894239

theorem tailTrace_332854 : CollatzResearch.WordTrace tailWord_332854 prefixEnd_332854 170914089771745940894239 := by
  unfold tailWord_332854
  simp only [CollatzResearch.WordTrace]
  refine ⟨758761421008392486405851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8093455157422853188329077 758761421008392486405851)
  ·
    refine ⟨1138142131512588729608777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758761421008392486405851 1138142131512588729608777)
    ·
      refine ⟨853606598634441547206583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1138142131512588729608777 853606598634441547206583)
      ·
        refine ⟨1280409897951662320809875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853606598634441547206583 1280409897951662320809875)
        ·
          refine ⟨1920614846927493481214813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280409897951662320809875 1920614846927493481214813)
          ·
            refine ⟨720230567597810055455555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1920614846927493481214813 720230567597810055455555)
            ·
              refine ⟨1080345851396715083183333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720230567597810055455555 1080345851396715083183333)
              ·
                refine ⟨202564847136884078096875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1080345851396715083183333 202564847136884078096875)
                ·
                  refine ⟨303847270705326117145313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202564847136884078096875 303847270705326117145313)
                  ·
                    refine ⟨227885453028994587858985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303847270705326117145313 227885453028994587858985)
                    ·
                      refine ⟨170914089771745940894239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227885453028994587858985 170914089771745940894239)
                      ·
                        rfl

theorem cell23_332854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_332854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332854 prefixEnd_332854 := by exact prefixLift 332854
  have htrace : WordTrace (prefixWord ++ tailWord_332854) baseStart_332854 baseEnd_332854 := by
    simpa [prefixWord, tailWord_332854, baseEnd_332854] using wordTrace_append hprefix tailTrace_332854
  have hstable : (prefixWord ++ tailWord_332854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332854).length < 2 ^ (prefixWord ++ tailWord_332854).sum := by decide
  have hdescent : baseEnd_332854 < baseStart_332854 := by decide
  rcases family_descends (prefixWord ++ tailWord_332854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332869 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_332869 : Nat := 118140960795 + 332869 * 2 ^ 59
def prefixEnd_332869 : Nat := 4983230072969 + 3 ^ 40 * 332869 * 2
def baseEnd_332869 : Nat := 56973930660521127402223

theorem tailTrace_332869 : CollatzResearch.WordTrace tailWord_332869 prefixEnd_332869 56973930660521127402223 := by
  unfold tailWord_332869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12140729831079937344289661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8093819887386624896193107 12140729831079937344289661)
  ·
    refine ⟨4552773686654976504108623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12140729831079937344289661 4552773686654976504108623)
    ·
      refine ⟨6829160529982464756162935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552773686654976504108623 6829160529982464756162935)
      ·
        refine ⟨10243740794973697134244403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6829160529982464756162935 10243740794973697134244403)
        ·
          refine ⟨15365611192460545701366605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243740794973697134244403 15365611192460545701366605)
          ·
            refine ⟨5762104197172704638012477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15365611192460545701366605 5762104197172704638012477)
            ·
              refine ⟨2160789073939764239254679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5762104197172704638012477 2160789073939764239254679)
              ·
                refine ⟨3241183610909646358882019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160789073939764239254679 3241183610909646358882019)
                ·
                  refine ⟨4861775416364469538323029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241183610909646358882019 4861775416364469538323029)
                  ·
                    refine ⟨56973930660521127402223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4861775416364469538323029 56973930660521127402223)
                    ·
                      rfl

theorem cell23_332869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_332869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332869 prefixEnd_332869 := by exact prefixLift 332869
  have htrace : WordTrace (prefixWord ++ tailWord_332869) baseStart_332869 baseEnd_332869 := by
    simpa [prefixWord, tailWord_332869, baseEnd_332869] using wordTrace_append hprefix tailTrace_332869
  have hstable : (prefixWord ++ tailWord_332869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332869).length < 2 ^ (prefixWord ++ tailWord_332869).sum := by decide
  have hdescent : baseEnd_332869 < baseStart_332869 := by decide
  rcases family_descends (prefixWord ++ tailWord_332869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332870 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_332870 : Nat := 118140960795 + 332870 * 2 ^ 59
def prefixEnd_332870 : Nat := 4983230072969 + 3 ^ 40 * 332870 * 2
def baseEnd_332870 : Nat := 170922305462217878294165

theorem tailTrace_332870 : CollatzResearch.WordTrace tailWord_332870 prefixEnd_332870 170922305462217878294165 := by
  unfold tailWord_332870
  simp only [CollatzResearch.WordTrace]
  refine ⟨379398947002384828596127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8093844202717543010050709 379398947002384828596127)
  ·
    refine ⟨569098420503577242894191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 379398947002384828596127 569098420503577242894191)
    ·
      refine ⟨853647630755365864341287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569098420503577242894191 853647630755365864341287)
      ·
        refine ⟨1280471446133048796511931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853647630755365864341287 1280471446133048796511931)
        ·
          refine ⟨1920707169199573194767897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280471446133048796511931 1920707169199573194767897)
          ·
            refine ⟨1440530376899679896075923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920707169199573194767897 1440530376899679896075923)
            ·
              refine ⟨2160795565349519844113885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440530376899679896075923 2160795565349519844113885)
              ·
                refine ⟨810298337006069941542707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2160795565349519844113885 810298337006069941542707)
                ·
                  refine ⟨1215447505509104912314061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810298337006069941542707 1215447505509104912314061)
                  ·
                    refine ⟨455792814565914342117773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215447505509104912314061 455792814565914342117773)
                    ·
                      refine ⟨170922305462217878294165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 455792814565914342117773 170922305462217878294165)
                      ·
                        rfl

theorem cell23_332870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_332870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332870 prefixEnd_332870 := by exact prefixLift 332870
  have htrace : WordTrace (prefixWord ++ tailWord_332870) baseStart_332870 baseEnd_332870 := by
    simpa [prefixWord, tailWord_332870, baseEnd_332870] using wordTrace_append hprefix tailTrace_332870
  have hstable : (prefixWord ++ tailWord_332870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332870).length < 2 ^ (prefixWord ++ tailWord_332870).sum := by decide
  have hdescent : baseEnd_332870 < baseStart_332870 := by decide
  rcases family_descends (prefixWord ++ tailWord_332870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332899 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 11]
def baseStart_332899 : Nat := 118140960795 + 332899 * 2 ^ 59
def prefixEnd_332899 : Nat := 4983230072969 + 3 ^ 40 * 332899 * 2
def baseEnd_332899 : Nat := 18993021822355362759059

theorem tailTrace_332899 : CollatzResearch.WordTrace tailWord_332899 prefixEnd_332899 18993021822355362759059 := by
  unfold tailWord_332899
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141824020971252467881751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094549347314168311921167 12141824020971252467881751)
  ·
    refine ⟨18212736031456878701822627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12141824020971252467881751 18212736031456878701822627)
    ·
      refine ⟨27319104047185318052733941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18212736031456878701822627 27319104047185318052733941)
      ·
        refine ⟨2561166004423623567443807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27319104047185318052733941 2561166004423623567443807)
        ·
          refine ⟨3841749006635435351165711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561166004423623567443807 3841749006635435351165711)
          ·
            refine ⟨5762623509953153026748567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841749006635435351165711 5762623509953153026748567)
            ·
              refine ⟨8643935264929729540122851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762623509953153026748567 8643935264929729540122851)
              ·
                refine ⟨12965902897394594310184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8643935264929729540122851 12965902897394594310184277)
                ·
                  refine ⟨18993021822355362759059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 12965902897394594310184277 18993021822355362759059)
                  ·
                    rfl

theorem cell23_332899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 11].length) (baseStart_332899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332899 prefixEnd_332899 := by exact prefixLift 332899
  have htrace : WordTrace (prefixWord ++ tailWord_332899) baseStart_332899 baseEnd_332899 := by
    simpa [prefixWord, tailWord_332899, baseEnd_332899] using wordTrace_append hprefix tailTrace_332899
  have hstable : (prefixWord ++ tailWord_332899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332899).length < 2 ^ (prefixWord ++ tailWord_332899).sum := by decide
  have hdescent : baseEnd_332899 < baseStart_332899 := by decide
  rcases family_descends (prefixWord ++ tailWord_332899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332904 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_332904 : Nat := 118140960795 + 332904 * 2 ^ 59
def prefixEnd_332904 : Nat := 4983230072969 + 3 ^ 40 * 332904 * 2
def baseEnd_332904 : Nat := 170939763804470745269009

theorem tailTrace_332904 : CollatzResearch.WordTrace tailWord_332904 prefixEnd_332904 170939763804470745269009 := by
  unfold tailWord_332904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071003192976569160906883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8094670923968758881209177 6071003192976569160906883)
  ·
    refine ⟨9106504789464853741360325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071003192976569160906883 9106504789464853741360325)
    ·
      refine ⟨1707469648024660076505061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9106504789464853741360325 1707469648024660076505061)
      ·
        refine ⟨320150559004623764344699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1707469648024660076505061 320150559004623764344699)
        ·
          refine ⟨480225838506935646517049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320150559004623764344699 480225838506935646517049)
          ·
            refine ⟨360169378880201734887787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480225838506935646517049 360169378880201734887787)
            ·
              refine ⟨540254068320302602331681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360169378880201734887787 540254068320302602331681)
              ·
                refine ⟨405190551240226951748761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540254068320302602331681 405190551240226951748761)
                ·
                  refine ⟨303892913430170213811571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405190551240226951748761 303892913430170213811571)
                  ·
                    refine ⟨455839370145255320717357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 303892913430170213811571 455839370145255320717357)
                    ·
                      refine ⟨170939763804470745269009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 455839370145255320717357 170939763804470745269009)
                      ·
                        rfl

theorem cell23_332904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_332904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332904 prefixEnd_332904 := by exact prefixLift 332904
  have htrace : WordTrace (prefixWord ++ tailWord_332904) baseStart_332904 baseEnd_332904 := by
    simpa [prefixWord, tailWord_332904, baseEnd_332904] using wordTrace_append hprefix tailTrace_332904
  have hstable : (prefixWord ++ tailWord_332904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332904).length < 2 ^ (prefixWord ++ tailWord_332904).sum := by decide
  have hdescent : baseEnd_332904 < baseStart_332904 := by decide
  rcases family_descends (prefixWord ++ tailWord_332904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332967 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 5]
def baseStart_332967 : Nat := 118140960795 + 332967 * 2 ^ 59
def prefixEnd_332967 : Nat := 4983230072969 + 3 ^ 40 * 332967 * 2
def baseEnd_332967 : Nat := 18996901453967110975691

theorem tailTrace_332967 : CollatzResearch.WordTrace tailWord_332967 prefixEnd_332967 18996901453967110975691 := by
  unfold tailWord_332967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144304184724900081357155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8096202789816600054238103 12144304184724900081357155)
  ·
    refine ⟨18216456277087350122035733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144304184724900081357155 18216456277087350122035733)
    ·
      refine ⟨853896387988469536970425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18216456277087350122035733 853896387988469536970425)
      ·
        refine ⟨640422290991352152727819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853896387988469536970425 640422290991352152727819)
        ·
          refine ⟨960633436487028229091729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640422290991352152727819 960633436487028229091729)
          ·
            refine ⟨720475077365271171818797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960633436487028229091729 720475077365271171818797)
            ·
              refine ⟨270178154011976689432049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 720475077365271171818797 270178154011976689432049)
              ·
                refine ⟨202633615508982517074037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270178154011976689432049 202633615508982517074037)
                ·
                  refine ⟨18996901453967110975691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202633615508982517074037 18996901453967110975691)
                  ·
                    rfl

theorem cell23_332967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 5].length) (baseStart_332967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332967 prefixEnd_332967 := by exact prefixLift 332967
  have htrace : WordTrace (prefixWord ++ tailWord_332967) baseStart_332967 baseEnd_332967 := by
    simpa [prefixWord, tailWord_332967, baseEnd_332967] using wordTrace_append hprefix tailTrace_332967
  have hstable : (prefixWord ++ tailWord_332967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332967).length < 2 ^ (prefixWord ++ tailWord_332967).sum := by decide
  have hdescent : baseEnd_332967 < baseStart_332967 := by decide
  rcases family_descends (prefixWord ++ tailWord_332967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332983 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_332983 : Nat := 118140960795 + 332983 * 2 ^ 59
def prefixEnd_332983 : Nat := 4983230072969 + 3 ^ 40 * 332983 * 2
def baseEnd_332983 : Nat := 170980328776175936181145

theorem tailTrace_332983 : CollatzResearch.WordTrace tailWord_332983 prefixEnd_332983 170980328776175936181145 := by
  unfold tailWord_332983
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144887752666934813939603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8096591835111289875959735 12144887752666934813939603)
  ·
    refine ⟨18217331629000402220909405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144887752666934813939603 18217331629000402220909405)
    ·
      refine ⟨6831499360875150832841027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18217331629000402220909405 6831499360875150832841027)
      ·
        refine ⟨10247249041312726249261541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831499360875150832841027 10247249041312726249261541)
        ·
          refine ⟨1921359195246136171736539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10247249041312726249261541 1921359195246136171736539)
          ·
            refine ⟨2882038792869204257604809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921359195246136171736539 2882038792869204257604809)
            ·
              refine ⟨2161529094651903193203607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882038792869204257604809 2161529094651903193203607)
              ·
                refine ⟨3242293641977854789805411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161529094651903193203607 3242293641977854789805411)
                ·
                  refine ⟨4863440462966782184708117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242293641977854789805411 4863440462966782184708117)
                  ·
                    refine ⟨227973771701567914908193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4863440462966782184708117 227973771701567914908193)
                    ·
                      refine ⟨170980328776175936181145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 227973771701567914908193 170980328776175936181145)
                      ·
                        rfl

theorem cell23_332983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_332983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_332983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_332983 prefixEnd_332983 := by exact prefixLift 332983
  have htrace : WordTrace (prefixWord ++ tailWord_332983) baseStart_332983 baseEnd_332983 := by
    simpa [prefixWord, tailWord_332983, baseEnd_332983] using wordTrace_append hprefix tailTrace_332983
  have hstable : (prefixWord ++ tailWord_332983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332983).length < 2 ^ (prefixWord ++ tailWord_332983).sum := by decide
  have hdescent : baseEnd_332983 < baseStart_332983 := by decide
  rcases family_descends (prefixWord ++ tailWord_332983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333050 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_333050 : Nat := 118140960795 + 333050 * 2 ^ 59
def prefixEnd_333050 : Nat := 4983230072969 + 3 ^ 40 * 333050 * 2
def baseEnd_333050 : Nat := 171014731980027174043337

theorem tailTrace_333050 : CollatzResearch.WordTrace tailWord_333050 prefixEnd_333050 171014731980027174043337 := by
  unfold tailWord_333050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036832860856051314157151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8098220962282803504419069 3036832860856051314157151)
  ·
    refine ⟨4555249291284076971235727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036832860856051314157151 4555249291284076971235727)
    ·
      refine ⟨6832873936926115456853591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555249291284076971235727 6832873936926115456853591)
      ·
        refine ⟨10249310905389173185280387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832873936926115456853591 10249310905389173185280387)
        ·
          refine ⟨15373966358083759777920581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249310905389173185280387 15373966358083759777920581)
          ·
            refine ⟨2882618692140704958360109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15373966358083759777920581 2882618692140704958360109)
            ·
              refine ⟨1080982009552764359385041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2882618692140704958360109 1080982009552764359385041)
              ·
                refine ⟨810736507164573269538781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080982009552764359385041 810736507164573269538781)
                ·
                  refine ⟨304026190186714976077043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810736507164573269538781 304026190186714976077043)
                  ·
                    refine ⟨456039285280072464115565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304026190186714976077043 456039285280072464115565)
                    ·
                      refine ⟨171014731980027174043337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456039285280072464115565 171014731980027174043337)
                      ·
                        rfl

theorem cell23_333050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_333050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333050 prefixEnd_333050 := by exact prefixLift 333050
  have htrace : WordTrace (prefixWord ++ tailWord_333050) baseStart_333050 baseEnd_333050 := by
    simpa [prefixWord, tailWord_333050, baseEnd_333050] using wordTrace_append hprefix tailTrace_333050
  have hstable : (prefixWord ++ tailWord_333050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333050).length < 2 ^ (prefixWord ++ tailWord_333050).sum := by decide
  have hdescent : baseEnd_333050 < baseStart_333050 := by decide
  rcases family_descends (prefixWord ++ tailWord_333050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333067 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 1, 1, 3]
def baseStart_333067 : Nat := 118140960795 + 333067 * 2 ^ 59
def prefixEnd_333067 : Nat := 4983230072969 + 3 ^ 40 * 333067 * 2
def baseEnd_333067 : Nat := 171023461151153607530759

theorem tailTrace_333067 : CollatzResearch.WordTrace tailWord_333067 prefixEnd_333067 171023461151153607530759 := by
  unfold tailWord_333067
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147951484362617159997455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8098634322908411439998303 12147951484362617159997455)
  ·
    refine ⟨18221927226543925739996183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12147951484362617159997455 18221927226543925739996183)
    ·
      refine ⟨27332890839815888609994275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18221927226543925739996183 27332890839815888609994275)
      ·
        refine ⟨40999336259723832914991413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27332890839815888609994275 40999336259723832914991413)
        ·
          refine ⟨3843687774349109335780445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40999336259723832914991413 3843687774349109335780445)
          ·
            refine ⟨1441382915380916000917667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3843687774349109335780445 1441382915380916000917667)
            ·
              refine ⟨2162074373071374001376501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441382915380916000917667 2162074373071374001376501)
              ·
                refine ⟨202694472475441312629047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2162074373071374001376501 202694472475441312629047)
                ·
                  refine ⟨304041708713161968943571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202694472475441312629047 304041708713161968943571)
                  ·
                    refine ⟨456062563069742953415357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304041708713161968943571 456062563069742953415357)
                    ·
                      refine ⟨171023461151153607530759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456062563069742953415357 171023461151153607530759)
                      ·
                        rfl

theorem cell23_333067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 1, 3].length) (baseStart_333067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333067 prefixEnd_333067 := by exact prefixLift 333067
  have htrace : WordTrace (prefixWord ++ tailWord_333067) baseStart_333067 baseEnd_333067 := by
    simpa [prefixWord, tailWord_333067, baseEnd_333067] using wordTrace_append hprefix tailTrace_333067
  have hstable : (prefixWord ++ tailWord_333067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333067).length < 2 ^ (prefixWord ++ tailWord_333067).sum := by decide
  have hdescent : baseEnd_333067 < baseStart_333067 := by decide
  rcases family_descends (prefixWord ++ tailWord_333067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333070 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_333070 : Nat := 118140960795 + 333070 * 2 ^ 59
def prefixEnd_333070 : Nat := 4983230072969 + 3 ^ 40 * 333070 * 2
def baseEnd_333070 : Nat := 57008333864372365264415

theorem tailTrace_333070 : CollatzResearch.WordTrace tailWord_333070 prefixEnd_333070 57008333864372365264415 := by
  unfold tailWord_333070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518507612918968584044583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8098707268901165781571109 1518507612918968584044583)
  ·
    refine ⟨2277761419378452876066875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518507612918968584044583 2277761419378452876066875)
    ·
      refine ⟨3416642129067679314100313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277761419378452876066875 3416642129067679314100313)
      ·
        refine ⟨2562481596800759485575235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3416642129067679314100313 2562481596800759485575235)
        ·
          refine ⟨3843722395201139228362853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562481596800759485575235 3843722395201139228362853)
          ·
            refine ⟨720697949100213605318035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3843722395201139228362853 720697949100213605318035)
            ·
              refine ⟨1081046923650320407977053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720697949100213605318035 1081046923650320407977053)
              ·
                refine ⟨405392596368870152991395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081046923650320407977053 405392596368870152991395)
                ·
                  refine ⟨608088894553305229487093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405392596368870152991395 608088894553305229487093)
                  ·
                    refine ⟨57008333864372365264415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 608088894553305229487093 57008333864372365264415)
                    ·
                      rfl

theorem cell23_333070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_333070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333070 prefixEnd_333070 := by exact prefixLift 333070
  have htrace : WordTrace (prefixWord ++ tailWord_333070) baseStart_333070 baseEnd_333070 := by
    simpa [prefixWord, tailWord_333070, baseEnd_333070] using wordTrace_append hprefix tailTrace_333070
  have hstable : (prefixWord ++ tailWord_333070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333070).length < 2 ^ (prefixWord ++ tailWord_333070).sum := by decide
  have hdescent : baseEnd_333070 < baseStart_333070 := by decide
  rcases family_descends (prefixWord ++ tailWord_333070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333074 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_333074 : Nat := 118140960795 + 333074 * 2 ^ 59
def prefixEnd_333074 : Nat := 4983230072969 + 3 ^ 40 * 333074 * 2
def baseEnd_333074 : Nat := 19003006168415008904803

theorem tailTrace_333074 : CollatzResearch.WordTrace tailWord_333074 prefixEnd_333074 19003006168415008904803 := by
  unfold tailWord_333074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037051698834314338875569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8098804530224838237001517 3037051698834314338875569)
  ·
    refine ⟨2277788774125735754156677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3037051698834314338875569 2277788774125735754156677)
    ·
      refine ⟨427085395148575453904377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2277788774125735754156677 427085395148575453904377)
      ·
        refine ⟨320314046361431590428283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427085395148575453904377 320314046361431590428283)
        ·
          refine ⟨480471069542147385642425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320314046361431590428283 480471069542147385642425)
          ·
            refine ⟨360353302156610539231819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480471069542147385642425 360353302156610539231819)
            ·
              refine ⟨540529953234915808847729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360353302156610539231819 540529953234915808847729)
              ·
                refine ⟨405397464926186856635797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540529953234915808847729 405397464926186856635797)
                ·
                  refine ⟨19003006168415008904803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405397464926186856635797 19003006168415008904803)
                  ·
                    rfl

theorem cell23_333074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_333074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333074 prefixEnd_333074 := by exact prefixLift 333074
  have htrace : WordTrace (prefixWord ++ tailWord_333074) baseStart_333074 baseEnd_333074 := by
    simpa [prefixWord, tailWord_333074, baseEnd_333074] using wordTrace_append hprefix tailTrace_333074
  have hstable : (prefixWord ++ tailWord_333074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333074).length < 2 ^ (prefixWord ++ tailWord_333074).sum := by decide
  have hdescent : baseEnd_333074 < baseStart_333074 := by decide
  rcases family_descends (prefixWord ++ tailWord_333074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333093 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_333093 : Nat := 118140960795 + 333093 * 2 ^ 59
def prefixEnd_333093 : Nat := 4983230072969 + 3 ^ 40 * 333093 * 2
def baseEnd_333093 : Nat := 171036811648170505805639

theorem tailTrace_333093 : CollatzResearch.WordTrace tailWord_333093 prefixEnd_333093 171036811648170505805639 := by
  unfold tailWord_333093
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148899782268423600443933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8099266521512282400295955 12148899782268423600443933)
  ·
    refine ⟨4555837418350658850166475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12148899782268423600443933 4555837418350658850166475)
    ·
      refine ⟨6833756127525988275249713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555837418350658850166475 6833756127525988275249713)
      ·
        refine ⟨5125317095644491206437285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833756127525988275249713 5125317095644491206437285)
        ·
          refine ⟨960996955433342101206991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5125317095644491206437285 960996955433342101206991)
          ·
            refine ⟨1441495433150013151810487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960996955433342101206991 1441495433150013151810487)
            ·
              refine ⟨2162243149725019727715731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441495433150013151810487 2162243149725019727715731)
              ·
                refine ⟨3243364724587529591573597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162243149725019727715731 3243364724587529591573597)
                ·
                  refine ⟨1216261771720323596840099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243364724587529591573597 1216261771720323596840099)
                  ·
                    refine ⟨1824392657580485395260149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216261771720323596840099 1824392657580485395260149)
                    ·
                      refine ⟨171036811648170505805639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1824392657580485395260149 171036811648170505805639)
                      ·
                        rfl

theorem cell23_333093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_333093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333093 prefixEnd_333093 := by exact prefixLift 333093
  have htrace : WordTrace (prefixWord ++ tailWord_333093) baseStart_333093 baseEnd_333093 := by
    simpa [prefixWord, tailWord_333093, baseEnd_333093] using wordTrace_append hprefix tailTrace_333093
  have hstable : (prefixWord ++ tailWord_333093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333093).length < 2 ^ (prefixWord ++ tailWord_333093).sum := by decide
  have hdescent : baseEnd_333093 < baseStart_333093 := by decide
  rcases family_descends (prefixWord ++ tailWord_333093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333107 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 3, 2, 2]
def baseStart_333107 : Nat := 118140960795 + 333107 * 2 ^ 59
def prefixEnd_333107 : Nat := 4983230072969 + 3 ^ 40 * 333107 * 2
def baseEnd_333107 : Nat := 171044000377333451030575

theorem tailTrace_333107 : CollatzResearch.WordTrace tailWord_333107 prefixEnd_333107 171044000377333451030575 := by
  unfold tailWord_333107
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149410404217703991453575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8099606936145135994302383 12149410404217703991453575)
  ·
    refine ⟨18224115606326555987180363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149410404217703991453575 18224115606326555987180363)
    ·
      refine ⟨27336173409489833980770545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224115606326555987180363 27336173409489833980770545)
      ·
        refine ⟨20502130057117375485577909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27336173409489833980770545 20502130057117375485577909)
        ·
          refine ⟨1922074692854753951772929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20502130057117375485577909 1922074692854753951772929)
          ·
            refine ⟨1441556019641065463829697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922074692854753951772929 1441556019641065463829697)
            ·
              refine ⟨1081167014730799097872273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441556019641065463829697 1081167014730799097872273)
              ·
                refine ⟨810875261048099323404205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081167014730799097872273 810875261048099323404205)
                ·
                  refine ⟨304078222893037246276577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810875261048099323404205 304078222893037246276577)
                  ·
                    refine ⟨228058667169777934707433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304078222893037246276577 228058667169777934707433)
                    ·
                      refine ⟨171044000377333451030575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228058667169777934707433 171044000377333451030575)
                      ·
                        rfl

theorem cell23_333107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2, 2].length) (baseStart_333107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333107 prefixEnd_333107 := by exact prefixLift 333107
  have htrace : WordTrace (prefixWord ++ tailWord_333107) baseStart_333107 baseEnd_333107 := by
    simpa [prefixWord, tailWord_333107, baseEnd_333107] using wordTrace_append hprefix tailTrace_333107
  have hstable : (prefixWord ++ tailWord_333107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333107).length < 2 ^ (prefixWord ++ tailWord_333107).sum := by decide
  have hdescent : baseEnd_333107 < baseStart_333107 := by decide
  rcases family_descends (prefixWord ++ tailWord_333107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333123 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3]
def baseStart_333123 : Nat := 118140960795 + 333123 * 2 ^ 59
def prefixEnd_333123 : Nat := 4983230072969 + 3 ^ 40 * 333123 * 2
def baseEnd_333123 : Nat := 171052216067805388430501

theorem tailTrace_333123 : CollatzResearch.WordTrace tailWord_333123 prefixEnd_333123 171052216067805388430501 := by
  unfold tailWord_333123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149993972159738724036023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8099995981439825816024015 12149993972159738724036023)
  ·
    refine ⟨18224990958239608086054035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149993972159738724036023 18224990958239608086054035)
    ·
      refine ⟨27337486437359412129081053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18224990958239608086054035 27337486437359412129081053)
      ·
        refine ⟨10251557414009779548405395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27337486437359412129081053 10251557414009779548405395)
        ·
          refine ⟨15377336121014669322608093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10251557414009779548405395 15377336121014669322608093)
          ·
            refine ⟨5766501045380500995978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15377336121014669322608093 5766501045380500995978035)
            ·
              refine ⟨8649751568070751493967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5766501045380500995978035 8649751568070751493967053)
              ·
                refine ⟨3243656838026531810237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8649751568070751493967053 3243656838026531810237645)
                ·
                  refine ⟨1216371314259949428839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3243656838026531810237645 1216371314259949428839117)
                  ·
                    refine ⟨456139242847481035814669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216371314259949428839117 456139242847481035814669)
                    ·
                      refine ⟨171052216067805388430501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456139242847481035814669 171052216067805388430501)
                      ·
                        rfl

theorem cell23_333123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_333123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333123 prefixEnd_333123 := by exact prefixLift 333123
  have htrace : WordTrace (prefixWord ++ tailWord_333123) baseStart_333123 baseEnd_333123 := by
    simpa [prefixWord, tailWord_333123, baseEnd_333123] using wordTrace_append hprefix tailTrace_333123
  have hstable : (prefixWord ++ tailWord_333123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333123).length < 2 ^ (prefixWord ++ tailWord_333123).sum := by decide
  have hdescent : baseEnd_333123 < baseStart_333123 := by decide
  rcases family_descends (prefixWord ++ tailWord_333123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333157 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_333157 : Nat := 118140960795 + 333157 * 2 ^ 59
def prefixEnd_333157 : Nat := 4983230072969 + 3 ^ 40 * 333157 * 2
def baseEnd_333157 : Nat := 171069674410058255405345

theorem tailTrace_333157 : CollatzResearch.WordTrace tailWord_333157 prefixEnd_333157 171069674410058255405345 := by
  unfold tailWord_333157
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151234054036562530773725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8100822702691041687182483 12151234054036562530773725)
  ·
    refine ⟨4556712770263710949040147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12151234054036562530773725 4556712770263710949040147)
    ·
      refine ⟨6835069155395566423560221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556712770263710949040147 6835069155395566423560221)
      ·
        refine ⟨2563150933273337408835083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6835069155395566423560221 2563150933273337408835083)
        ·
          refine ⟨3844726399910006113252625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563150933273337408835083 3844726399910006113252625)
          ·
            refine ⟨2883544799932504584939469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844726399910006113252625 2883544799932504584939469)
            ·
              refine ⟨1081329299974689219352301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883544799932504584939469 1081329299974689219352301)
              ·
                refine ⟨405498487490508457257113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081329299974689219352301 405498487490508457257113)
                ·
                  refine ⟨304123865617881342942835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405498487490508457257113 304123865617881342942835)
                  ·
                    refine ⟨456185798426822014414253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304123865617881342942835 456185798426822014414253)
                    ·
                      refine ⟨171069674410058255405345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456185798426822014414253 171069674410058255405345)
                      ·
                        rfl

theorem cell23_333157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_333157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333157 prefixEnd_333157 := by exact prefixLift 333157
  have htrace : WordTrace (prefixWord ++ tailWord_333157) baseStart_333157 baseEnd_333157 := by
    simpa [prefixWord, tailWord_333157, baseEnd_333157] using wordTrace_append hprefix tailTrace_333157
  have hstable : (prefixWord ++ tailWord_333157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333157).length < 2 ^ (prefixWord ++ tailWord_333157).sum := by decide
  have hdescent : baseEnd_333157 < baseStart_333157 := by decide
  rcases family_descends (prefixWord ++ tailWord_333157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333183 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_333183 : Nat := 118140960795 + 333183 * 2 ^ 59
def prefixEnd_333183 : Nat := 4983230072969 + 3 ^ 40 * 333183 * 2
def baseEnd_333183 : Nat := 171083024907075153680225

theorem tailTrace_333183 : CollatzResearch.WordTrace tailWord_333183 prefixEnd_333183 171083024907075153680225 := by
  unfold tailWord_333183
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152182351942368971220203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8101454901294912647480135 12152182351942368971220203)
  ·
    refine ⟨18228273527913553456830305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12152182351942368971220203 18228273527913553456830305)
    ·
      refine ⟨13671205145935165092622729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18228273527913553456830305 13671205145935165092622729)
      ·
        refine ⟨10253403859451373819467047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13671205145935165092622729 10253403859451373819467047)
        ·
          refine ⟨15380105789177060729200571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10253403859451373819467047 15380105789177060729200571)
          ·
            refine ⟨23070158683765591093800857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15380105789177060729200571 23070158683765591093800857)
            ·
              refine ⟨17302619012824193320350643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23070158683765591093800857 17302619012824193320350643)
              ·
                refine ⟨25953928519236289980525965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17302619012824193320350643 25953928519236289980525965)
                ·
                  refine ⟨9732723194713608742697237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25953928519236289980525965 9732723194713608742697237)
                  ·
                    refine ⟨456221399752200409813933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9732723194713608742697237 456221399752200409813933)
                    ·
                      refine ⟨171083024907075153680225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456221399752200409813933 171083024907075153680225)
                      ·
                        rfl

theorem cell23_333183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_333183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333183 prefixEnd_333183 := by exact prefixLift 333183
  have htrace : WordTrace (prefixWord ++ tailWord_333183) baseStart_333183 baseEnd_333183 := by
    simpa [prefixWord, tailWord_333183, baseEnd_333183] using wordTrace_append hprefix tailTrace_333183
  have hstable : (prefixWord ++ tailWord_333183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333183).length < 2 ^ (prefixWord ++ tailWord_333183).sum := by decide
  have hdescent : baseEnd_333183 < baseStart_333183 := by decide
  rcases family_descends (prefixWord ++ tailWord_333183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333210 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_333210 : Nat := 118140960795 + 333210 * 2 ^ 59
def prefixEnd_333210 : Nat := 4983230072969 + 3 ^ 40 * 333210 * 2
def baseEnd_333210 : Nat := 171096888884746548042601

theorem tailTrace_333210 : CollatzResearch.WordTrace tailWord_333210 prefixEnd_333210 171096888884746548042601 := by
  unfold tailWord_333210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038291780711138145613271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8102111415229701721635389 3038291780711138145613271)
  ·
    refine ⟨4557437671066707218419907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3038291780711138145613271 4557437671066707218419907)
    ·
      refine ⟨6836156506600060827629861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557437671066707218419907 6836156506600060827629861)
      ·
        refine ⟨1281779344987511405180599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6836156506600060827629861 1281779344987511405180599)
        ·
          refine ⟨1922669017481267107770899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281779344987511405180599 1922669017481267107770899)
          ·
            refine ⟨2884003526221900661656349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922669017481267107770899 2884003526221900661656349)
            ·
              refine ⟨1081501322333212748121131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2884003526221900661656349 1081501322333212748121131)
              ·
                refine ⟨1622251983499819122181697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081501322333212748121131 1622251983499819122181697)
                ·
                  refine ⟨1216688987624864341636273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1622251983499819122181697 1216688987624864341636273)
                  ·
                    refine ⟨912516740718648256227205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216688987624864341636273 912516740718648256227205)
                    ·
                      refine ⟨171096888884746548042601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 912516740718648256227205 171096888884746548042601)
                      ·
                        rfl

theorem cell23_333210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_333210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333210 prefixEnd_333210 := by exact prefixLift 333210
  have htrace : WordTrace (prefixWord ++ tailWord_333210) baseStart_333210 baseEnd_333210 := by
    simpa [prefixWord, tailWord_333210, baseEnd_333210] using wordTrace_append hprefix tailTrace_333210
  have hstable : (prefixWord ++ tailWord_333210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333210).length < 2 ^ (prefixWord ++ tailWord_333210).sum := by decide
  have hdescent : baseEnd_333210 < baseStart_333210 := by decide
  rcases family_descends (prefixWord ++ tailWord_333210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333237 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 5]
def baseStart_333237 : Nat := 118140960795 + 333237 * 2 ^ 59
def prefixEnd_333237 : Nat := 4983230072969 + 3 ^ 40 * 333237 * 2
def baseEnd_333237 : Nat := 19012305873601993600553

theorem tailTrace_333237 : CollatzResearch.WordTrace tailWord_333237 prefixEnd_333237 19012305873601993600553 := by
  unfold tailWord_333237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154151893746736193685965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8102767929164490795790643 12154151893746736193685965)
  ·
    refine ⟨4557806960155026072632237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12154151893746736193685965 4557806960155026072632237)
    ·
      refine ⟨1709177610058134777237089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4557806960155026072632237 1709177610058134777237089)
      ·
        refine ⟨1281883207543601082927817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1709177610058134777237089 1281883207543601082927817)
        ·
          refine ⟨961412405657700812195863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1281883207543601082927817 961412405657700812195863)
          ·
            refine ⟨1442118608486551218293795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961412405657700812195863 1442118608486551218293795)
            ·
              refine ⟨2163177912729826827440693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442118608486551218293795 2163177912729826827440693)
              ·
                refine ⟨202797929318421265072565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2163177912729826827440693 202797929318421265072565)
                ·
                  refine ⟨19012305873601993600553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202797929318421265072565 19012305873601993600553)
                  ·
                    rfl

theorem cell23_333237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_333237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333237 prefixEnd_333237 := by exact prefixLift 333237
  have htrace : WordTrace (prefixWord ++ tailWord_333237) baseStart_333237 baseEnd_333237 := by
    simpa [prefixWord, tailWord_333237, baseEnd_333237] using wordTrace_append hprefix tailTrace_333237
  have hstable : (prefixWord ++ tailWord_333237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333237).length < 2 ^ (prefixWord ++ tailWord_333237).sum := by decide
  have hdescent : baseEnd_333237 < baseStart_333237 := by decide
  rcases family_descends (prefixWord ++ tailWord_333237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333280 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_333280 : Nat := 118140960795 + 333280 * 2 ^ 59
def prefixEnd_333280 : Nat := 4983230072969 + 3 ^ 40 * 333280 * 2
def baseEnd_333280 : Nat := 57044277510187091389093

theorem tailTrace_333280 : CollatzResearch.WordTrace tailWord_333280 prefixEnd_333280 57044277510187091389093 := by
  unfold tailWord_333280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077860116295477268750647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8103813488393969691667529 6077860116295477268750647)
  ·
    refine ⟨9116790174443215903125971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6077860116295477268750647 9116790174443215903125971)
    ·
      refine ⟨13675185261664823854688957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9116790174443215903125971 13675185261664823854688957)
      ·
        refine ⟨5128194473124308945508359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13675185261664823854688957 5128194473124308945508359)
        ·
          refine ⟨7692291709686463418262539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5128194473124308945508359 7692291709686463418262539)
          ·
            refine ⟨11538437564529695127393809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692291709686463418262539 11538437564529695127393809)
            ·
              refine ⟨8653828173397271345545357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11538437564529695127393809 8653828173397271345545357)
              ·
                refine ⟨3245185565023976754579509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8653828173397271345545357 3245185565023976754579509)
                ·
                  refine ⟨304236146720997820741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3245185565023976754579509 304236146720997820741829)
                  ·
                    refine ⟨57044277510187091389093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304236146720997820741829 57044277510187091389093)
                    ·
                      rfl

theorem cell23_333280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_333280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333280 prefixEnd_333280 := by exact prefixLift 333280
  have htrace : WordTrace (prefixWord ++ tailWord_333280) baseStart_333280 baseEnd_333280 := by
    simpa [prefixWord, tailWord_333280, baseEnd_333280] using wordTrace_append hprefix tailTrace_333280
  have hstable : (prefixWord ++ tailWord_333280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333280).length < 2 ^ (prefixWord ++ tailWord_333280).sum := by decide
  have hdescent : baseEnd_333280 < baseStart_333280 := by decide
  rcases family_descends (prefixWord ++ tailWord_333280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333370 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_333370 : Nat := 118140960795 + 333370 * 2 ^ 59
def prefixEnd_333370 : Nat := 4983230072969 + 3 ^ 40 * 333370 * 2
def baseEnd_333370 : Nat := 57059681929821974013955

theorem tailTrace_333370 : CollatzResearch.WordTrace tailWord_333370 prefixEnd_333370 57059681929821974013955 := by
  unfold tailWord_333370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039750700566224977069391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8106001868176599938851709 3039750700566224977069391)
  ·
    refine ⟨4559626050849337465604087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039750700566224977069391 4559626050849337465604087)
    ·
      refine ⟨6839439076274006198406131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559626050849337465604087 6839439076274006198406131)
      ·
        refine ⟨10259158614411009297609197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839439076274006198406131 10259158614411009297609197)
        ·
          refine ⟨3847184480404128486603449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10259158614411009297609197 3847184480404128486603449)
          ·
            refine ⟨2885388360303096364952587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847184480404128486603449 2885388360303096364952587)
            ·
              refine ⟨4328082540454644547428881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885388360303096364952587 4328082540454644547428881)
              ·
                refine ⟨3246061905340983410571661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4328082540454644547428881 3246061905340983410571661)
                ·
                  refine ⟨1217273214502868778964373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3246061905340983410571661 1217273214502868778964373)
                  ·
                    refine ⟨57059681929821974013955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1217273214502868778964373 57059681929821974013955)
                    ·
                      rfl

theorem cell23_333370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_333370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333370 prefixEnd_333370 := by exact prefixLift 333370
  have htrace : WordTrace (prefixWord ++ tailWord_333370) baseStart_333370 baseEnd_333370 := by
    simpa [prefixWord, tailWord_333370, baseEnd_333370] using wordTrace_append hprefix tailTrace_333370
  have hstable : (prefixWord ++ tailWord_333370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333370).length < 2 ^ (prefixWord ++ tailWord_333370).sum := by decide
  have hdescent : baseEnd_333370 < baseStart_333370 := by decide
  rcases family_descends (prefixWord ++ tailWord_333370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333377 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_333377 : Nat := 118140960795 + 333377 * 2 ^ 59
def prefixEnd_333377 : Nat := 4983230072969 + 3 ^ 40 * 333377 * 2
def baseEnd_333377 : Nat := 171182640154047394654333

theorem tailTrace_333377 : CollatzResearch.WordTrace tailWord_333377 prefixEnd_333377 171182640154047394654333 := by
  unfold tailWord_333377
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159258113239540103782385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8106172075493026735854923 12159258113239540103782385)
  ·
    refine ⟨9119443584929655077836789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12159258113239540103782385 9119443584929655077836789)
    ·
      refine ⟨854947836087155163547199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9119443584929655077836789 854947836087155163547199)
      ·
        refine ⟨1282421754130732745320799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854947836087155163547199 1282421754130732745320799)
        ·
          refine ⟨1923632631196099117981199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282421754130732745320799 1923632631196099117981199)
          ·
            refine ⟨2885448946794148676971799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923632631196099117981199 2885448946794148676971799)
            ·
              refine ⟨4328173420191223015457699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885448946794148676971799 4328173420191223015457699)
              ·
                refine ⟨6492260130286834523186549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328173420191223015457699 6492260130286834523186549)
                ·
                  refine ⟨608649387214390736548739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6492260130286834523186549 608649387214390736548739)
                  ·
                    refine ⟨912974080821586104823109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 608649387214390736548739 912974080821586104823109)
                    ·
                      refine ⟨171182640154047394654333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 912974080821586104823109 171182640154047394654333)
                      ·
                        rfl

theorem cell23_333377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_333377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333377 prefixEnd_333377 := by exact prefixLift 333377
  have htrace : WordTrace (prefixWord ++ tailWord_333377) baseStart_333377 baseEnd_333377 := by
    simpa [prefixWord, tailWord_333377, baseEnd_333377] using wordTrace_append hprefix tailTrace_333377
  have hstable : (prefixWord ++ tailWord_333377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333377).length < 2 ^ (prefixWord ++ tailWord_333377).sum := by decide
  have hdescent : baseEnd_333377 < baseStart_333377 := by decide
  rcases family_descends (prefixWord ++ tailWord_333377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333411 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 1, 1, 4]
def baseStart_333411 : Nat := 118140960795 + 333411 * 2 ^ 59
def prefixEnd_333411 : Nat := 4983230072969 + 3 ^ 40 * 333411 * 2
def baseEnd_333411 : Nat := 171200098496300261629177

theorem tailTrace_333411 : CollatzResearch.WordTrace tailWord_333411 prefixEnd_333411 171200098496300261629177 := by
  unfold tailWord_333411
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160498195116363910520087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8106998796744242607013391 12160498195116363910520087)
  ·
    refine ⟨18240747292674545865780131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12160498195116363910520087 18240747292674545865780131)
    ·
      refine ⟨27361120939011818798670197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18240747292674545865780131 27361120939011818798670197)
      ·
        refine ⟨2565105088032358012375331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27361120939011818798670197 2565105088032358012375331)
        ·
          refine ⟨3847657632048537018562997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565105088032358012375331 3847657632048537018562997)
          ·
            refine ⟨360717903004550345490281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3847657632048537018562997 360717903004550345490281)
            ·
              refine ⟨270538427253412759117711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360717903004550345490281 270538427253412759117711)
              ·
                refine ⟨405807640880119138676567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270538427253412759117711 405807640880119138676567)
                ·
                  refine ⟨608711461320178708014851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405807640880119138676567 608711461320178708014851)
                  ·
                    refine ⟨913067191980268062022277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 608711461320178708014851 913067191980268062022277)
                    ·
                      refine ⟨171200098496300261629177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 913067191980268062022277 171200098496300261629177)
                      ·
                        rfl

theorem cell23_333411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_333411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333411 prefixEnd_333411 := by exact prefixLift 333411
  have htrace : WordTrace (prefixWord ++ tailWord_333411) baseStart_333411 baseEnd_333411 := by
    simpa [prefixWord, tailWord_333411, baseEnd_333411] using wordTrace_append hprefix tailTrace_333411
  have hstable : (prefixWord ++ tailWord_333411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333411).length < 2 ^ (prefixWord ++ tailWord_333411).sum := by decide
  have hdescent : baseEnd_333411 < baseStart_333411 := by decide
  rcases family_descends (prefixWord ++ tailWord_333411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_333420 : Nat := 118140960795 + 333420 * 2 ^ 59
def prefixEnd_333420 : Nat := 4983230072969 + 3 ^ 40 * 333420 * 2
def baseEnd_333420 : Nat := 171204719822190726416635

theorem tailTrace_333420 : CollatzResearch.WordTrace tailWord_333420 prefixEnd_333420 171204719822190726416635 := by
  unfold tailWord_333420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080413226041879223798857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8107217634722505631731809 6080413226041879223798857)
  ·
    refine ⟨4560309919531409417849143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6080413226041879223798857 4560309919531409417849143)
    ·
      refine ⟨6840464879297114126773715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560309919531409417849143 6840464879297114126773715)
      ·
        refine ⟨10260697318945671190160573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840464879297114126773715 10260697318945671190160573)
        ·
          refine ⟨3847761494604626696310215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10260697318945671190160573 3847761494604626696310215)
          ·
            refine ⟨5771642241906940044465323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847761494604626696310215 5771642241906940044465323)
            ·
              refine ⟨8657463362860410066697985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5771642241906940044465323 8657463362860410066697985)
              ·
                refine ⟨6493097522145307550023489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8657463362860410066697985 6493097522145307550023489)
                ·
                  refine ⟨4869823141608980662517617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493097522145307550023489 4869823141608980662517617)
                  ·
                    refine ⟨3652367356206735496888213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4869823141608980662517617 3652367356206735496888213)
                    ·
                      refine ⟨171204719822190726416635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3652367356206735496888213 171204719822190726416635)
                      ·
                        rfl

theorem cell23_333420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_333420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333420 prefixEnd_333420 := by exact prefixLift 333420
  have htrace : WordTrace (prefixWord ++ tailWord_333420) baseStart_333420 baseEnd_333420 := by
    simpa [prefixWord, tailWord_333420, baseEnd_333420] using wordTrace_append hprefix tailTrace_333420
  have hstable : (prefixWord ++ tailWord_333420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333420).length < 2 ^ (prefixWord ++ tailWord_333420).sum := by decide
  have hdescent : baseEnd_333420 < baseStart_333420 := by decide
  rcases family_descends (prefixWord ++ tailWord_333420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333448 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_333448 : Nat := 118140960795 + 333448 * 2 ^ 59
def prefixEnd_333448 : Nat := 4983230072969 + 3 ^ 40 * 333448 * 2
def baseEnd_333448 : Nat := 171219097280516616866507

theorem tailTrace_333448 : CollatzResearch.WordTrace tailWord_333448 prefixEnd_333448 171219097280516616866507 := by
  unfold tailWord_333448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080923847991159614808499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8107898463988212819744665 6080923847991159614808499)
  ·
    refine ⟨9121385771986739422212749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6080923847991159614808499 9121385771986739422212749)
    ·
      refine ⟨3420519664495027283329781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9121385771986739422212749 3420519664495027283329781)
      ·
        refine ⟨320673718546408807812167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3420519664495027283329781 320673718546408807812167)
        ·
          refine ⟨481010577819613211718251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320673718546408807812167 481010577819613211718251)
          ·
            refine ⟨721515866729419817577377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481010577819613211718251 721515866729419817577377)
            ·
              refine ⟨541136900047064863183033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721515866729419817577377 541136900047064863183033)
              ·
                refine ⟨405852675035298647387275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541136900047064863183033 405852675035298647387275)
                ·
                  refine ⟨608779012552947971080913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405852675035298647387275 608779012552947971080913)
                  ·
                    refine ⟨456584259414710978310685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608779012552947971080913 456584259414710978310685)
                    ·
                      refine ⟨171219097280516616866507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456584259414710978310685 171219097280516616866507)
                      ·
                        rfl

theorem cell23_333448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_333448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333448 prefixEnd_333448 := by exact prefixLift 333448
  have htrace : WordTrace (prefixWord ++ tailWord_333448) baseStart_333448 baseEnd_333448 := by
    simpa [prefixWord, tailWord_333448, baseEnd_333448] using wordTrace_append hprefix tailTrace_333448
  have hstable : (prefixWord ++ tailWord_333448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333448).length < 2 ^ (prefixWord ++ tailWord_333448).sum := by decide
  have hdescent : baseEnd_333448 < baseStart_333448 := by decide
  rcases family_descends (prefixWord ++ tailWord_333448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333487 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_333487 : Nat := 118140960795 + 333487 * 2 ^ 59
def prefixEnd_333487 : Nat := 4983230072969 + 3 ^ 40 * 333487 * 2
def baseEnd_333487 : Nat := 171239123026041964278827

theorem tailTrace_333487 : CollatzResearch.WordTrace tailWord_333487 prefixEnd_333487 171239123026041964278827 := by
  unfold tailWord_333487
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163270142841028890286715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8108846761894019260191143 12163270142841028890286715)
  ·
    refine ⟨18244905214261543335430073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12163270142841028890286715 18244905214261543335430073)
    ·
      refine ⟨13683678910696157501572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18244905214261543335430073 13683678910696157501572555)
      ·
        refine ⟨20525518366044236252358833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13683678910696157501572555 20525518366044236252358833)
        ·
          refine ⟨15394138774533177189269125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20525518366044236252358833 15394138774533177189269125)
          ·
            refine ⟨2886401020224970722987961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15394138774533177189269125 2886401020224970722987961)
            ·
              refine ⟨2164800765168728042240971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886401020224970722987961 2164800765168728042240971)
              ·
                refine ⟨3247201147753092063361457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164800765168728042240971 3247201147753092063361457)
                ·
                  refine ⟨2435400860814819047521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3247201147753092063361457 2435400860814819047521093)
                  ·
                    refine ⟨456637661402778571410205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2435400860814819047521093 456637661402778571410205)
                    ·
                      refine ⟨171239123026041964278827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456637661402778571410205 171239123026041964278827)
                      ·
                        rfl

theorem cell23_333487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_333487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333487 prefixEnd_333487 := by exact prefixLift 333487
  have htrace : WordTrace (prefixWord ++ tailWord_333487) baseStart_333487 baseEnd_333487 := by
    simpa [prefixWord, tailWord_333487, baseEnd_333487] using wordTrace_append hprefix tailTrace_333487
  have hstable : (prefixWord ++ tailWord_333487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333487).length < 2 ^ (prefixWord ++ tailWord_333487).sum := by decide
  have hdescent : baseEnd_333487 < baseStart_333487 := by decide
  rcases family_descends (prefixWord ++ tailWord_333487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333497 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_333497 : Nat := 118140960795 + 333497 * 2 ^ 59
def prefixEnd_333497 : Nat := 4983230072969 + 3 ^ 40 * 333497 * 2
def baseEnd_333497 : Nat := 171244257832586925153781

theorem tailTrace_333497 : CollatzResearch.WordTrace tailWord_333497 prefixEnd_333497 171244257832586925153781 := by
  unfold tailWord_333497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163634872804800598150745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8109089915203200398767163 12163634872804800598150745)
  ·
    refine ⟨9122726154603600448613059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12163634872804800598150745 9122726154603600448613059)
    ·
      refine ⟨13684089231905400672919589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9122726154603600448613059 13684089231905400672919589)
      ·
        refine ⟨2565766730982262626172423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13684089231905400672919589 2565766730982262626172423)
        ·
          refine ⟨3848650096473393939258635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2565766730982262626172423 3848650096473393939258635)
          ·
            refine ⟨5772975144710090908887953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3848650096473393939258635 5772975144710090908887953)
            ·
              refine ⟨4329731358532568181665965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5772975144710090908887953 4329731358532568181665965)
              ·
                refine ⟨1623649259449713068124737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4329731358532568181665965 1623649259449713068124737)
                ·
                  refine ⟨1217736944587284801093553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623649259449713068124737 1217736944587284801093553)
                  ·
                    refine ⟨913302708440463600820165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1217736944587284801093553 913302708440463600820165)
                    ·
                      refine ⟨171244257832586925153781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 913302708440463600820165 171244257832586925153781)
                      ·
                        rfl

theorem cell23_333497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_333497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333497 prefixEnd_333497 := by exact prefixLift 333497
  have htrace : WordTrace (prefixWord ++ tailWord_333497) baseStart_333497 baseEnd_333497 := by
    simpa [prefixWord, tailWord_333497, baseEnd_333497] using wordTrace_append hprefix tailTrace_333497
  have hstable : (prefixWord ++ tailWord_333497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333497).length < 2 ^ (prefixWord ++ tailWord_333497).sum := by decide
  have hdescent : baseEnd_333497 < baseStart_333497 := by decide
  rcases family_descends (prefixWord ++ tailWord_333497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333547 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_333547 : Nat := 118140960795 + 333547 * 2 ^ 59
def prefixEnd_333547 : Nat := 4983230072969 + 3 ^ 40 * 333547 * 2
def baseEnd_333547 : Nat := 171269931865311729528551

theorem tailTrace_333547 : CollatzResearch.WordTrace tailWord_333547 prefixEnd_333547 171269931865311729528551 := by
  unfold tailWord_333547
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165458522623659137470895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8110305681749106091647263 12165458522623659137470895)
  ·
    refine ⟨18248187783935488706206343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165458522623659137470895 18248187783935488706206343)
    ·
      refine ⟨27372281675903233059309515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248187783935488706206343 27372281675903233059309515)
      ·
        refine ⟨41058422513854849588964273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27372281675903233059309515 41058422513854849588964273)
        ·
          refine ⟨30793816885391137191723205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41058422513854849588964273 30793816885391137191723205)
          ·
            refine ⟨5773840666010838223448101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30793816885391137191723205 5773840666010838223448101)
            ·
              refine ⟨1082595124877032166896519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5773840666010838223448101 1082595124877032166896519)
              ·
                refine ⟨1623892687315548250344779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082595124877032166896519 1623892687315548250344779)
                ·
                  refine ⟨2435839030973322375517169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623892687315548250344779 2435839030973322375517169)
                  ·
                    refine ⟨1826879273229991781637877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435839030973322375517169 1826879273229991781637877)
                    ·
                      refine ⟨171269931865311729528551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1826879273229991781637877 171269931865311729528551)
                      ·
                        rfl

theorem cell23_333547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_333547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333547 prefixEnd_333547 := by exact prefixLift 333547
  have htrace : WordTrace (prefixWord ++ tailWord_333547) baseStart_333547 baseEnd_333547 := by
    simpa [prefixWord, tailWord_333547, baseEnd_333547] using wordTrace_append hprefix tailTrace_333547
  have hstable : (prefixWord ++ tailWord_333547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333547).length < 2 ^ (prefixWord ++ tailWord_333547).sum := by decide
  have hdescent : baseEnd_333547 < baseStart_333547 := by decide
  rcases family_descends (prefixWord ++ tailWord_333547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333591 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_333591 : Nat := 118140960795 + 333591 * 2 ^ 59
def prefixEnd_333591 : Nat := 4983230072969 + 3 ^ 40 * 333591 * 2
def baseEnd_333591 : Nat := 171292525014109557378349

theorem tailTrace_333591 : CollatzResearch.WordTrace tailWord_333591 prefixEnd_333591 171292525014109557378349 := by
  unfold tailWord_333591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12167063334464254652072627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8111375556309503101381751 12167063334464254652072627)
  ·
    refine ⟨18250595001696381978108941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12167063334464254652072627 18250595001696381978108941)
    ·
      refine ⟨6843973125636143241790853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18250595001696381978108941 6843973125636143241790853)
      ·
        refine ⟨1283244961056776857835785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6843973125636143241790853 1283244961056776857835785)
        ·
          refine ⟨962433720792582643376839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283244961056776857835785 962433720792582643376839)
          ·
            refine ⟨1443650581188873965065259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962433720792582643376839 1443650581188873965065259)
            ·
              refine ⟨2165475871783310947597889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443650581188873965065259 2165475871783310947597889)
              ·
                refine ⟨1624106903837483210698417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165475871783310947597889 1624106903837483210698417)
                ·
                  refine ⟨1218080177878112408023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624106903837483210698417 1218080177878112408023813)
                  ·
                    refine ⟨228390033352146076504465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218080177878112408023813 228390033352146076504465)
                    ·
                      refine ⟨171292525014109557378349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228390033352146076504465 171292525014109557378349)
                      ·
                        rfl

theorem cell23_333591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_333591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333591 prefixEnd_333591 := by exact prefixLift 333591
  have htrace : WordTrace (prefixWord ++ tailWord_333591) baseStart_333591 baseEnd_333591 := by
    simpa [prefixWord, tailWord_333591, baseEnd_333591] using wordTrace_append hprefix tailTrace_333591
  have hstable : (prefixWord ++ tailWord_333591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333591).length < 2 ^ (prefixWord ++ tailWord_333591).sum := by decide
  have hdescent : baseEnd_333591 < baseStart_333591 := by decide
  rcases family_descends (prefixWord ++ tailWord_333591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333601 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_333601 : Nat := 118140960795 + 333601 * 2 ^ 59
def prefixEnd_333601 : Nat := 4983230072969 + 3 ^ 40 * 333601 * 2
def baseEnd_333601 : Nat := 57099219940218172751101

theorem tailTrace_333601 : CollatzResearch.WordTrace tailWord_333601 prefixEnd_333601 57099219940218172751101 := by
  unfold tailWord_333601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12167428064428026359936657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8111618709618684239957771 12167428064428026359936657)
  ·
    refine ⟨9125571048321019769952493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12167428064428026359936657 9125571048321019769952493)
    ·
      refine ⟨3422089143120382413732185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9125571048321019769952493 3422089143120382413732185)
      ·
        refine ⟨2566566857340286810299139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3422089143120382413732185 2566566857340286810299139)
        ·
          refine ⟨3849850286010430215448709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566566857340286810299139 3849850286010430215448709)
          ·
            refine ⟨721846928626955665396633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3849850286010430215448709 721846928626955665396633)
            ·
              refine ⟨541385196470216749047475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721846928626955665396633 541385196470216749047475)
              ·
                refine ⟨812077794705325123571213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541385196470216749047475 812077794705325123571213)
                ·
                  refine ⟨304529173014496921339205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812077794705325123571213 304529173014496921339205)
                  ·
                    refine ⟨57099219940218172751101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304529173014496921339205 57099219940218172751101)
                    ·
                      rfl

theorem cell23_333601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_333601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333601 prefixEnd_333601 := by exact prefixLift 333601
  have htrace : WordTrace (prefixWord ++ tailWord_333601) baseStart_333601 baseEnd_333601 := by
    simpa [prefixWord, tailWord_333601, baseEnd_333601] using wordTrace_append hprefix tailTrace_333601
  have hstable : (prefixWord ++ tailWord_333601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333601).length < 2 ^ (prefixWord ++ tailWord_333601).sum := by decide
  have hdescent : baseEnd_333601 < baseStart_333601 := by decide
  rcases family_descends (prefixWord ++ tailWord_333601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333678 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_333678 : Nat := 118140960795 + 333678 * 2 ^ 59
def prefixEnd_333678 : Nat := 4983230072969 + 3 ^ 40 * 333678 * 2
def baseEnd_333678 : Nat := 57112399277016905663483

theorem tailTrace_333678 : CollatzResearch.WordTrace tailWord_333678 prefixEnd_333678 57112399277016905663483 := by
  unfold tailWord_333678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521279560643633563811211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8113490990099379006993125 1521279560643633563811211)
  ·
    refine ⟨2281919340965450345716817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1521279560643633563811211 2281919340965450345716817)
    ·
      refine ⟨1711439505724087759287613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2281919340965450345716817 1711439505724087759287613)
      ·
        refine ⟨641789814646532909732855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1711439505724087759287613 641789814646532909732855)
        ·
          refine ⟨962684721969799364599283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641789814646532909732855 962684721969799364599283)
          ·
            refine ⟨1444027082954699046898925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962684721969799364599283 1444027082954699046898925)
            ·
              refine ⟨541510156108012142587097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444027082954699046898925 541510156108012142587097)
              ·
                refine ⟨406132617081009106940323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541510156108012142587097 406132617081009106940323)
                ·
                  refine ⟨609198925621513660410485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406132617081009106940323 609198925621513660410485)
                  ·
                    refine ⟨57112399277016905663483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609198925621513660410485 57112399277016905663483)
                    ·
                      rfl

theorem cell23_333678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_333678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333678 prefixEnd_333678 := by exact prefixLift 333678
  have htrace : WordTrace (prefixWord ++ tailWord_333678) baseStart_333678 baseEnd_333678 := by
    simpa [prefixWord, tailWord_333678, baseEnd_333678] using wordTrace_append hprefix tailTrace_333678
  have hstable : (prefixWord ++ tailWord_333678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333678).length < 2 ^ (prefixWord ++ tailWord_333678).sum := by decide
  have hdescent : baseEnd_333678 < baseStart_333678 := by decide
  rcases family_descends (prefixWord ++ tailWord_333678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333704 : List Nat := [2, 1, 3, 3, 3, 11]
def baseStart_333704 : Nat := 118140960795 + 333704 * 2 ^ 59
def prefixEnd_333704 : Nat := 4983230072969 + 3 ^ 40 * 333704 * 2
def baseEnd_333704 : Nat := 705146289415916112203

theorem tailTrace_333704 : CollatzResearch.WordTrace tailWord_333704 prefixEnd_333704 705146289415916112203 := by
  unfold tailWord_333704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085592391527437475468083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8114123188703249967290777 6085592391527437475468083)
  ·
    refine ⟨9128388587291156213202125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085592391527437475468083 9128388587291156213202125)
    ·
      refine ⟨3423145720234183579950797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9128388587291156213202125 3423145720234183579950797)
      ·
        refine ⟨1283679645087818842481549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3423145720234183579950797 1283679645087818842481549)
        ·
          refine ⟨481379866907932065930581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1283679645087818842481549 481379866907932065930581)
          ·
            refine ⟨705146289415916112203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 481379866907932065930581 705146289415916112203)
            ·
              rfl

theorem cell23_333704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 11].length) (baseStart_333704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333704 prefixEnd_333704 := by exact prefixLift 333704
  have htrace : WordTrace (prefixWord ++ tailWord_333704) baseStart_333704 baseEnd_333704 := by
    simpa [prefixWord, tailWord_333704, baseEnd_333704] using wordTrace_append hprefix tailTrace_333704
  have hstable : (prefixWord ++ tailWord_333704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333704).length < 2 ^ (prefixWord ++ tailWord_333704).sum := by decide
  have hdescent : baseEnd_333704 < baseStart_333704 := by decide
  rcases family_descends (prefixWord ++ tailWord_333704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333731 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 3]
def baseStart_333731 : Nat := 118140960795 + 333731 * 2 ^ 59
def prefixEnd_333731 : Nat := 4983230072969 + 3 ^ 40 * 333731 * 2
def baseEnd_333731 : Nat := 171364412305739009627705

theorem tailTrace_333731 : CollatzResearch.WordTrace tailWord_333731 prefixEnd_333731 171364412305739009627705 := by
  unfold tailWord_333731
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172169553957058562169047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8114779702638039041446031 12172169553957058562169047)
  ·
    refine ⟨18258254330935587843253571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172169553957058562169047 18258254330935587843253571)
    ·
      refine ⟨27387381496403381764880357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258254330935587843253571 27387381496403381764880357)
      ·
        refine ⟨5135134030575634080915067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27387381496403381764880357 5135134030575634080915067)
        ·
          refine ⟨7702701045863451121372601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135134030575634080915067 7702701045863451121372601)
          ·
            refine ⟨5777025784397588341029451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7702701045863451121372601 5777025784397588341029451)
            ·
              refine ⟨8665538676596382511544177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5777025784397588341029451 8665538676596382511544177)
              ·
                refine ⟨6499154007447286883658133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8665538676596382511544177 6499154007447286883658133)
                ·
                  refine ⟨304647844099091572671475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6499154007447286883658133 304647844099091572671475)
                  ·
                    refine ⟨456971766148637359007213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304647844099091572671475 456971766148637359007213)
                    ·
                      refine ⟨171364412305739009627705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 456971766148637359007213 171364412305739009627705)
                      ·
                        rfl

theorem cell23_333731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_333731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333731 prefixEnd_333731 := by exact prefixLift 333731
  have htrace : WordTrace (prefixWord ++ tailWord_333731) baseStart_333731 baseEnd_333731 := by
    simpa [prefixWord, tailWord_333731, baseEnd_333731] using wordTrace_append hprefix tailTrace_333731
  have hstable : (prefixWord ++ tailWord_333731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333731).length < 2 ^ (prefixWord ++ tailWord_333731).sum := by decide
  have hdescent : baseEnd_333731 < baseStart_333731 := by decide
  rcases family_descends (prefixWord ++ tailWord_333731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333754 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_333754 : Nat := 118140960795 + 333754 * 2 ^ 59
def prefixEnd_333754 : Nat := 4983230072969 + 3 ^ 40 * 333754 * 2
def baseEnd_333754 : Nat := 171376222360792419640099

theorem tailTrace_333754 : CollatzResearch.WordTrace tailWord_333754 prefixEnd_333754 171376222360792419640099 := by
  unfold tailWord_333754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043252108218433372564079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8115338955249155660170877 3043252108218433372564079)
  ·
    refine ⟨4564878162327650058846119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3043252108218433372564079 4564878162327650058846119)
    ·
      refine ⟨6847317243491475088269179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4564878162327650058846119 6847317243491475088269179)
      ·
        refine ⟨10270975865237212632403769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6847317243491475088269179 10270975865237212632403769)
        ·
          refine ⟨7703231898927909474302827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10270975865237212632403769 7703231898927909474302827)
          ·
            refine ⟨11554847848391864211454241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703231898927909474302827 11554847848391864211454241)
            ·
              refine ⟨8666135886293898158590681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11554847848391864211454241 8666135886293898158590681)
              ·
                refine ⟨6499601914720423618943011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666135886293898158590681 6499601914720423618943011)
                ·
                  refine ⟨9749402872080635428414517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6499601914720423618943011 9749402872080635428414517)
                  ·
                    refine ⟨914006519257559571413861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9749402872080635428414517 914006519257559571413861)
                    ·
                      refine ⟨171376222360792419640099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 914006519257559571413861 171376222360792419640099)
                      ·
                        rfl

theorem cell23_333754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_333754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333754 prefixEnd_333754 := by exact prefixLift 333754
  have htrace : WordTrace (prefixWord ++ tailWord_333754) baseStart_333754 baseEnd_333754 := by
    simpa [prefixWord, tailWord_333754, baseEnd_333754] using wordTrace_append hprefix tailTrace_333754
  have hstable : (prefixWord ++ tailWord_333754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333754).length < 2 ^ (prefixWord ++ tailWord_333754).sum := by decide
  have hdescent : baseEnd_333754 < baseStart_333754 := by decide
  rcases family_descends (prefixWord ++ tailWord_333754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333781 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_333781 : Nat := 118140960795 + 333781 * 2 ^ 59
def prefixEnd_333781 : Nat := 4983230072969 + 3 ^ 40 * 333781 * 2
def baseEnd_333781 : Nat := 57130028779487938000825

theorem tailTrace_333781 : CollatzResearch.WordTrace tailWord_333781 prefixEnd_333781 57130028779487938000825 := by
  unfold tailWord_333781
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173993203775917101489197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8115995469183944734326131 12173993203775917101489197)
  ·
    refine ⟨4565247451415968913058449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12173993203775917101489197 4565247451415968913058449)
    ·
      refine ⟨3423935588561976684793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4565247451415968913058449 3423935588561976684793837)
      ·
        refine ⟨1283975845710741256797689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3423935588561976684793837 1283975845710741256797689)
        ·
          refine ⟨962981884283055942598267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283975845710741256797689 962981884283055942598267)
          ·
            refine ⟨1444472826424583913897401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962981884283055942598267 1444472826424583913897401)
            ·
              refine ⟨1083354619818437935423051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444472826424583913897401 1083354619818437935423051)
              ·
                refine ⟨1625031929727656903134577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083354619818437935423051 1625031929727656903134577)
                ·
                  refine ⟨1218773947295742677350933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625031929727656903134577 1218773947295742677350933)
                  ·
                    refine ⟨57130028779487938000825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1218773947295742677350933 57130028779487938000825)
                    ·
                      rfl

theorem cell23_333781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_333781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333781 prefixEnd_333781 := by exact prefixLift 333781
  have htrace : WordTrace (prefixWord ++ tailWord_333781) baseStart_333781 baseEnd_333781 := by
    simpa [prefixWord, tailWord_333781, baseEnd_333781] using wordTrace_append hprefix tailTrace_333781
  have hstable : (prefixWord ++ tailWord_333781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333781).length < 2 ^ (prefixWord ++ tailWord_333781).sum := by decide
  have hdescent : baseEnd_333781 < baseStart_333781 := by decide
  rcases family_descends (prefixWord ++ tailWord_333781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333782 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_333782 : Nat := 118140960795 + 333782 * 2 ^ 59
def prefixEnd_333782 : Nat := 4983230072969 + 3 ^ 40 * 333782 * 2
def baseEnd_333782 : Nat := 171390599819118310089971

theorem tailTrace_333782 : CollatzResearch.WordTrace tailWord_333782 prefixEnd_333782 171390599819118310089971 := by
  unfold tailWord_333782
  simp only [CollatzResearch.WordTrace]
  refine ⟨760876854798268392017225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8116019784514862848183733 760876854798268392017225)
  ·
    refine ⟨570657641098701294012919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 760876854798268392017225 570657641098701294012919)
    ·
      refine ⟨855986461648051941019379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570657641098701294012919 855986461648051941019379)
      ·
        refine ⟨1283979692472077911529069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855986461648051941019379 1283979692472077911529069)
        ·
          refine ⟨481492384677029216823401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1283979692472077911529069 481492384677029216823401)
          ·
            refine ⟨361119288507771912617551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481492384677029216823401 361119288507771912617551)
            ·
              refine ⟨541678932761657868926327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361119288507771912617551 541678932761657868926327)
              ·
                refine ⟨812518399142486803389491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541678932761657868926327 812518399142486803389491)
                ·
                  refine ⟨1218777598713730205084237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812518399142486803389491 1218777598713730205084237)
                  ·
                    refine ⟨457041599517648826906589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218777598713730205084237 457041599517648826906589)
                    ·
                      refine ⟨171390599819118310089971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457041599517648826906589 171390599819118310089971)
                      ·
                        rfl

theorem cell23_333782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_333782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333782 prefixEnd_333782 := by exact prefixLift 333782
  have htrace : WordTrace (prefixWord ++ tailWord_333782) baseStart_333782 baseEnd_333782 := by
    simpa [prefixWord, tailWord_333782, baseEnd_333782] using wordTrace_append hprefix tailTrace_333782
  have hstable : (prefixWord ++ tailWord_333782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333782).length < 2 ^ (prefixWord ++ tailWord_333782).sum := by decide
  have hdescent : baseEnd_333782 < baseStart_333782 := by decide
  rcases family_descends (prefixWord ++ tailWord_333782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333821 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_333821 : Nat := 118140960795 + 333821 * 2 ^ 59
def prefixEnd_333821 : Nat := 4983230072969 + 3 ^ 40 * 333821 * 2
def baseEnd_333821 : Nat := 171410625564643657502291

theorem tailTrace_333821 : CollatzResearch.WordTrace tailWord_333821 prefixEnd_333821 171410625564643657502291 := by
  unfold tailWord_333821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175452123631003932945317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8116968082420669288630211 12175452123631003932945317)
  ·
    refine ⟨2282897273180813237427247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12175452123631003932945317 2282897273180813237427247)
    ·
      refine ⟨3424345909771219856140871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282897273180813237427247 3424345909771219856140871)
      ·
        refine ⟨5136518864656829784211307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3424345909771219856140871 5136518864656829784211307)
        ·
          refine ⟨7704778296985244676316961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136518864656829784211307 7704778296985244676316961)
          ·
            refine ⟨5778583722738933507237721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704778296985244676316961 5778583722738933507237721)
            ·
              refine ⟨4333937792054200130428291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778583722738933507237721 4333937792054200130428291)
              ·
                refine ⟨6500906688081300195642437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333937792054200130428291 6500906688081300195642437)
                ·
                  refine ⟨1218920004015243786682957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6500906688081300195642437 1218920004015243786682957)
                  ·
                    refine ⟨457095001505716420006109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218920004015243786682957 457095001505716420006109)
                    ·
                      refine ⟨171410625564643657502291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457095001505716420006109 171410625564643657502291)
                      ·
                        rfl

theorem cell23_333821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_333821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333821 prefixEnd_333821 := by exact prefixLift 333821
  have htrace : WordTrace (prefixWord ++ tailWord_333821) baseStart_333821 baseEnd_333821 := by
    simpa [prefixWord, tailWord_333821, baseEnd_333821] using wordTrace_append hprefix tailTrace_333821
  have hstable : (prefixWord ++ tailWord_333821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333821).length < 2 ^ (prefixWord ++ tailWord_333821).sum := by decide
  have hdescent : baseEnd_333821 < baseStart_333821 := by decide
  rcases family_descends (prefixWord ++ tailWord_333821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333822 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_333822 : Nat := 118140960795 + 333822 * 2 ^ 59
def prefixEnd_333822 : Nat := 4983230072969 + 3 ^ 40 * 333822 * 2
def baseEnd_333822 : Nat := 171411139045298153589787

theorem tailTrace_333822 : CollatzResearch.WordTrace tailWord_333822 prefixEnd_333822 171411139045298153589787 := by
  unfold tailWord_333822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521936074578422637966465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8116992397751587402487813 1521936074578422637966465)
  ·
    refine ⟨1141452055933816978474849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1521936074578422637966465 1141452055933816978474849)
    ·
      refine ⟨856089041950362733856137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1141452055933816978474849 856089041950362733856137)
      ·
        refine ⟨642066781462772050392103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856089041950362733856137 642066781462772050392103)
        ·
          refine ⟨963100172194158075588155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642066781462772050392103 963100172194158075588155)
          ·
            refine ⟨1444650258291237113382233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963100172194158075588155 1444650258291237113382233)
            ·
              refine ⟨1083487693718427835036675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444650258291237113382233 1083487693718427835036675)
              ·
                refine ⟨1625231540577641752555013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083487693718427835036675 1625231540577641752555013)
                ·
                  refine ⟨304730913858307828604065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625231540577641752555013 304730913858307828604065)
                  ·
                    refine ⟨228548185393730871453049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304730913858307828604065 228548185393730871453049)
                    ·
                      refine ⟨171411139045298153589787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228548185393730871453049 171411139045298153589787)
                      ·
                        rfl

theorem cell23_333822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_333822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333822 prefixEnd_333822 := by exact prefixLift 333822
  have htrace : WordTrace (prefixWord ++ tailWord_333822) baseStart_333822 baseEnd_333822 := by
    simpa [prefixWord, tailWord_333822, baseEnd_333822] using wordTrace_append hprefix tailTrace_333822
  have hstable : (prefixWord ++ tailWord_333822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333822).length < 2 ^ (prefixWord ++ tailWord_333822).sum := by decide
  have hdescent : baseEnd_333822 < baseStart_333822 := by decide
  rcases family_descends (prefixWord ++ tailWord_333822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333824 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_333824 : Nat := 118140960795 + 333824 * 2 ^ 59
def prefixEnd_333824 : Nat := 4983230072969 + 3 ^ 40 * 333824 * 2
def baseEnd_333824 : Nat := 57137388668869048588259

theorem tailTrace_333824 : CollatzResearch.WordTrace tailWord_333824 prefixEnd_333824 57137388668869048588259 := by
  unfold tailWord_333824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087780771310067722652263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8117041028413423630203017 6087780771310067722652263)
  ·
    refine ⟨9131671156965101583978395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087780771310067722652263 9131671156965101583978395)
    ·
      refine ⟨13697506735447652375967593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9131671156965101583978395 13697506735447652375967593)
      ·
        refine ⟨10273130051585739281975695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13697506735447652375967593 10273130051585739281975695)
        ·
          refine ⟨15409695077378608922963543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10273130051585739281975695 15409695077378608922963543)
          ·
            refine ⟨23114542616067913384445315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15409695077378608922963543 23114542616067913384445315)
            ·
              refine ⟨34671813924101870076667973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23114542616067913384445315 34671813924101870076667973)
              ·
                refine ⟨6500965110769100639375245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34671813924101870076667973 6500965110769100639375245)
                ·
                  refine ⟨2437861916538412739765717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6500965110769100639375245 2437861916538412739765717)
                  ·
                    refine ⟨57137388668869048588259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2437861916538412739765717 57137388668869048588259)
                    ·
                      rfl

theorem cell23_333824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_333824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333824 prefixEnd_333824 := by exact prefixLift 333824
  have htrace : WordTrace (prefixWord ++ tailWord_333824) baseStart_333824 baseEnd_333824 := by
    simpa [prefixWord, tailWord_333824, baseEnd_333824] using wordTrace_append hprefix tailTrace_333824
  have hstable : (prefixWord ++ tailWord_333824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333824).length < 2 ^ (prefixWord ++ tailWord_333824).sum := by decide
  have hdescent : baseEnd_333824 < baseStart_333824 := by decide
  rcases family_descends (prefixWord ++ tailWord_333824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333858 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_333858 : Nat := 118140960795 + 333858 * 2 ^ 59
def prefixEnd_333858 : Nat := 4983230072969 + 3 ^ 40 * 333858 * 2
def baseEnd_333858 : Nat := 57143208116286670913207

theorem tailTrace_333858 : CollatzResearch.WordTrace tailWord_333858 prefixEnd_333858 57143208116286670913207 := by
  unfold tailWord_333858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044200406124239813010557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8117867749664639501361485 3044200406124239813010557)
  ·
    refine ⟨1141575152296589929878959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3044200406124239813010557 1141575152296589929878959)
    ·
      refine ⟨1712362728444884894818439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141575152296589929878959 1712362728444884894818439)
      ·
        refine ⟨2568544092667327342227659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712362728444884894818439 2568544092667327342227659)
        ·
          refine ⟨3852816139000991013341489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568544092667327342227659 3852816139000991013341489)
          ·
            refine ⟨2889612104250743260006117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3852816139000991013341489 2889612104250743260006117)
            ·
              refine ⟨541802269547014361251147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2889612104250743260006117 541802269547014361251147)
              ·
                refine ⟨812703404320521541876721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541802269547014361251147 812703404320521541876721)
                ·
                  refine ⟨609527553240391156407541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812703404320521541876721 609527553240391156407541)
                  ·
                    refine ⟨57143208116286670913207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609527553240391156407541 57143208116286670913207)
                    ·
                      rfl

theorem cell23_333858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_333858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333858 prefixEnd_333858 := by exact prefixLift 333858
  have htrace : WordTrace (prefixWord ++ tailWord_333858) baseStart_333858 baseEnd_333858 := by
    simpa [prefixWord, tailWord_333858, baseEnd_333858] using wordTrace_append hprefix tailTrace_333858
  have hstable : (prefixWord ++ tailWord_333858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333858).length < 2 ^ (prefixWord ++ tailWord_333858).sum := by decide
  have hdescent : baseEnd_333858 < baseStart_333858 := by decide
  rcases family_descends (prefixWord ++ tailWord_333858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333871 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 7, 4]
def baseStart_333871 : Nat := 118140960795 + 333871 * 2 ^ 59
def prefixEnd_333871 : Nat := 4983230072969 + 3 ^ 40 * 333871 * 2
def baseEnd_333871 : Nat := 57145433199122820625687

theorem tailTrace_333871 : CollatzResearch.WordTrace tailWord_333871 prefixEnd_333871 57145433199122820625687 := by
  unfold tailWord_333871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177275773449862472265467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8118183848966574981510311 12177275773449862472265467)
  ·
    refine ⟨18265913660174793708398201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12177275773449862472265467 18265913660174793708398201)
    ·
      refine ⟨13699435245131095281298651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18265913660174793708398201 13699435245131095281298651)
      ·
        refine ⟨20549152867696642921947977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13699435245131095281298651 20549152867696642921947977)
        ·
          refine ⟨15411864650772482191460983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20549152867696642921947977 15411864650772482191460983)
          ·
            refine ⟨23117796976158723287191475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15411864650772482191460983 23117796976158723287191475)
            ·
              refine ⟨34676695464238084930787213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23117796976158723287191475 34676695464238084930787213)
              ·
                refine ⟨13003760799089281849045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34676695464238084930787213 13003760799089281849045205)
                ·
                  refine ⟨304775643728655043336997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13003760799089281849045205 304775643728655043336997)
                  ·
                    refine ⟨57145433199122820625687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304775643728655043336997 57145433199122820625687)
                    ·
                      rfl

theorem cell23_333871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_333871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333871 prefixEnd_333871 := by exact prefixLift 333871
  have htrace : WordTrace (prefixWord ++ tailWord_333871) baseStart_333871 baseEnd_333871 := by
    simpa [prefixWord, tailWord_333871, baseEnd_333871] using wordTrace_append hprefix tailTrace_333871
  have hstable : (prefixWord ++ tailWord_333871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333871).length < 2 ^ (prefixWord ++ tailWord_333871).sum := by decide
  have hdescent : baseEnd_333871 < baseStart_333871 := by decide
  rcases family_descends (prefixWord ++ tailWord_333871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333945 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_333945 : Nat := 118140960795 + 333945 * 2 ^ 59
def prefixEnd_333945 : Nat := 4983230072969 + 3 ^ 40 * 333945 * 2
def baseEnd_333945 : Nat := 171474297165801172351721

theorem tailTrace_333945 : CollatzResearch.WordTrace tailWord_333945 prefixEnd_333945 171474297165801172351721 := by
  unfold tailWord_333945
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179974775181773110459289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8119983183454515406972859 12179974775181773110459289)
  ·
    refine ⟨9134981081386329832844467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12179974775181773110459289 9134981081386329832844467)
    ·
      refine ⟨13702471622079494749266701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134981081386329832844467 13702471622079494749266701)
      ·
        refine ⟨5138426858279810530975013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13702471622079494749266701 5138426858279810530975013)
        ·
          refine ⟨963455035927464474557815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5138426858279810530975013 963455035927464474557815)
          ·
            refine ⟨1445182553891196711836723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963455035927464474557815 1445182553891196711836723)
            ·
              refine ⟨2167773830836795067755085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445182553891196711836723 2167773830836795067755085)
              ·
                refine ⟨812915186563798150408157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167773830836795067755085 812915186563798150408157)
                ·
                  refine ⟨304843194961424306403059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812915186563798150408157 304843194961424306403059)
                  ·
                    refine ⟨457264792442136459604589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 304843194961424306403059 457264792442136459604589)
                    ·
                      refine ⟨171474297165801172351721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457264792442136459604589 171474297165801172351721)
                      ·
                        rfl

theorem cell23_333945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_333945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333945 prefixEnd_333945 := by exact prefixLift 333945
  have htrace : WordTrace (prefixWord ++ tailWord_333945) baseStart_333945 baseEnd_333945 := by
    simpa [prefixWord, tailWord_333945, baseEnd_333945] using wordTrace_append hprefix tailTrace_333945
  have hstable : (prefixWord ++ tailWord_333945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333945).length < 2 ^ (prefixWord ++ tailWord_333945).sum := by decide
  have hdescent : baseEnd_333945 < baseStart_333945 := by decide
  rcases family_descends (prefixWord ++ tailWord_333945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333968 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2]
def baseStart_333968 : Nat := 118140960795 + 333968 * 2 ^ 59
def prefixEnd_333968 : Nat := 4983230072969 + 3 ^ 40 * 333968 * 2
def baseEnd_333968 : Nat := 171486107220854582364115

theorem tailTrace_333968 : CollatzResearch.WordTrace tailWord_333968 prefixEnd_333968 171486107220854582364115 := by
  unfold tailWord_333968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090406827049224019273279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8120542436065632025697705 6090406827049224019273279)
  ·
    refine ⟨9135610240573836028909919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6090406827049224019273279 9135610240573836028909919)
    ·
      refine ⟨13703415360860754043364879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9135610240573836028909919 13703415360860754043364879)
      ·
        refine ⟨20555123041291131065047319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703415360860754043364879 20555123041291131065047319)
        ·
          refine ⟨30832684561936696597570979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20555123041291131065047319 30832684561936696597570979)
          ·
            refine ⟨46249026842905044896356469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30832684561936696597570979 46249026842905044896356469)
            ·
              refine ⟨4335846266522347959033419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46249026842905044896356469 4335846266522347959033419)
              ·
                refine ⟨6503769399783521938550129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335846266522347959033419 6503769399783521938550129)
                ·
                  refine ⟨4877827049837641453912597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6503769399783521938550129 4877827049837641453912597)
                  ·
                    refine ⟨228648142961139443152153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4877827049837641453912597 228648142961139443152153)
                    ·
                      refine ⟨171486107220854582364115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228648142961139443152153 171486107220854582364115)
                      ·
                        rfl

theorem cell23_333968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 6, 2].length) (baseStart_333968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333968 prefixEnd_333968 := by exact prefixLift 333968
  have htrace : WordTrace (prefixWord ++ tailWord_333968) baseStart_333968 baseEnd_333968 := by
    simpa [prefixWord, tailWord_333968, baseEnd_333968] using wordTrace_append hprefix tailTrace_333968
  have hstable : (prefixWord ++ tailWord_333968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333968).length < 2 ^ (prefixWord ++ tailWord_333968).sum := by decide
  have hdescent : baseEnd_333968 < baseStart_333968 := by decide
  rcases family_descends (prefixWord ++ tailWord_333968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333971 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_333971 : Nat := 118140960795 + 333971 * 2 ^ 59
def prefixEnd_333971 : Nat := 4983230072969 + 3 ^ 40 * 333971 * 2
def baseEnd_333971 : Nat := 171487647662818070626601

theorem tailTrace_333971 : CollatzResearch.WordTrace tailWord_333971 prefixEnd_333971 171487647662818070626601 := by
  unfold tailWord_333971
  simp only [CollatzResearch.WordTrace]
  refine ⟨12180923073087579550905767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8120615382058386367270511 12180923073087579550905767)
  ·
    refine ⟨18271384609631369326358651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12180923073087579550905767 18271384609631369326358651)
    ·
      refine ⟨27407076914447053989537977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18271384609631369326358651 27407076914447053989537977)
      ·
        refine ⟨20555307685835290492153483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27407076914447053989537977 20555307685835290492153483)
        ·
          refine ⟨30832961528752935738230225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20555307685835290492153483 30832961528752935738230225)
          ·
            refine ⟨23124721146564701803672669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30832961528752935738230225 23124721146564701803672669)
            ·
              refine ⟨8671770429961763176377251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23124721146564701803672669 8671770429961763176377251)
              ·
                refine ⟨13007655644942644764565877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671770429961763176377251 13007655644942644764565877)
                ·
                  refine ⟨1219467716713372946678051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13007655644942644764565877 1219467716713372946678051)
                  ·
                    refine ⟨1829201575070059420017077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219467716713372946678051 1829201575070059420017077)
                    ·
                      refine ⟨171487647662818070626601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1829201575070059420017077 171487647662818070626601)
                      ·
                        rfl

theorem cell23_333971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_333971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333971 prefixEnd_333971 := by exact prefixLift 333971
  have htrace : WordTrace (prefixWord ++ tailWord_333971) baseStart_333971 baseEnd_333971 := by
    simpa [prefixWord, tailWord_333971, baseEnd_333971] using wordTrace_append hprefix tailTrace_333971
  have hstable : (prefixWord ++ tailWord_333971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333971).length < 2 ^ (prefixWord ++ tailWord_333971).sum := by decide
  have hdescent : baseEnd_333971 < baseStart_333971 := by decide
  rcases family_descends (prefixWord ++ tailWord_333971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333985 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_333985 : Nat := 118140960795 + 333985 * 2 ^ 59
def prefixEnd_333985 : Nat := 4983230072969 + 3 ^ 40 * 333985 * 2
def baseEnd_333985 : Nat := 171494836391981015851537

theorem tailTrace_333985 : CollatzResearch.WordTrace tailWord_333985 prefixEnd_333985 171494836391981015851537 := by
  unfold tailWord_333985
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181433695036859941915409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8120955796691239961276939 12181433695036859941915409)
  ·
    refine ⟨9136075271277644956436557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12181433695036859941915409 9136075271277644956436557)
    ·
      refine ⟨3426028226729116858663709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9136075271277644956436557 3426028226729116858663709)
      ·
        refine ⟨1284760585023418821998891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3426028226729116858663709 1284760585023418821998891)
        ·
          refine ⟨1927140877535128232998337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284760585023418821998891 1927140877535128232998337)
          ·
            refine ⟨1445355658151346174748753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927140877535128232998337 1445355658151346174748753)
            ·
              refine ⟨1084016743613509631061565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445355658151346174748753 1084016743613509631061565)
              ·
                refine ⟨406506278855066111648087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084016743613509631061565 406506278855066111648087)
                ·
                  refine ⟨609759418282599167472131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406506278855066111648087 609759418282599167472131)
                  ·
                    refine ⟨914639127423898751208197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 609759418282599167472131 914639127423898751208197)
                    ·
                      refine ⟨171494836391981015851537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 914639127423898751208197 171494836391981015851537)
                      ·
                        rfl

theorem cell23_333985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_333985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_333985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_333985 prefixEnd_333985 := by exact prefixLift 333985
  have htrace : WordTrace (prefixWord ++ tailWord_333985) baseStart_333985 baseEnd_333985 := by
    simpa [prefixWord, tailWord_333985, baseEnd_333985] using wordTrace_append hprefix tailTrace_333985
  have hstable : (prefixWord ++ tailWord_333985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333985).length < 2 ^ (prefixWord ++ tailWord_333985).sum := by decide
  have hdescent : baseEnd_333985 < baseStart_333985 := by decide
  rcases family_descends (prefixWord ++ tailWord_333985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334011 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_334011 : Nat := 118140960795 + 334011 * 2 ^ 59
def prefixEnd_334011 : Nat := 4983230072969 + 3 ^ 40 * 334011 * 2
def baseEnd_334011 : Nat := 171508186888997914126417

theorem tailTrace_334011 : CollatzResearch.WordTrace tailWord_334011 prefixEnd_334011 171508186888997914126417 := by
  unfold tailWord_334011
  simp only [CollatzResearch.WordTrace]
  refine ⟨12182381992942666382361887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8121587995295110921574591 12182381992942666382361887)
  ·
    refine ⟨18273572989413999573542831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12182381992942666382361887 18273572989413999573542831)
    ·
      refine ⟨27410359484120999360314247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18273572989413999573542831 27410359484120999360314247)
      ·
        refine ⟨41115539226181499040471371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27410359484120999360314247 41115539226181499040471371)
        ·
          refine ⟨61673308839272248560707057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41115539226181499040471371 61673308839272248560707057)
          ·
            refine ⟨46254981629454186420530293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61673308839272248560707057 46254981629454186420530293)
            ·
              refine ⟨4336404527761329976924715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46254981629454186420530293 4336404527761329976924715)
              ·
                refine ⟨6504606791641994965387073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4336404527761329976924715 6504606791641994965387073)
                ·
                  refine ⟨4878455093731496224040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6504606791641994965387073 4878455093731496224040305)
                  ·
                    refine ⟨3658841320298622168030229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878455093731496224040305 3658841320298622168030229)
                    ·
                      refine ⟨171508186888997914126417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3658841320298622168030229 171508186888997914126417)
                      ·
                        rfl

theorem cell23_334011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_334011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334011 prefixEnd_334011 := by exact prefixLift 334011
  have htrace : WordTrace (prefixWord ++ tailWord_334011) baseStart_334011 baseEnd_334011 := by
    simpa [prefixWord, tailWord_334011, baseEnd_334011] using wordTrace_append hprefix tailTrace_334011
  have hstable : (prefixWord ++ tailWord_334011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334011).length < 2 ^ (prefixWord ++ tailWord_334011).sum := by decide
  have hdescent : baseEnd_334011 < baseStart_334011 := by decide
  rcases family_descends (prefixWord ++ tailWord_334011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334012 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_334012 : Nat := 118140960795 + 334012 * 2 ^ 59
def prefixEnd_334012 : Nat := 4983230072969 + 3 ^ 40 * 334012 * 2
def baseEnd_334012 : Nat := 57169566789884136737971

theorem tailTrace_334012 : CollatzResearch.WordTrace tailWord_334012 prefixEnd_334012 57169566789884136737971 := by
  unfold tailWord_334012
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091209232969521776574145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8121612310626029035432193 6091209232969521776574145)
  ·
    refine ⟨4568406924727141332430609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6091209232969521776574145 4568406924727141332430609)
    ·
      refine ⟨3426305193545355999322957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4568406924727141332430609 3426305193545355999322957)
      ·
        refine ⟨1284864447579508499746109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3426305193545355999322957 1284864447579508499746109)
        ·
          refine ⟨481824167842315687404791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284864447579508499746109 481824167842315687404791)
          ·
            refine ⟨722736251763473531107187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481824167842315687404791 722736251763473531107187)
            ·
              refine ⟨1084104377645210296660781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722736251763473531107187 1084104377645210296660781)
              ·
                refine ⟨406539141616953861247793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084104377645210296660781 406539141616953861247793)
                ·
                  refine ⟨304904356212715395935845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406539141616953861247793 304904356212715395935845)
                  ·
                    refine ⟨57169566789884136737971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 304904356212715395935845 57169566789884136737971)
                    ·
                      rfl

theorem cell23_334012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_334012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334012 prefixEnd_334012 := by exact prefixLift 334012
  have htrace : WordTrace (prefixWord ++ tailWord_334012) baseStart_334012 baseEnd_334012 := by
    simpa [prefixWord, tailWord_334012, baseEnd_334012] using wordTrace_append hprefix tailTrace_334012
  have hstable : (prefixWord ++ tailWord_334012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334012).length < 2 ^ (prefixWord ++ tailWord_334012).sum := by decide
  have hdescent : baseEnd_334012 < baseStart_334012 := by decide
  rcases family_descends (prefixWord ++ tailWord_334012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334053 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_334053 : Nat := 118140960795 + 334053 * 2 ^ 59
def prefixEnd_334053 : Nat := 4983230072969 + 3 ^ 40 * 334053 * 2
def baseEnd_334053 : Nat := 171529753076486749801225

theorem tailTrace_334053 : CollatzResearch.WordTrace tailWord_334053 prefixEnd_334053 171529753076486749801225 := by
  unfold tailWord_334053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183913858790507555390813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8122609239193671703593875 12183913858790507555390813)
  ·
    refine ⟨4568967697046440333271555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12183913858790507555390813 4568967697046440333271555)
    ·
      refine ⟨6853451545569660499907333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4568967697046440333271555 6853451545569660499907333)
      ·
        refine ⟨1285022164794311343732625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6853451545569660499907333 1285022164794311343732625)
        ·
          refine ⟨963766623595733507799469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285022164794311343732625 963766623595733507799469)
          ·
            refine ⟨361412483848400065424801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 963766623595733507799469 361412483848400065424801)
            ·
              refine ⟨271059362886300049068601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361412483848400065424801 271059362886300049068601)
              ·
                refine ⟨203294522164725036801451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271059362886300049068601 203294522164725036801451)
                ·
                  refine ⟨304941783247087555202177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203294522164725036801451 304941783247087555202177)
                  ·
                    refine ⟨228706337435315666401633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304941783247087555202177 228706337435315666401633)
                    ·
                      refine ⟨171529753076486749801225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228706337435315666401633 171529753076486749801225)
                      ·
                        rfl

theorem cell23_334053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_334053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334053 prefixEnd_334053 := by exact prefixLift 334053
  have htrace : WordTrace (prefixWord ++ tailWord_334053) baseStart_334053 baseEnd_334053 := by
    simpa [prefixWord, tailWord_334053, baseEnd_334053] using wordTrace_append hprefix tailTrace_334053
  have hstable : (prefixWord ++ tailWord_334053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334053).length < 2 ^ (prefixWord ++ tailWord_334053).sum := by decide
  have hdescent : baseEnd_334053 < baseStart_334053 := by decide
  rcases family_descends (prefixWord ++ tailWord_334053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334058 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_334058 : Nat := 118140960795 + 334058 * 2 ^ 59
def prefixEnd_334058 : Nat := 4983230072969 + 3 ^ 40 * 334058 * 2
def baseEnd_334058 : Nat := 171532320479759230238701

theorem tailTrace_334058 : CollatzResearch.WordTrace tailWord_334058 prefixEnd_334058 171532320479759230238701 := by
  unfold tailWord_334058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046024055943098352330707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8122730815848262272881885 3046024055943098352330707)
  ·
    refine ⟨4569036083914647528496061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046024055943098352330707 4569036083914647528496061)
    ·
      refine ⟨1713388531467992823186023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4569036083914647528496061 1713388531467992823186023)
      ·
        refine ⟨2570082797201989234779035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713388531467992823186023 2570082797201989234779035)
        ·
          refine ⟨3855124195802983852168553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570082797201989234779035 3855124195802983852168553)
          ·
            refine ⟨2891343146852237889126415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855124195802983852168553 2891343146852237889126415)
            ·
              refine ⟨4337014720278356833689623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891343146852237889126415 4337014720278356833689623)
              ·
                refine ⟨6505522080417535250534435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337014720278356833689623 6505522080417535250534435)
                ·
                  refine ⟨9758283120626302875801653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6505522080417535250534435 9758283120626302875801653)
                  ·
                    refine ⟨914839042558715894606405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9758283120626302875801653 914839042558715894606405)
                    ·
                      refine ⟨171532320479759230238701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 914839042558715894606405 171532320479759230238701)
                      ·
                        rfl

theorem cell23_334058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_334058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334058 prefixEnd_334058 := by exact prefixLift 334058
  have htrace : WordTrace (prefixWord ++ tailWord_334058) baseStart_334058 baseEnd_334058 := by
    simpa [prefixWord, tailWord_334058, baseEnd_334058] using wordTrace_append hprefix tailTrace_334058
  have hstable : (prefixWord ++ tailWord_334058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334058).length < 2 ^ (prefixWord ++ tailWord_334058).sum := by decide
  have hdescent : baseEnd_334058 < baseStart_334058 := by decide
  rcases family_descends (prefixWord ++ tailWord_334058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334092 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_334092 : Nat := 118140960795 + 334092 * 2 ^ 59
def prefixEnd_334092 : Nat := 4983230072969 + 3 ^ 40 * 334092 * 2
def baseEnd_334092 : Nat := 171549778822012097213545

theorem tailTrace_334092 : CollatzResearch.WordTrace tailWord_334092 prefixEnd_334092 171549778822012097213545 := by
  unfold tailWord_334092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092668152824608608030265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8123557537099478144040353 6092668152824608608030265)
  ·
    refine ⟨4569501114618456456022699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6092668152824608608030265 4569501114618456456022699)
    ·
      refine ⟨6854251671927684684034049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569501114618456456022699 6854251671927684684034049)
      ·
        refine ⟨5140688753945763513025537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6854251671927684684034049 5140688753945763513025537)
        ·
          refine ⟨3855516565459322634769153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5140688753945763513025537 3855516565459322634769153)
          ·
            refine ⟨2891637424094491976076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855516565459322634769153 2891637424094491976076865)
            ·
              refine ⟨2168728068070868982057649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891637424094491976076865 2168728068070868982057649)
              ·
                refine ⟨1626546051053151736543237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168728068070868982057649 1626546051053151736543237)
                ·
                  refine ⟨304977384572465950601857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626546051053151736543237 304977384572465950601857)
                  ·
                    refine ⟨228733038429349462951393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 304977384572465950601857 228733038429349462951393)
                    ·
                      refine ⟨171549778822012097213545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228733038429349462951393 171549778822012097213545)
                      ·
                        rfl

theorem cell23_334092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_334092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334092 prefixEnd_334092 := by exact prefixLift 334092
  have htrace : WordTrace (prefixWord ++ tailWord_334092) baseStart_334092 baseEnd_334092 := by
    simpa [prefixWord, tailWord_334092, baseEnd_334092] using wordTrace_append hprefix tailTrace_334092
  have hstable : (prefixWord ++ tailWord_334092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334092).length < 2 ^ (prefixWord ++ tailWord_334092).sum := by decide
  have hdescent : baseEnd_334092 < baseStart_334092 := by decide
  rcases family_descends (prefixWord ++ tailWord_334092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334115 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 5]
def baseStart_334115 : Nat := 118140960795 + 334115 * 2 ^ 59
def prefixEnd_334115 : Nat := 4983230072969 + 3 ^ 40 * 334115 * 2
def baseEnd_334115 : Nat := 19062398764118389691771

theorem tailTrace_334115 : CollatzResearch.WordTrace tailWord_334115 prefixEnd_334115 19062398764118389691771 := by
  unfold tailWord_334115
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186175184565892144147799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8124116789710594762765199 12186175184565892144147799)
  ·
    refine ⟨18279262776848838216221699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186175184565892144147799 18279262776848838216221699)
    ·
      refine ⟨27418894165273257324332549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279262776848838216221699 27418894165273257324332549)
      ·
        refine ⟨5141042655988735748312353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27418894165273257324332549 5141042655988735748312353)
        ·
          refine ⟨3855781991991551811234265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5141042655988735748312353 3855781991991551811234265)
          ·
            refine ⟨2891836493993663858425699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855781991991551811234265 2891836493993663858425699)
            ·
              refine ⟨4337754740990495787638549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891836493993663858425699 4337754740990495787638549)
              ·
                refine ⟨203332253483929490045557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4337754740990495787638549 203332253483929490045557)
                ·
                  refine ⟨19062398764118389691771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203332253483929490045557 19062398764118389691771)
                  ·
                    rfl

theorem cell23_334115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 5].length) (baseStart_334115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334115 prefixEnd_334115 := by exact prefixLift 334115
  have htrace : WordTrace (prefixWord ++ tailWord_334115) baseStart_334115 baseEnd_334115 := by
    simpa [prefixWord, tailWord_334115, baseEnd_334115] using wordTrace_append hprefix tailTrace_334115
  have hstable : (prefixWord ++ tailWord_334115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334115).length < 2 ^ (prefixWord ++ tailWord_334115).sum := by decide
  have hdescent : baseEnd_334115 < baseStart_334115 := by decide
  rcases family_descends (prefixWord ++ tailWord_334115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334128 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_334128 : Nat := 118140960795 + 334128 * 2 ^ 59
def prefixEnd_334128 : Nat := 4983230072969 + 3 ^ 40 * 334128 * 2
def baseEnd_334128 : Nat := 57189421375191318787793

theorem tailTrace_334128 : CollatzResearch.WordTrace tailWord_334128 prefixEnd_334128 57189421375191318787793 := by
  unfold tailWord_334128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093324666759397682185519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8124432889012530242914025 6093324666759397682185519)
  ·
    refine ⟨9139987000139096523278279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093324666759397682185519 9139987000139096523278279)
    ·
      refine ⟨13709980500208644784917419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139987000139096523278279 13709980500208644784917419)
      ·
        refine ⟨20564970750312967177376129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13709980500208644784917419 20564970750312967177376129)
        ·
          refine ⟨15423728062734725383032097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20564970750312967177376129 15423728062734725383032097)
          ·
            refine ⟨11567796047051044037274073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15423728062734725383032097 11567796047051044037274073)
            ·
              refine ⟨8675847035288283027955555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11567796047051044037274073 8675847035288283027955555)
              ·
                refine ⟨13013770552932424541933333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675847035288283027955555 13013770552932424541933333)
                ·
                  refine ⟨610020494668707400403125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13013770552932424541933333 610020494668707400403125)
                  ·
                    refine ⟨57189421375191318787793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 610020494668707400403125 57189421375191318787793)
                    ·
                      rfl

theorem cell23_334128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_334128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334128 prefixEnd_334128 := by exact prefixLift 334128
  have htrace : WordTrace (prefixWord ++ tailWord_334128) baseStart_334128 baseEnd_334128 := by
    simpa [prefixWord, tailWord_334128, baseEnd_334128] using wordTrace_append hprefix tailTrace_334128
  have hstable : (prefixWord ++ tailWord_334128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334128).length < 2 ^ (prefixWord ++ tailWord_334128).sum := by decide
  have hdescent : baseEnd_334128 < baseStart_334128 := by decide
  rcases family_descends (prefixWord ++ tailWord_334128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334135 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_334135 : Nat := 118140960795 + 334135 * 2 ^ 59
def prefixEnd_334135 : Nat := 4983230072969 + 3 ^ 40 * 334135 * 2
def baseEnd_334135 : Nat := 171571858490155428975847

theorem tailTrace_334135 : CollatzResearch.WordTrace tailWord_334135 prefixEnd_334135 171571858490155428975847 := by
  unfold tailWord_334135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186904644493435559875859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8124603096328957039917239 12186904644493435559875859)
  ·
    refine ⟨18280356966740153339813789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186904644493435559875859 18280356966740153339813789)
    ·
      refine ⟨6855133862527557502430171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18280356966740153339813789 6855133862527557502430171)
      ·
        refine ⟨10282700793791336253645257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6855133862527557502430171 10282700793791336253645257)
        ·
          refine ⟨7712025595343502190233943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10282700793791336253645257 7712025595343502190233943)
          ·
            refine ⟨11568038393015253285350915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7712025595343502190233943 11568038393015253285350915)
            ·
              refine ⟨17352057589522879928026373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11568038393015253285350915 17352057589522879928026373)
              ·
                refine ⟨3253510798035539986504945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17352057589522879928026373 3253510798035539986504945)
                ·
                  refine ⟨2440133098526654989878709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253510798035539986504945 2440133098526654989878709)
                  ·
                    refine ⟨228762477986873905301129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2440133098526654989878709 228762477986873905301129)
                    ·
                      refine ⟨171571858490155428975847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228762477986873905301129 171571858490155428975847)
                      ·
                        rfl

theorem cell23_334135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_334135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334135 prefixEnd_334135 := by exact prefixLift 334135
  have htrace : WordTrace (prefixWord ++ tailWord_334135) baseStart_334135 baseEnd_334135 := by
    simpa [prefixWord, tailWord_334135, baseEnd_334135] using wordTrace_append hprefix tailTrace_334135
  have hstable : (prefixWord ++ tailWord_334135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334135).length < 2 ^ (prefixWord ++ tailWord_334135).sum := by decide
  have hdescent : baseEnd_334135 < baseStart_334135 := by decide
  rcases family_descends (prefixWord ++ tailWord_334135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334168 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_334168 : Nat := 118140960795 + 334168 * 2 ^ 59
def prefixEnd_334168 : Nat := 4983230072969 + 3 ^ 40 * 334168 * 2
def baseEnd_334168 : Nat := 171588803351753799863195

theorem tailTrace_334168 : CollatzResearch.WordTrace tailWord_334168 prefixEnd_334168 171588803351753799863195 := by
  unfold tailWord_334168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094054126686941097913579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8125405502249254797218105 6094054126686941097913579)
  ·
    refine ⟨9141081190030411646870369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094054126686941097913579 9141081190030411646870369)
    ·
      refine ⟨6855810892522808735152777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9141081190030411646870369 6855810892522808735152777)
      ·
        refine ⟨5141858169392106551364583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6855810892522808735152777 5141858169392106551364583)
        ·
          refine ⟨7712787254088159827046875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141858169392106551364583 7712787254088159827046875)
          ·
            refine ⟨11569180881132239740570313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7712787254088159827046875 11569180881132239740570313)
            ·
              refine ⟨8676885660849179805427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569180881132239740570313 8676885660849179805427735)
              ·
                refine ⟨13015328491273769708141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8676885660849179805427735 13015328491273769708141603)
                ·
                  refine ⟨19522992736910654562212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13015328491273769708141603 19522992736910654562212405)
                  ·
                    refine ⟨1830280569085373865207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19522992736910654562212405 1830280569085373865207413)
                    ·
                      refine ⟨171588803351753799863195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1830280569085373865207413 171588803351753799863195)
                      ·
                        rfl

theorem cell23_334168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_334168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334168 prefixEnd_334168 := by exact prefixLift 334168
  have htrace : WordTrace (prefixWord ++ tailWord_334168) baseStart_334168 baseEnd_334168 := by
    simpa [prefixWord, tailWord_334168, baseEnd_334168] using wordTrace_append hprefix tailTrace_334168
  have hstable : (prefixWord ++ tailWord_334168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334168).length < 2 ^ (prefixWord ++ tailWord_334168).sum := by decide
  have hdescent : baseEnd_334168 < baseStart_334168 := by decide
  rcases family_descends (prefixWord ++ tailWord_334168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334185 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_334185 : Nat := 118140960795 + 334185 * 2 ^ 59
def prefixEnd_334185 : Nat := 4983230072969 + 3 ^ 40 * 334185 * 2
def baseEnd_334185 : Nat := 171597532522880233350617

theorem tailTrace_334185 : CollatzResearch.WordTrace tailWord_334185 prefixEnd_334185 171597532522880233350617 := by
  unfold tailWord_334185
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188728294312294099196009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8125818862874862732797339 12188728294312294099196009)
  ·
    refine ⟨9141546220734220574397007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12188728294312294099196009 9141546220734220574397007)
    ·
      refine ⟨13712319331101330861595511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9141546220734220574397007 13712319331101330861595511)
      ·
        refine ⟨20568478996651996292393267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13712319331101330861595511 20568478996651996292393267)
        ·
          refine ⟨30852718494977994438589901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20568478996651996292393267 30852718494977994438589901)
          ·
            refine ⟨11569769435616747914471213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30852718494977994438589901 11569769435616747914471213)
            ·
              refine ⟨4338663538356280467926705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11569769435616747914471213 4338663538356280467926705)
              ·
                refine ⟨3253997653767210350945029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338663538356280467926705 3253997653767210350945029)
                ·
                  refine ⟨610124560081351940802193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3253997653767210350945029 610124560081351940802193)
                  ·
                    refine ⟨457593420061013955601645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610124560081351940802193 457593420061013955601645)
                    ·
                      refine ⟨171597532522880233350617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457593420061013955601645 171597532522880233350617)
                      ·
                        rfl

theorem cell23_334185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_334185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334185 prefixEnd_334185 := by exact prefixLift 334185
  have htrace : WordTrace (prefixWord ++ tailWord_334185) baseStart_334185 baseEnd_334185 := by
    simpa [prefixWord, tailWord_334185, baseEnd_334185] using wordTrace_append hprefix tailTrace_334185
  have hstable : (prefixWord ++ tailWord_334185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334185).length < 2 ^ (prefixWord ++ tailWord_334185).sum := by decide
  have hdescent : baseEnd_334185 < baseStart_334185 := by decide
  rcases family_descends (prefixWord ++ tailWord_334185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334208 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_334208 : Nat := 118140960795 + 334208 * 2 ^ 59
def prefixEnd_334208 : Nat := 4983230072969 + 3 ^ 40 * 334208 * 2
def baseEnd_334208 : Nat := 171609342577933643363011

theorem tailTrace_334208 : CollatzResearch.WordTrace tailWord_334208 prefixEnd_334208 171609342577933643363011 := by
  unfold tailWord_334208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094783586614484513641639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8126378115485979351522185 6094783586614484513641639)
  ·
    refine ⟨9142175379921726770462459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6094783586614484513641639 9142175379921726770462459)
    ·
      refine ⟨13713263069882590155693689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9142175379921726770462459 13713263069882590155693689)
      ·
        refine ⟨10284947302411942616770267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13713263069882590155693689 10284947302411942616770267)
        ·
          refine ⟨15427420953617913925155401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10284947302411942616770267 15427420953617913925155401)
          ·
            refine ⟨11570565715213435443866551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15427420953617913925155401 11570565715213435443866551)
            ·
              refine ⟨17355848572820153165799827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570565715213435443866551 17355848572820153165799827)
              ·
                refine ⟨26033772859230229748699741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17355848572820153165799827 26033772859230229748699741)
                ·
                  refine ⟨9762664822211336155762403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26033772859230229748699741 9762664822211336155762403)
                  ·
                    refine ⟨14643997233317004233643605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9762664822211336155762403 14643997233317004233643605)
                    ·
                      refine ⟨171609342577933643363011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 14643997233317004233643605 171609342577933643363011)
                      ·
                        rfl

theorem cell23_334208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_334208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334208 prefixEnd_334208 := by exact prefixLift 334208
  have htrace : WordTrace (prefixWord ++ tailWord_334208) baseStart_334208 baseEnd_334208 := by
    simpa [prefixWord, tailWord_334208, baseEnd_334208] using wordTrace_append hprefix tailTrace_334208
  have hstable : (prefixWord ++ tailWord_334208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334208).length < 2 ^ (prefixWord ++ tailWord_334208).sum := by decide
  have hdescent : baseEnd_334208 < baseStart_334208 := by decide
  rcases family_descends (prefixWord ++ tailWord_334208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334222 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_334222 : Nat := 118140960795 + 334222 * 2 ^ 59
def prefixEnd_334222 : Nat := 4983230072969 + 3 ^ 40 * 334222 * 2
def baseEnd_334222 : Nat := 19068503478566287620883

theorem tailTrace_334222 : CollatzResearch.WordTrace tailWord_334222 prefixEnd_334222 19068503478566287620883 := by
  unfold tailWord_334222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523759724397281177286615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8126718530118832945528613 1523759724397281177286615)
  ·
    refine ⟨2285639586595921765929923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1523759724397281177286615 2285639586595921765929923)
    ·
      refine ⟨3428459379893882648894885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285639586595921765929923 3428459379893882648894885)
      ·
        refine ⟨642836133730102996667791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3428459379893882648894885 642836133730102996667791)
        ·
          refine ⟨964254200595154495001687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642836133730102996667791 964254200595154495001687)
          ·
            refine ⟨1446381300892731742502531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964254200595154495001687 1446381300892731742502531)
            ·
              refine ⟨2169571951339097613753797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446381300892731742502531 2169571951339097613753797)
              ·
                refine ⟨406794740876080802578837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2169571951339097613753797 406794740876080802578837)
                ·
                  refine ⟨19068503478566287620883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 406794740876080802578837 19068503478566287620883)
                  ·
                    rfl

theorem cell23_334222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_334222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334222 prefixEnd_334222 := by exact prefixLift 334222
  have htrace : WordTrace (prefixWord ++ tailWord_334222) baseStart_334222 baseEnd_334222 := by
    simpa [prefixWord, tailWord_334222, baseEnd_334222] using wordTrace_append hprefix tailTrace_334222
  have hstable : (prefixWord ++ tailWord_334222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334222).length < 2 ^ (prefixWord ++ tailWord_334222).sum := by decide
  have hdescent : baseEnd_334222 < baseStart_334222 := by decide
  rcases family_descends (prefixWord ++ tailWord_334222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334250 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_334250 : Nat := 118140960795 + 334250 * 2 ^ 59
def prefixEnd_334250 : Nat := 4983230072969 + 3 ^ 40 * 334250 * 2
def baseEnd_334250 : Nat := 171630908765422479037819

theorem tailTrace_334250 : CollatzResearch.WordTrace tailWord_334250 prefixEnd_334250 171630908765422479037819 := by
  unfold tailWord_334250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047774759769202550078051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8127399359384540133541469 3047774759769202550078051)
  ·
    refine ⟨4571662139653803825117077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3047774759769202550078051 4571662139653803825117077)
    ·
      refine ⟨214296662796272054302363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4571662139653803825117077 214296662796272054302363)
      ·
        refine ⟨321444994194408081453545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214296662796272054302363 321444994194408081453545)
        ·
          refine ⟨241083745645806061090159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321444994194408081453545 241083745645806061090159)
          ·
            refine ⟨361625618468709091635239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241083745645806061090159 361625618468709091635239)
            ·
              refine ⟨542438427703063637452859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361625618468709091635239 542438427703063637452859)
              ·
                refine ⟨813657641554595456179289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542438427703063637452859 813657641554595456179289)
                ·
                  refine ⟨610243231165946592134467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813657641554595456179289 610243231165946592134467)
                  ·
                    refine ⟨915364846748919888201701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610243231165946592134467 915364846748919888201701)
                    ·
                      refine ⟨171630908765422479037819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 915364846748919888201701 171630908765422479037819)
                      ·
                        rfl

theorem cell23_334250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_334250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334250 prefixEnd_334250 := by exact prefixLift 334250
  have htrace : WordTrace (prefixWord ++ tailWord_334250) baseStart_334250 baseEnd_334250 := by
    simpa [prefixWord, tailWord_334250, baseEnd_334250] using wordTrace_append hprefix tailTrace_334250
  have hstable : (prefixWord ++ tailWord_334250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334250).length < 2 ^ (prefixWord ++ tailWord_334250).sum := by decide
  have hdescent : baseEnd_334250 < baseStart_334250 := by decide
  rcases family_descends (prefixWord ++ tailWord_334250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334253 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_334253 : Nat := 118140960795 + 334253 * 2 ^ 59
def prefixEnd_334253 : Nat := 4983230072969 + 3 ^ 40 * 334253 * 2
def baseEnd_334253 : Nat := 171632449207385967300305

theorem tailTrace_334253 : CollatzResearch.WordTrace tailWord_334253 prefixEnd_334253 171632449207385967300305 := by
  unfold tailWord_334253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191208458065941712671413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8127472305377294475114275 12191208458065941712671413)
  ·
    refine ⟨1142925792943682035562945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12191208458065941712671413 1142925792943682035562945)
    ·
      refine ⟨857194344707761526672209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1142925792943682035562945 857194344707761526672209)
      ·
        refine ⟨642895758530821145004157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857194344707761526672209 642895758530821145004157)
        ·
          refine ⟨241085909449057929376559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642895758530821145004157 241085909449057929376559)
          ·
            refine ⟨361628864173586894064839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241085909449057929376559 361628864173586894064839)
            ·
              refine ⟨542443296260380341097259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361628864173586894064839 542443296260380341097259)
              ·
                refine ⟨813664944390570511645889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542443296260380341097259 813664944390570511645889)
                ·
                  refine ⟨610248708292927883734417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813664944390570511645889 610248708292927883734417)
                  ·
                    refine ⟨457686531219695912800813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610248708292927883734417 457686531219695912800813)
                    ·
                      refine ⟨171632449207385967300305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457686531219695912800813 171632449207385967300305)
                      ·
                        rfl

theorem cell23_334253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_334253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334253 prefixEnd_334253 := by exact prefixLift 334253
  have htrace : WordTrace (prefixWord ++ tailWord_334253) baseStart_334253 baseEnd_334253 := by
    simpa [prefixWord, tailWord_334253, baseEnd_334253] using wordTrace_append hprefix tailTrace_334253
  have hstable : (prefixWord ++ tailWord_334253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334253).length < 2 ^ (prefixWord ++ tailWord_334253).sum := by decide
  have hdescent : baseEnd_334253 < baseStart_334253 := by decide
  rcases family_descends (prefixWord ++ tailWord_334253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334260 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_334260 : Nat := 118140960795 + 334260 * 2 ^ 59
def prefixEnd_334260 : Nat := 4983230072969 + 3 ^ 40 * 334260 * 2
def baseEnd_334260 : Nat := 57212014523989146637591

theorem tailTrace_334260 : CollatzResearch.WordTrace tailWord_334260 prefixEnd_334260 57212014523989146637591 := by
  unfold tailWord_334260
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095731884520290954088117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8127642512693721272117489 6095731884520290954088117)
  ·
    refine ⟨571474864173777276945761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6095731884520290954088117 571474864173777276945761)
    ·
      refine ⟨428606148130332957709321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 571474864173777276945761 428606148130332957709321)
      ·
        refine ⟨321454611097749718281991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428606148130332957709321 321454611097749718281991)
        ·
          refine ⟨482181916646624577422987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321454611097749718281991 482181916646624577422987)
          ·
            refine ⟨723272874969936866134481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482181916646624577422987 723272874969936866134481)
            ·
              refine ⟨542454656227452649600861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723272874969936866134481 542454656227452649600861)
              ·
                refine ⟨203420496085294743600323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542454656227452649600861 203420496085294743600323)
                ·
                  refine ⟨305130744127942115400485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203420496085294743600323 305130744127942115400485)
                  ·
                    refine ⟨57212014523989146637591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305130744127942115400485 57212014523989146637591)
                    ·
                      rfl

theorem cell23_334260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_334260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334260 prefixEnd_334260 := by exact prefixLift 334260
  have htrace : WordTrace (prefixWord ++ tailWord_334260) baseStart_334260 baseEnd_334260 := by
    simpa [prefixWord, tailWord_334260, baseEnd_334260] using wordTrace_append hprefix tailTrace_334260
  have hstable : (prefixWord ++ tailWord_334260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334260).length < 2 ^ (prefixWord ++ tailWord_334260).sum := by decide
  have hdescent : baseEnd_334260 < baseStart_334260 := by decide
  rcases family_descends (prefixWord ++ tailWord_334260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334269 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_334269 : Nat := 118140960795 + 334269 * 2 ^ 59
def prefixEnd_334269 : Nat := 4983230072969 + 3 ^ 40 * 334269 * 2
def baseEnd_334269 : Nat := 57213554965952634900077

theorem tailTrace_334269 : CollatzResearch.WordTrace tailWord_334269 prefixEnd_334269 57213554965952634900077 := by
  unfold tailWord_334269
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191792026007976445253861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8127861350671984296835907 12191792026007976445253861)
  ·
    refine ⟨2285961004876495583485099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12191792026007976445253861 2285961004876495583485099)
    ·
      refine ⟨3428941507314743375227649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285961004876495583485099 3428941507314743375227649)
      ·
        refine ⟨2571706130486057531420737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3428941507314743375227649 2571706130486057531420737)
        ·
          refine ⟨1928779597864543148565553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2571706130486057531420737 1928779597864543148565553)
          ·
            refine ⟨1446584698398407361424165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928779597864543148565553 1446584698398407361424165)
            ·
              refine ⟨271234630949701380267031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1446584698398407361424165 271234630949701380267031)
              ·
                refine ⟨406851946424552070400547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271234630949701380267031 406851946424552070400547)
                ·
                  refine ⟨610277919636828105600821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406851946424552070400547 610277919636828105600821)
                  ·
                    refine ⟨57213554965952634900077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 610277919636828105600821 57213554965952634900077)
                    ·
                      rfl

theorem cell23_334269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_334269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334269 prefixEnd_334269 := by exact prefixLift 334269
  have htrace : WordTrace (prefixWord ++ tailWord_334269) baseStart_334269 baseEnd_334269 := by
    simpa [prefixWord, tailWord_334269, baseEnd_334269] using wordTrace_append hprefix tailTrace_334269
  have hstable : (prefixWord ++ tailWord_334269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334269).length < 2 ^ (prefixWord ++ tailWord_334269).sum := by decide
  have hdescent : baseEnd_334269 < baseStart_334269 := by decide
  rcases family_descends (prefixWord ++ tailWord_334269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334273 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 6]
def baseStart_334273 : Nat := 118140960795 + 334273 * 2 ^ 59
def prefixEnd_334273 : Nat := 4983230072969 + 3 ^ 40 * 334273 * 2
def baseEnd_334273 : Nat := 19071413202275098783357

theorem tailTrace_334273 : CollatzResearch.WordTrace tailWord_334273 prefixEnd_334273 19071413202275098783357 := by
  unfold tailWord_334273
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191937917993485128399473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8127958611995656752266315 12191937917993485128399473)
  ·
    refine ⟨9143953438495113846299605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12191937917993485128399473 9143953438495113846299605)
    ·
      refine ⟨214311408714729230772647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9143953438495113846299605 214311408714729230772647)
      ·
        refine ⟨321467113072093846158971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214311408714729230772647 321467113072093846158971)
        ·
          refine ⟨482200669608140769238457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321467113072093846158971 482200669608140769238457)
          ·
            refine ⟨361650502206105576928843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482200669608140769238457 361650502206105576928843)
            ·
              refine ⟨542475753309158365393265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361650502206105576928843 542475753309158365393265)
              ·
                refine ⟨406856814981868774044949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542475753309158365393265 406856814981868774044949)
                ·
                  refine ⟨19071413202275098783357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 406856814981868774044949 19071413202275098783357)
                  ·
                    rfl

theorem cell23_334273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 6].length) (baseStart_334273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334273 prefixEnd_334273 := by exact prefixLift 334273
  have htrace : WordTrace (prefixWord ++ tailWord_334273) baseStart_334273 baseEnd_334273 := by
    simpa [prefixWord, tailWord_334273, baseEnd_334273] using wordTrace_append hprefix tailTrace_334273
  have hstable : (prefixWord ++ tailWord_334273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334273).length < 2 ^ (prefixWord ++ tailWord_334273).sum := by decide
  have hdescent : baseEnd_334273 < baseStart_334273 := by decide
  rcases family_descends (prefixWord ++ tailWord_334273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334275 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_334275 : Nat := 118140960795 + 334275 * 2 ^ 59
def prefixEnd_334275 : Nat := 4983230072969 + 3 ^ 40 * 334275 * 2
def baseEnd_334275 : Nat := 171643745781784881225203

theorem tailTrace_334275 : CollatzResearch.WordTrace tailWord_334275 prefixEnd_334275 171643745781784881225203 := by
  unfold tailWord_334275
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192010863986239469972279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8128007242657492979981519 12192010863986239469972279)
  ·
    refine ⟨18288016295979359204958419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12192010863986239469972279 18288016295979359204958419)
    ·
      refine ⟨27432024443969038807437629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18288016295979359204958419 27432024443969038807437629)
      ·
        refine ⟨10287009166488389552789111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27432024443969038807437629 10287009166488389552789111)
        ·
          refine ⟨15430513749732584329183667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10287009166488389552789111 15430513749732584329183667)
          ·
            refine ⟨23145770624598876493775501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430513749732584329183667 23145770624598876493775501)
            ·
              refine ⟨8679663984224578685165813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23145770624598876493775501 8679663984224578685165813)
              ·
                refine ⟨813718498521054251734295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8679663984224578685165813 813718498521054251734295)
                ·
                  refine ⟨1220577747781581377601443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813718498521054251734295 1220577747781581377601443)
                  ·
                    refine ⟨1830866621672372066402165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220577747781581377601443 1830866621672372066402165)
                    ·
                      refine ⟨171643745781784881225203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1830866621672372066402165 171643745781784881225203)
                      ·
                        rfl

theorem cell23_334275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_334275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334275 prefixEnd_334275 := by exact prefixLift 334275
  have htrace : WordTrace (prefixWord ++ tailWord_334275) baseStart_334275 baseEnd_334275 := by
    simpa [prefixWord, tailWord_334275, baseEnd_334275] using wordTrace_append hprefix tailTrace_334275
  have hstable : (prefixWord ++ tailWord_334275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334275).length < 2 ^ (prefixWord ++ tailWord_334275).sum := by decide
  have hdescent : baseEnd_334275 < baseStart_334275 := by decide
  rcases family_descends (prefixWord ++ tailWord_334275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334282 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_334282 : Nat := 118140960795 + 334282 * 2 ^ 59
def prefixEnd_334282 : Nat := 4983230072969 + 3 ^ 40 * 334282 * 2
def baseEnd_334282 : Nat := 57215780048788784612557

theorem tailTrace_334282 : CollatzResearch.WordTrace tailWord_334282 prefixEnd_334282 57215780048788784612557 := by
  unfold tailWord_334282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048066543740219916369275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8128177449973919776984733 3048066543740219916369275)
  ·
    refine ⟨4572099815610329874553913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048066543740219916369275 4572099815610329874553913)
    ·
      refine ⟨3429074861707747405915435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4572099815610329874553913 3429074861707747405915435)
      ·
        refine ⟨5143612292561621108873153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429074861707747405915435 5143612292561621108873153)
        ·
          refine ⟨3857709219421215831654865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143612292561621108873153 3857709219421215831654865)
          ·
            refine ⟨2893281914565911873741149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857709219421215831654865 2893281914565911873741149)
            ·
              refine ⟨1084980717962216952652931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893281914565911873741149 1084980717962216952652931)
              ·
                refine ⟨1627471076943325428979397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084980717962216952652931 1627471076943325428979397)
                ·
                  refine ⟨305150826926873517933637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627471076943325428979397 305150826926873517933637)
                  ·
                    refine ⟨57215780048788784612557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305150826926873517933637 57215780048788784612557)
                    ·
                      rfl

theorem cell23_334282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_334282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334282 prefixEnd_334282 := by exact prefixLift 334282
  have htrace : WordTrace (prefixWord ++ tailWord_334282) baseStart_334282 baseEnd_334282 := by
    simpa [prefixWord, tailWord_334282, baseEnd_334282] using wordTrace_append hprefix tailTrace_334282
  have hstable : (prefixWord ++ tailWord_334282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334282).length < 2 ^ (prefixWord ++ tailWord_334282).sum := by decide
  have hdescent : baseEnd_334282 < baseStart_334282 := by decide
  rcases family_descends (prefixWord ++ tailWord_334282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334292 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_334292 : Nat := 118140960795 + 334292 * 2 ^ 59
def prefixEnd_334292 : Nat := 4983230072969 + 3 ^ 40 * 334292 * 2
def baseEnd_334292 : Nat := 171652474952911314712625

theorem tailTrace_334292 : CollatzResearch.WordTrace tailWord_334292 prefixEnd_334292 171652474952911314712625 := by
  unfold tailWord_334292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096315452462325686670565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8128420603283100915560753 6096315452462325686670565)
  ·
    refine ⟨1143059147336686066250731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6096315452462325686670565 1143059147336686066250731)
    ·
      refine ⟨1714588721005029099376097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143059147336686066250731 1714588721005029099376097)
      ·
        refine ⟨1285941540753771824532073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1714588721005029099376097 1285941540753771824532073)
        ·
          refine ⟨964456155565328868399055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285941540753771824532073 964456155565328868399055)
          ·
            refine ⟨1446684233347993302598583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964456155565328868399055 1446684233347993302598583)
            ·
              refine ⟨2170026350021989953897875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446684233347993302598583 2170026350021989953897875)
              ·
                refine ⟨3255039525032984930846813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170026350021989953897875 3255039525032984930846813)
                ·
                  refine ⟨1220639821887369349067555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3255039525032984930846813 1220639821887369349067555)
                  ·
                    refine ⟨1830959732831054023601333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220639821887369349067555 1830959732831054023601333)
                    ·
                      refine ⟨171652474952911314712625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1830959732831054023601333 171652474952911314712625)
                      ·
                        rfl

theorem cell23_334292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_334292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334292 prefixEnd_334292 := by exact prefixLift 334292
  have htrace : WordTrace (prefixWord ++ tailWord_334292) baseStart_334292 baseEnd_334292 := by
    simpa [prefixWord, tailWord_334292, baseEnd_334292] using wordTrace_append hprefix tailTrace_334292
  have hstable : (prefixWord ++ tailWord_334292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334292).length < 2 ^ (prefixWord ++ tailWord_334292).sum := by decide
  have hdescent : baseEnd_334292 < baseStart_334292 := by decide
  rcases family_descends (prefixWord ++ tailWord_334292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334312 : List Nat := [2, 1, 4, 1, 1, 3, 4, 7]
def baseStart_334312 : Nat := 118140960795 + 334312 * 2 ^ 59
def prefixEnd_334312 : Nat := 4983230072969 + 3 ^ 40 * 334312 * 2
def baseEnd_334312 : Nat := 6357879428370416165279

theorem tailTrace_334312 : CollatzResearch.WordTrace tailWord_334312 prefixEnd_334312 6357879428370416165279 := by
  unfold tailWord_334312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096680182426097394534595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8128906909901463192712793 6096680182426097394534595)
  ·
    refine ⟨9145020273639146091801893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096680182426097394534595 9145020273639146091801893)
    ·
      refine ⟨1714691301307339892212855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9145020273639146091801893 1714691301307339892212855)
      ·
        refine ⟨2572036951961009838319283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714691301307339892212855 2572036951961009838319283)
        ·
          refine ⟨3858055427941514757478925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572036951961009838319283 3858055427941514757478925)
          ·
            refine ⟨1446770785478068034054597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3858055427941514757478925 1446770785478068034054597)
            ·
              refine ⟨271269522277137756385237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1446770785478068034054597 271269522277137756385237)
              ·
                refine ⟨6357879428370416165279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 271269522277137756385237 6357879428370416165279)
                ·
                  rfl

theorem cell23_334312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 7].length) (baseStart_334312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334312 prefixEnd_334312 := by exact prefixLift 334312
  have htrace : WordTrace (prefixWord ++ tailWord_334312) baseStart_334312 baseEnd_334312 := by
    simpa [prefixWord, tailWord_334312, baseEnd_334312] using wordTrace_append hprefix tailTrace_334312
  have hstable : (prefixWord ++ tailWord_334312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334312).length < 2 ^ (prefixWord ++ tailWord_334312).sum := by decide
  have hdescent : baseEnd_334312 < baseStart_334312 := by decide
  rcases family_descends (prefixWord ++ tailWord_334312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334335 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_334335 : Nat := 118140960795 + 334335 * 2 ^ 59
def prefixEnd_334335 : Nat := 4983230072969 + 3 ^ 40 * 334335 * 2
def baseEnd_334335 : Nat := 171674554621054646474927

theorem tailTrace_334335 : CollatzResearch.WordTrace tailWord_334335 prefixEnd_334335 171674554621054646474927 := by
  unfold tailWord_334335
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194199243768869717156459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8129466162512579811437639 12194199243768869717156459)
  ·
    refine ⟨18291298865653304575734689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194199243768869717156459 18291298865653304575734689)
    ·
      refine ⟨13718474149239978431801017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18291298865653304575734689 13718474149239978431801017)
      ·
        refine ⟨10288855611929983823850763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13718474149239978431801017 10288855611929983823850763)
        ·
          refine ⟨15433283417894975735776145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10288855611929983823850763 15433283417894975735776145)
          ·
            refine ⟨11574962563421231801832109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15433283417894975735776145 11574962563421231801832109)
            ·
              refine ⟨4340610961282961925687041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11574962563421231801832109 4340610961282961925687041)
              ·
                refine ⟨3255458220962221444265281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340610961282961925687041 3255458220962221444265281)
                ·
                  refine ⟨2441593665721666083198961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3255458220962221444265281 2441593665721666083198961)
                  ·
                    refine ⟨1831195249291249562399221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441593665721666083198961 1831195249291249562399221)
                    ·
                      refine ⟨171674554621054646474927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1831195249291249562399221 171674554621054646474927)
                      ·
                        rfl

theorem cell23_334335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_334335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334335 prefixEnd_334335 := by exact prefixLift 334335
  have htrace : WordTrace (prefixWord ++ tailWord_334335) baseStart_334335 baseEnd_334335 := by
    simpa [prefixWord, tailWord_334335, baseEnd_334335] using wordTrace_append hprefix tailTrace_334335
  have hstable : (prefixWord ++ tailWord_334335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334335).length < 2 ^ (prefixWord ++ tailWord_334335).sum := by decide
  have hdescent : baseEnd_334335 < baseStart_334335 := by decide
  rcases family_descends (prefixWord ++ tailWord_334335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334339 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 3]
def baseStart_334339 : Nat := 118140960795 + 334339 * 2 ^ 59
def prefixEnd_334339 : Nat := 4983230072969 + 3 ^ 40 * 334339 * 2
def baseEnd_334339 : Nat := 171676608543672630824909

theorem tailTrace_334339 : CollatzResearch.WordTrace tailWord_334339 prefixEnd_334339 171676608543672630824909 := by
  unfold tailWord_334339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194345135754378400302071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8129563423836252266868047 12194345135754378400302071)
  ·
    refine ⟨18291517703631567600453107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194345135754378400302071 18291517703631567600453107)
    ·
      refine ⟨27437276555447351400679661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291517703631567600453107 27437276555447351400679661)
      ·
        refine ⟨10288978708292756775254873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27437276555447351400679661 10288978708292756775254873)
        ·
          refine ⟨7716734031219567581441155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10288978708292756775254873 7716734031219567581441155)
          ·
            refine ⟨11575101046829351372161733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716734031219567581441155 11575101046829351372161733)
            ·
              refine ⟨2170331446280503382280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11575101046829351372161733 2170331446280503382280325)
              ·
                refine ⟨406937146177594384177561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2170331446280503382280325 406937146177594384177561)
                ·
                  refine ⟨305202859633195788133171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 406937146177594384177561 305202859633195788133171)
                  ·
                    refine ⟨457804289449793682199757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305202859633195788133171 457804289449793682199757)
                    ·
                      refine ⟨171676608543672630824909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 457804289449793682199757 171676608543672630824909)
                      ·
                        rfl

theorem cell23_334339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_334339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334339 prefixEnd_334339 := by exact prefixLift 334339
  have htrace : WordTrace (prefixWord ++ tailWord_334339) baseStart_334339 baseEnd_334339 := by
    simpa [prefixWord, tailWord_334339, baseEnd_334339] using wordTrace_append hprefix tailTrace_334339
  have hstable : (prefixWord ++ tailWord_334339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334339).length < 2 ^ (prefixWord ++ tailWord_334339).sum := by decide
  have hdescent : baseEnd_334339 < baseStart_334339 := by decide
  rcases family_descends (prefixWord ++ tailWord_334339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334355 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 8]
def baseStart_334355 : Nat := 118140960795 + 334355 * 2 ^ 59
def prefixEnd_334355 : Nat := 4983230072969 + 3 ^ 40 * 334355 * 2
def baseEnd_334355 : Nat := 57228274744714856074945

theorem tailTrace_334355 : CollatzResearch.WordTrace tailWord_334355 prefixEnd_334355 57228274744714856074945 := by
  unfold tailWord_334355
  simp only [CollatzResearch.WordTrace]
  refine ⟨12194928703696413132884519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8129952469130942088589679 12194928703696413132884519)
  ·
    refine ⟨18292393055544619699326779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12194928703696413132884519 18292393055544619699326779)
    ·
      refine ⟨27438589583316929548990169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18292393055544619699326779 27438589583316929548990169)
      ·
        refine ⟨20578942187487697161742627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27438589583316929548990169 20578942187487697161742627)
        ·
          refine ⟨30868413281231545742613941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20578942187487697161742627 30868413281231545742613941)
          ·
            refine ⟨2893913745115457413370057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30868413281231545742613941 2893913745115457413370057)
            ·
              refine ⟨2170435308836593060027543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893913745115457413370057 2170435308836593060027543)
              ·
                refine ⟨3255652963254889590041315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170435308836593060027543 3255652963254889590041315)
                ·
                  refine ⟨4883479444882334385061973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255652963254889590041315 4883479444882334385061973)
                  ·
                    refine ⟨57228274744714856074945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4883479444882334385061973 57228274744714856074945)
                    ·
                      rfl

theorem cell23_334355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_334355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334355 prefixEnd_334355 := by exact prefixLift 334355
  have htrace : WordTrace (prefixWord ++ tailWord_334355) baseStart_334355 baseEnd_334355 := by
    simpa [prefixWord, tailWord_334355, baseEnd_334355] using wordTrace_append hprefix tailTrace_334355
  have hstable : (prefixWord ++ tailWord_334355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334355).length < 2 ^ (prefixWord ++ tailWord_334355).sum := by decide
  have hdescent : baseEnd_334355 < baseStart_334355 := by decide
  rcases family_descends (prefixWord ++ tailWord_334355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334379 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 6, 2, 2]
def baseStart_334379 : Nat := 118140960795 + 334379 * 2 ^ 59
def prefixEnd_334379 : Nat := 4983230072969 + 3 ^ 40 * 334379 * 2
def baseEnd_334379 : Nat := 171697147769852474324725

theorem tailTrace_334379 : CollatzResearch.WordTrace tailWord_334379 prefixEnd_334379 171697147769852474324725 := by
  unfold tailWord_334379
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195804055609465231758191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8130536037072976821172127 12195804055609465231758191)
  ·
    refine ⟨18293706083414197847637287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12195804055609465231758191 18293706083414197847637287)
    ·
      refine ⟨27440559125121296771455931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18293706083414197847637287 27440559125121296771455931)
      ·
        refine ⟨41160838687681945157183897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27440559125121296771455931 41160838687681945157183897)
        ·
          refine ⟨30870629015761458867887923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41160838687681945157183897 30870629015761458867887923)
          ·
            refine ⟨46305943523642188301831885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30870629015761458867887923 46305943523642188301831885)
            ·
              refine ⟨17364728821365820613186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46305943523642188301831885 17364728821365820613186957)
              ·
                refine ⟨6511773308012182729945109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17364728821365820613186957 6511773308012182729945109)
                ·
                  refine ⟨305239373813071065466177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6511773308012182729945109 305239373813071065466177)
                  ·
                    refine ⟨228929530359803299099633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305239373813071065466177 228929530359803299099633)
                    ·
                      refine ⟨171697147769852474324725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228929530359803299099633 171697147769852474324725)
                      ·
                        rfl

theorem cell23_334379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 2, 2].length) (baseStart_334379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334379 prefixEnd_334379 := by exact prefixLift 334379
  have htrace : WordTrace (prefixWord ++ tailWord_334379) baseStart_334379 baseEnd_334379 := by
    simpa [prefixWord, tailWord_334379, baseEnd_334379] using wordTrace_append hprefix tailTrace_334379
  have hstable : (prefixWord ++ tailWord_334379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334379).length < 2 ^ (prefixWord ++ tailWord_334379).sum := by decide
  have hdescent : baseEnd_334379 < baseStart_334379 := by decide
  rcases family_descends (prefixWord ++ tailWord_334379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334392 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_334392 : Nat := 118140960795 + 334392 * 2 ^ 59
def prefixEnd_334392 : Nat := 4983230072969 + 3 ^ 40 * 334392 * 2
def baseEnd_334392 : Nat := 171703823018360923462165

theorem tailTrace_334392 : CollatzResearch.WordTrace tailWord_334392 prefixEnd_334392 171703823018360923462165 := by
  unfold tailWord_334392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098139102281184225990715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8130852136374912301320953 6098139102281184225990715)
  ·
    refine ⟨9147208653421776338986073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6098139102281184225990715 9147208653421776338986073)
    ·
      refine ⟨6860406490066332254239555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9147208653421776338986073 6860406490066332254239555)
      ·
        refine ⟨10290609735099498381359333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860406490066332254239555 10290609735099498381359333)
        ·
          refine ⟨1929489325331155946504875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10290609735099498381359333 1929489325331155946504875)
          ·
            refine ⟨2894233987996733919757313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929489325331155946504875 2894233987996733919757313)
            ·
              refine ⟨2170675490997550439817985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894233987996733919757313 2170675490997550439817985)
              ·
                refine ⟨1628006618248162829863489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170675490997550439817985 1628006618248162829863489)
                ·
                  refine ⟨1221004963686122122397617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628006618248162829863489 1221004963686122122397617)
                  ·
                    refine ⟨915753722764591591798213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221004963686122122397617 915753722764591591798213)
                    ·
                      refine ⟨171703823018360923462165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 915753722764591591798213 171703823018360923462165)
                      ·
                        rfl

theorem cell23_334392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_334392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334392 prefixEnd_334392 := by exact prefixLift 334392
  have htrace : WordTrace (prefixWord ++ tailWord_334392) baseStart_334392 baseEnd_334392 := by
    simpa [prefixWord, tailWord_334392, baseEnd_334392] using wordTrace_append hprefix tailTrace_334392
  have hstable : (prefixWord ++ tailWord_334392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334392).length < 2 ^ (prefixWord ++ tailWord_334392).sum := by decide
  have hdescent : baseEnd_334392 < baseStart_334392 := by decide
  rcases family_descends (prefixWord ++ tailWord_334392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334406 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_334406 : Nat := 118140960795 + 334406 * 2 ^ 59
def prefixEnd_334406 : Nat := 4983230072969 + 3 ^ 40 * 334406 * 2
def baseEnd_334406 : Nat := 57237003915841289562367

theorem tailTrace_334406 : CollatzResearch.WordTrace tailWord_334406 prefixEnd_334406 57237003915841289562367 := by
  unfold tailWord_334406
  simp only [CollatzResearch.WordTrace]
  refine ⟨381149650828489026343471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8131192551007765895327381 381149650828489026343471)
  ·
    refine ⟨571724476242733539515207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381149650828489026343471 571724476242733539515207)
    ·
      refine ⟨857586714364100309272811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571724476242733539515207 857586714364100309272811)
      ·
        refine ⟨1286380071546150463909217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857586714364100309272811 1286380071546150463909217)
        ·
          refine ⟨964785053659612847931913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286380071546150463909217 964785053659612847931913)
          ·
            refine ⟨723588790244709635948935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964785053659612847931913 723588790244709635948935)
            ·
              refine ⟨1085383185367064453923403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723588790244709635948935 1085383185367064453923403)
              ·
                refine ⟨1628074778050596680885105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085383185367064453923403 1628074778050596680885105)
                ·
                  refine ⟨1221056083537947510663829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628074778050596680885105 1221056083537947510663829)
                  ·
                    refine ⟨57237003915841289562367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1221056083537947510663829 57237003915841289562367)
                    ·
                      rfl

theorem cell23_334406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_334406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334406 prefixEnd_334406 := by exact prefixLift 334406
  have htrace : WordTrace (prefixWord ++ tailWord_334406) baseStart_334406 baseEnd_334406 := by
    simpa [prefixWord, tailWord_334406, baseEnd_334406] using wordTrace_append hprefix tailTrace_334406
  have hstable : (prefixWord ++ tailWord_334406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334406).length < 2 ^ (prefixWord ++ tailWord_334406).sum := by decide
  have hdescent : baseEnd_334406 < baseStart_334406 := by decide
  rcases family_descends (prefixWord ++ tailWord_334406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334413 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_334413 : Nat := 118140960795 + 334413 * 2 ^ 59
def prefixEnd_334413 : Nat := 4983230072969 + 3 ^ 40 * 334413 * 2
def baseEnd_334413 : Nat := 171714606112105341299569

theorem tailTrace_334413 : CollatzResearch.WordTrace tailWord_334413 prefixEnd_334413 171714606112105341299569 := by
  unfold tailWord_334413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197044137486289038495893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8131362758324192692330595 12197044137486289038495893)
  ·
    refine ⟨571736443944669798679495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12197044137486289038495893 571736443944669798679495)
    ·
      refine ⟨857604665917004698019243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571736443944669798679495 857604665917004698019243)
      ·
        refine ⟨1286406998875507047028865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857604665917004698019243 1286406998875507047028865)
        ·
          refine ⟨964805249156630285271649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286406998875507047028865 964805249156630285271649)
          ·
            refine ⟨723603936867472713953737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964805249156630285271649 723603936867472713953737)
            ·
              refine ⟨542702952650604535465303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723603936867472713953737 542702952650604535465303)
              ·
                refine ⟨814054428975906803197955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542702952650604535465303 814054428975906803197955)
                ·
                  refine ⟨1221081643463860204796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814054428975906803197955 1221081643463860204796933)
                  ·
                    refine ⟨228952808149473788399425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221081643463860204796933 228952808149473788399425)
                    ·
                      refine ⟨171714606112105341299569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228952808149473788399425 171714606112105341299569)
                      ·
                        rfl

theorem cell23_334413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_334413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334413 prefixEnd_334413 := by exact prefixLift 334413
  have htrace : WordTrace (prefixWord ++ tailWord_334413) baseStart_334413 baseEnd_334413 := by
    simpa [prefixWord, tailWord_334413, baseEnd_334413] using wordTrace_append hprefix tailTrace_334413
  have hstable : (prefixWord ++ tailWord_334413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334413).length < 2 ^ (prefixWord ++ tailWord_334413).sum := by decide
  have hdescent : baseEnd_334413 < baseStart_334413 := by decide
  rcases family_descends (prefixWord ++ tailWord_334413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334434 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_334434 : Nat := 118140960795 + 334434 * 2 ^ 59
def prefixEnd_334434 : Nat := 4983230072969 + 3 ^ 40 * 334434 * 2
def baseEnd_334434 : Nat := 171725389205849759136973

theorem tailTrace_334434 : CollatzResearch.WordTrace tailWord_334434 prefixEnd_334434 171725389205849759136973 := by
  unfold tailWord_334434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049452517602552406252589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8131873380273473083340237 3049452517602552406252589)
  ·
    refine ⟨1143544694100957152344721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3049452517602552406252589 1143544694100957152344721)
    ·
      refine ⟨857658520575717864258541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143544694100957152344721 857658520575717864258541)
      ·
        refine ⟨321621945215894199096953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 857658520575717864258541 321621945215894199096953)
        ·
          refine ⟨241216458911920649322715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321621945215894199096953 241216458911920649322715)
          ·
            refine ⟨361824688367880973984073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241216458911920649322715 361824688367880973984073)
            ·
              refine ⟨271368516275910730488055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361824688367880973984073 271368516275910730488055)
              ·
                refine ⟨407052774413866095732083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271368516275910730488055 407052774413866095732083)
                ·
                  refine ⟨610579161620799143598125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407052774413866095732083 610579161620799143598125)
                  ·
                    refine ⟨228967185607799678849297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610579161620799143598125 228967185607799678849297)
                    ·
                      refine ⟨171725389205849759136973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 228967185607799678849297 171725389205849759136973)
                      ·
                        rfl

theorem cell23_334434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_334434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334434 prefixEnd_334434 := by exact prefixLift 334434
  have htrace : WordTrace (prefixWord ++ tailWord_334434) baseStart_334434 baseEnd_334434 := by
    simpa [prefixWord, tailWord_334434, baseEnd_334434] using wordTrace_append hprefix tailTrace_334434
  have hstable : (prefixWord ++ tailWord_334434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334434).length < 2 ^ (prefixWord ++ tailWord_334434).sum := by decide
  have hdescent : baseEnd_334434 < baseStart_334434 := by decide
  rcases family_descends (prefixWord ++ tailWord_334434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334489 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_334489 : Nat := 118140960795 + 334489 * 2 ^ 59
def prefixEnd_334489 : Nat := 4983230072969 + 3 ^ 40 * 334489 * 2
def baseEnd_334489 : Nat := 171753630641847043949219

theorem tailTrace_334489 : CollatzResearch.WordTrace tailWord_334489 prefixEnd_334489 171753630641847043949219 := by
  unfold tailWord_334489
  simp only [CollatzResearch.WordTrace]
  refine ⟨12199816085210954018262521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8133210723473969345508347 12199816085210954018262521)
  ·
    refine ⟨9149862063908215513696891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12199816085210954018262521 9149862063908215513696891)
    ·
      refine ⟨13724793095862323270545337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9149862063908215513696891 13724793095862323270545337)
      ·
        refine ⟨10293594821896742452909003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13724793095862323270545337 10293594821896742452909003)
        ·
          refine ⟨15440392232845113679363505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10293594821896742452909003 15440392232845113679363505)
          ·
            refine ⟨11580294174633835259522629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15440392232845113679363505 11580294174633835259522629)
            ·
              refine ⟨2171305157743844111160493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11580294174633835259522629 2171305157743844111160493)
              ·
                refine ⟨814239434153941541685185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2171305157743844111160493 814239434153941541685185)
                ·
                  refine ⟨610679575615456156263889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814239434153941541685185 610679575615456156263889)
                  ·
                    refine ⟨458009681711592117197917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610679575615456156263889 458009681711592117197917)
                    ·
                      refine ⟨171753630641847043949219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458009681711592117197917 171753630641847043949219)
                      ·
                        rfl

theorem cell23_334489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_334489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334489 prefixEnd_334489 := by exact prefixLift 334489
  have htrace : WordTrace (prefixWord ++ tailWord_334489) baseStart_334489 baseEnd_334489 := by
    simpa [prefixWord, tailWord_334489, baseEnd_334489] using wordTrace_append hprefix tailTrace_334489
  have hstable : (prefixWord ++ tailWord_334489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334489).length < 2 ^ (prefixWord ++ tailWord_334489).sum := by decide
  have hdescent : baseEnd_334489 < baseStart_334489 := by decide
  rcases family_descends (prefixWord ++ tailWord_334489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334503 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_334503 : Nat := 118140960795 + 334503 * 2 ^ 59
def prefixEnd_334503 : Nat := 4983230072969 + 3 ^ 40 * 334503 * 2
def baseEnd_334503 : Nat := 171760819371009989174155

theorem tailTrace_334503 : CollatzResearch.WordTrace tailWord_334503 prefixEnd_334503 171760819371009989174155 := by
  unfold tailWord_334503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12200326707160234409272163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8133551138106822939514775 12200326707160234409272163)
  ·
    refine ⟨18300490060740351613908245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12200326707160234409272163 18300490060740351613908245)
    ·
      refine ⟨857835471597203981901949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18300490060740351613908245 857835471597203981901949)
      ·
        refine ⟨321688301848951493213231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 857835471597203981901949 321688301848951493213231)
        ·
          refine ⟨482532452773427239819847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321688301848951493213231 482532452773427239819847)
          ·
            refine ⟨723798679160140859729771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482532452773427239819847 723798679160140859729771)
            ·
              refine ⟨1085698018740211289594657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723798679160140859729771 1085698018740211289594657)
              ·
                refine ⟨814273514055158467195993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085698018740211289594657 814273514055158467195993)
                ·
                  refine ⟨610705135541368850396995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814273514055158467195993 610705135541368850396995)
                  ·
                    refine ⟨916057703312053275595493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610705135541368850396995 916057703312053275595493)
                    ·
                      refine ⟨171760819371009989174155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 916057703312053275595493 171760819371009989174155)
                      ·
                        rfl

theorem cell23_334503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_334503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334503 prefixEnd_334503 := by exact prefixLift 334503
  have htrace : WordTrace (prefixWord ++ tailWord_334503) baseStart_334503 baseEnd_334503 := by
    simpa [prefixWord, tailWord_334503, baseEnd_334503] using wordTrace_append hprefix tailTrace_334503
  have hstable : (prefixWord ++ tailWord_334503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334503).length < 2 ^ (prefixWord ++ tailWord_334503).sum := by decide
  have hdescent : baseEnd_334503 < baseStart_334503 := by decide
  rcases family_descends (prefixWord ++ tailWord_334503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334509 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 8]
def baseStart_334509 : Nat := 118140960795 + 334509 * 2 ^ 59
def prefixEnd_334509 : Nat := 4983230072969 + 3 ^ 40 * 334509 * 2
def baseEnd_334509 : Nat := 19084877806104107299903

theorem tailTrace_334509 : CollatzResearch.WordTrace tailWord_334509 prefixEnd_334509 19084877806104107299903 := by
  unfold tailWord_334509
  simp only [CollatzResearch.WordTrace]
  refine ⟨12200545545138497433990581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8133697030092331622660387 12200545545138497433990581)
  ·
    refine ⟨1143801144856734134436617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12200545545138497433990581 1143801144856734134436617)
    ·
      refine ⟨857850858642550600827463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143801144856734134436617 857850858642550600827463)
      ·
        refine ⟨1286776287963825901241195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857850858642550600827463 1286776287963825901241195)
        ·
          refine ⟨1930164431945738851861793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286776287963825901241195 1930164431945738851861793)
          ·
            refine ⟨1447623323959304138896345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930164431945738851861793 1447623323959304138896345)
            ·
              refine ⟨1085717492969478104172259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447623323959304138896345 1085717492969478104172259)
              ·
                refine ⟨1628576239454217156258389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085717492969478104172259 1628576239454217156258389)
                ·
                  refine ⟨19084877806104107299903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1628576239454217156258389 19084877806104107299903)
                  ·
                    rfl

theorem cell23_334509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_334509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334509 prefixEnd_334509 := by exact prefixLift 334509
  have htrace : WordTrace (prefixWord ++ tailWord_334509) baseStart_334509 baseEnd_334509 := by
    simpa [prefixWord, tailWord_334509, baseEnd_334509] using wordTrace_append hprefix tailTrace_334509
  have hstable : (prefixWord ++ tailWord_334509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334509).length < 2 ^ (prefixWord ++ tailWord_334509).sum := by decide
  have hdescent : baseEnd_334509 < baseStart_334509 := by decide
  rcases family_descends (prefixWord ++ tailWord_334509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334553 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 1, 1, 3]
def baseStart_334553 : Nat := 118140960795 + 334553 * 2 ^ 59
def prefixEnd_334553 : Nat := 4983230072969 + 3 ^ 40 * 334553 * 2
def baseEnd_334553 : Nat := 171786493403734793548925

theorem tailTrace_334553 : CollatzResearch.WordTrace tailWord_334553 prefixEnd_334553 171786493403734793548925 := by
  unfold tailWord_334553
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202150356979092948592313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8134766904652728632394875 12202150356979092948592313)
  ·
    refine ⟨9151612767734319711444235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12202150356979092948592313 9151612767734319711444235)
    ·
      refine ⟨13727419151601479567166353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9151612767734319711444235 13727419151601479567166353)
      ·
        refine ⟨10295564363701109675374765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13727419151601479567166353 10295564363701109675374765)
        ·
          refine ⟨3860836636387916128265537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10295564363701109675374765 3860836636387916128265537)
          ·
            refine ⟨2895627477290937096199153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3860836636387916128265537 2895627477290937096199153)
            ·
              refine ⟨2171720607968202822149365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895627477290937096199153 2171720607968202822149365)
              ·
                refine ⟨203598806997019014576503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2171720607968202822149365 203598806997019014576503)
                ·
                  refine ⟨305398210495528521864755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203598806997019014576503 305398210495528521864755)
                  ·
                    refine ⟨458097315743292782797133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305398210495528521864755 458097315743292782797133)
                    ·
                      refine ⟨171786493403734793548925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458097315743292782797133 171786493403734793548925)
                      ·
                        rfl

theorem cell23_334553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_334553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334553 prefixEnd_334553 := by exact prefixLift 334553
  have htrace : WordTrace (prefixWord ++ tailWord_334553) baseStart_334553 baseEnd_334553 := by
    simpa [prefixWord, tailWord_334553, baseEnd_334553] using wordTrace_append hprefix tailTrace_334553
  have hstable : (prefixWord ++ tailWord_334553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334553).length < 2 ^ (prefixWord ++ tailWord_334553).sum := by decide
  have hdescent : baseEnd_334553 < baseStart_334553 := by decide
  rcases family_descends (prefixWord ++ tailWord_334553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334563 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 2, 3, 2]
def baseStart_334563 : Nat := 118140960795 + 334563 * 2 ^ 59
def prefixEnd_334563 : Nat := 4983230072969 + 3 ^ 40 * 334563 * 2
def baseEnd_334563 : Nat := 171791628210279754423879

theorem tailTrace_334563 : CollatzResearch.WordTrace tailWord_334563 prefixEnd_334563 171791628210279754423879 := by
  unfold tailWord_334563
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202515086942864656456343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8135010057961909770970895 12202515086942864656456343)
  ·
    refine ⟨18303772630414296984684515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12202515086942864656456343 18303772630414296984684515)
    ·
      refine ⟨27455658945621445477026773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18303772630414296984684515 27455658945621445477026773)
      ·
        refine ⟨643492006538002628367815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27455658945621445477026773 643492006538002628367815)
        ·
          refine ⟨965238009807003942551723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643492006538002628367815 965238009807003942551723)
          ·
            refine ⟨1447857014710505913827585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965238009807003942551723 1447857014710505913827585)
            ·
              refine ⟨1085892761032879435370689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447857014710505913827585 1085892761032879435370689)
              ·
                refine ⟨814419570774659576528017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085892761032879435370689 814419570774659576528017)
                ·
                  refine ⟨610814678080994682396013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814419570774659576528017 610814678080994682396013)
                  ·
                    refine ⟨229055504280373005898505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610814678080994682396013 229055504280373005898505)
                    ·
                      refine ⟨171791628210279754423879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229055504280373005898505 171791628210279754423879)
                      ·
                        rfl

theorem cell23_334563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_334563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334563 prefixEnd_334563 := by exact prefixLift 334563
  have htrace : WordTrace (prefixWord ++ tailWord_334563) baseStart_334563 baseEnd_334563 := by
    simpa [prefixWord, tailWord_334563, baseEnd_334563] using wordTrace_append hprefix tailTrace_334563
  have hstable : (prefixWord ++ tailWord_334563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334563).length < 2 ^ (prefixWord ++ tailWord_334563).sum := by decide
  have hdescent : baseEnd_334563 < baseStart_334563 := by decide
  rcases family_descends (prefixWord ++ tailWord_334563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334569 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_334569 : Nat := 118140960795 + 334569 * 2 ^ 59
def prefixEnd_334569 : Nat := 4983230072969 + 3 ^ 40 * 334569 * 2
def baseEnd_334569 : Nat := 57264903031402243649617

theorem tailTrace_334569 : CollatzResearch.WordTrace tailWord_334569 prefixEnd_334569 57264903031402243649617 := by
  unfold tailWord_334569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202733924921127681174761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8135155949947418454116507 12202733924921127681174761)
  ·
    refine ⟨9152050443690845760881071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12202733924921127681174761 9152050443690845760881071)
    ·
      refine ⟨13728075665536268641321607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9152050443690845760881071 13728075665536268641321607)
      ·
        refine ⟨20592113498304402961982411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13728075665536268641321607 20592113498304402961982411)
        ·
          refine ⟨30888170247456604442973617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20592113498304402961982411 30888170247456604442973617)
          ·
            refine ⟨23166127685592453332230213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30888170247456604442973617 23166127685592453332230213)
            ·
              refine ⟨4343648941048584999793165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23166127685592453332230213 4343648941048584999793165)
              ·
                refine ⟨1628868352893219374922437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343648941048584999793165 1628868352893219374922437)
                ·
                  refine ⟨305412816167478632797957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628868352893219374922437 305412816167478632797957)
                  ·
                    refine ⟨57264903031402243649617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305412816167478632797957 57264903031402243649617)
                    ·
                      rfl

theorem cell23_334569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_334569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334569 prefixEnd_334569 := by exact prefixLift 334569
  have htrace : WordTrace (prefixWord ++ tailWord_334569) baseStart_334569 baseEnd_334569 := by
    simpa [prefixWord, tailWord_334569, baseEnd_334569] using wordTrace_append hprefix tailTrace_334569
  have hstable : (prefixWord ++ tailWord_334569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334569).length < 2 ^ (prefixWord ++ tailWord_334569).sum := by decide
  have hdescent : baseEnd_334569 < baseStart_334569 := by decide
  rcases family_descends (prefixWord ++ tailWord_334569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334586 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_334586 : Nat := 118140960795 + 334586 * 2 ^ 59
def prefixEnd_334586 : Nat := 4983230072969 + 3 ^ 40 * 334586 * 2
def baseEnd_334586 : Nat := 57267812755111054812091

theorem tailTrace_334586 : CollatzResearch.WordTrace tailWord_334586 prefixEnd_334586 57267812755111054812091 := by
  unfold tailWord_334586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050838491464884896135903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8135569310573026389695741 3050838491464884896135903)
  ·
    refine ⟨4576257737197327344203855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3050838491464884896135903 4576257737197327344203855)
    ·
      refine ⟨6864386605795991016305783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576257737197327344203855 6864386605795991016305783)
      ·
        refine ⟨10296579908693986524458675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864386605795991016305783 10296579908693986524458675)
        ·
          refine ⟨15444869863040979786688013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296579908693986524458675 15444869863040979786688013)
          ·
            refine ⟨5791826198640367420008005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15444869863040979786688013 5791826198640367420008005)
            ·
              refine ⟨1085967412245068891251501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5791826198640367420008005 1085967412245068891251501)
              ·
                refine ⟨407237779591900834219313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085967412245068891251501 407237779591900834219313)
                ·
                  refine ⟨305428334693925625664485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407237779591900834219313 305428334693925625664485)
                  ·
                    refine ⟨57267812755111054812091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 305428334693925625664485 57267812755111054812091)
                    ·
                      rfl

theorem cell23_334586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_334586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334586 prefixEnd_334586 := by exact prefixLift 334586
  have htrace : WordTrace (prefixWord ++ tailWord_334586) baseStart_334586 baseEnd_334586 := by
    simpa [prefixWord, tailWord_334586, baseEnd_334586] using wordTrace_append hprefix tailTrace_334586
  have hstable : (prefixWord ++ tailWord_334586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334586).length < 2 ^ (prefixWord ++ tailWord_334586).sum := by decide
  have hdescent : baseEnd_334586 < baseStart_334586 := by decide
  rcases family_descends (prefixWord ++ tailWord_334586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334596 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_334596 : Nat := 118140960795 + 334596 * 2 ^ 59
def prefixEnd_334596 : Nat := 4983230072969 + 3 ^ 40 * 334596 * 2
def baseEnd_334596 : Nat := 171808573071878125311227

theorem tailTrace_334596 : CollatzResearch.WordTrace tailWord_334596 prefixEnd_334596 171808573071878125311227 := by
  unfold tailWord_334596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101859347911655646203821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8135812463882207528271761 6101859347911655646203821)
  ·
    refine ⟨2288197255466870867326433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6101859347911655646203821 2288197255466870867326433)
    ·
      refine ⟨1716147941600153150494825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2288197255466870867326433 1716147941600153150494825)
      ·
        refine ⟨1287110956200114862871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716147941600153150494825 1287110956200114862871119)
        ·
          refine ⟨1930666434300172294306679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287110956200114862871119 1930666434300172294306679)
          ·
            refine ⟨2895999651450258441460019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930666434300172294306679 2895999651450258441460019)
            ·
              refine ⟨4343999477175387662190029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895999651450258441460019 4343999477175387662190029)
              ·
                refine ⟨1628999803940770373321261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4343999477175387662190029 1628999803940770373321261)
                ·
                  refine ⟨610874926477788889995473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1628999803940770373321261 610874926477788889995473)
                  ·
                    refine ⟨458156194858341667496605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 610874926477788889995473 458156194858341667496605)
                    ·
                      refine ⟨171808573071878125311227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458156194858341667496605 171808573071878125311227)
                      ·
                        rfl

theorem cell23_334596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_334596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334596 prefixEnd_334596 := by exact prefixLift 334596
  have htrace : WordTrace (prefixWord ++ tailWord_334596) baseStart_334596 baseEnd_334596 := by
    simpa [prefixWord, tailWord_334596, baseEnd_334596] using wordTrace_append hprefix tailTrace_334596
  have hstable : (prefixWord ++ tailWord_334596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334596).length < 2 ^ (prefixWord ++ tailWord_334596).sum := by decide
  have hdescent : baseEnd_334596 < baseStart_334596 := by decide
  rcases family_descends (prefixWord ++ tailWord_334596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334610 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_334610 : Nat := 118140960795 + 334610 * 2 ^ 59
def prefixEnd_334610 : Nat := 4983230072969 + 3 ^ 40 * 334610 * 2
def baseEnd_334610 : Nat := 171815761801041070536163

theorem tailTrace_334610 : CollatzResearch.WordTrace tailWord_334610 prefixEnd_334610 171815761801041070536163 := by
  unfold tailWord_334610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051057329443147920854321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8136152878515061122278189 3051057329443147920854321)
  ·
    refine ⟨2288292997082360940640741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3051057329443147920854321 2288292997082360940640741)
    ·
      refine ⟨429054936952942676370139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2288292997082360940640741 429054936952942676370139)
      ·
        refine ⟨643582405429414014555209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429054936952942676370139 643582405429414014555209)
        ·
          refine ⟨482686804072060510916407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643582405429414014555209 482686804072060510916407)
          ·
            refine ⟨724030206108090766374611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482686804072060510916407 724030206108090766374611)
            ·
              refine ⟨1086045309162136149561917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724030206108090766374611 1086045309162136149561917)
              ·
                refine ⟨407266990935801056085719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086045309162136149561917 407266990935801056085719)
                ·
                  refine ⟨610900486403701584128579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407266990935801056085719 610900486403701584128579)
                  ·
                    refine ⟨916350729605552376192869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 610900486403701584128579 916350729605552376192869)
                    ·
                      refine ⟨171815761801041070536163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 916350729605552376192869 171815761801041070536163)
                      ·
                        rfl

theorem cell23_334610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_334610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334610 prefixEnd_334610 := by exact prefixLift 334610
  have htrace : WordTrace (prefixWord ++ tailWord_334610) baseStart_334610 baseEnd_334610 := by
    simpa [prefixWord, tailWord_334610, baseEnd_334610] using wordTrace_append hprefix tailTrace_334610
  have hstable : (prefixWord ++ tailWord_334610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334610).length < 2 ^ (prefixWord ++ tailWord_334610).sum := by decide
  have hdescent : baseEnd_334610 < baseStart_334610 := by decide
  rcases family_descends (prefixWord ++ tailWord_334610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334637 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_334637 : Nat := 118140960795 + 334637 * 2 ^ 59
def prefixEnd_334637 : Nat := 4983230072969 + 3 ^ 40 * 334637 * 2
def baseEnd_334637 : Nat := 57276541926237488299513

theorem tailTrace_334637 : CollatzResearch.WordTrace tailWord_334637 prefixEnd_334637 57276541926237488299513 := by
  unfold tailWord_334637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205214088674775294650165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136809392449850196433443 12205214088674775294650165)
  ·
    refine ⟨1144238820813260183873453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12205214088674775294650165 1144238820813260183873453)
    ·
      refine ⟨429089557804972568952545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1144238820813260183873453 429089557804972568952545)
      ·
        refine ⟨321817168353729426714409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429089557804972568952545 321817168353729426714409)
        ·
          refine ⟨241362876265297070035807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321817168353729426714409 241362876265297070035807)
          ·
            refine ⟨362044314397945605053711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241362876265297070035807 362044314397945605053711)
            ·
              refine ⟨543066471596918407580567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362044314397945605053711 543066471596918407580567)
              ·
                refine ⟨814599707395377611370851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543066471596918407580567 814599707395377611370851)
                ·
                  refine ⟨1221899561093066417056277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814599707395377611370851 1221899561093066417056277)
                  ·
                    refine ⟨57276541926237488299513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1221899561093066417056277 57276541926237488299513)
                    ·
                      rfl

theorem cell23_334637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_334637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334637 prefixEnd_334637 := by exact prefixLift 334637
  have htrace : WordTrace (prefixWord ++ tailWord_334637) baseStart_334637 baseEnd_334637 := by
    simpa [prefixWord, tailWord_334637, baseEnd_334637] using wordTrace_append hprefix tailTrace_334637
  have hstable : (prefixWord ++ tailWord_334637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334637).length < 2 ^ (prefixWord ++ tailWord_334637).sum := by decide
  have hdescent : baseEnd_334637 < baseStart_334637 := by decide
  rcases family_descends (prefixWord ++ tailWord_334637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334643 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 3]
def baseStart_334643 : Nat := 118140960795 + 334643 * 2 ^ 59
def prefixEnd_334643 : Nat := 4983230072969 + 3 ^ 40 * 334643 * 2
def baseEnd_334643 : Nat := 171832706662639441423511

theorem tailTrace_334643 : CollatzResearch.WordTrace tailWord_334643 prefixEnd_334643 171832706662639441423511 := by
  unfold tailWord_334643
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205432926653038319368583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8136955284435358879579055 12205432926653038319368583)
  ·
    refine ⟨18308149389979557479052875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205432926653038319368583 18308149389979557479052875)
    ·
      refine ⟨27462224084969336218579313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18308149389979557479052875 27462224084969336218579313)
      ·
        refine ⟨20596668063727002163934485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27462224084969336218579313 20596668063727002163934485)
        ·
          refine ⟨965468815487203226434429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20596668063727002163934485 965468815487203226434429)
          ·
            refine ⟨362050805807701209912911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 965468815487203226434429 362050805807701209912911)
            ·
              refine ⟨543076208711551814869367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362050805807701209912911 543076208711551814869367)
              ·
                refine ⟨814614313067327722304051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543076208711551814869367 814614313067327722304051)
                ·
                  refine ⟨1221921469600991583456077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814614313067327722304051 1221921469600991583456077)
                  ·
                    refine ⟨458220551100371843796029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1221921469600991583456077 458220551100371843796029)
                    ·
                      refine ⟨171832706662639441423511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458220551100371843796029 171832706662639441423511)
                      ·
                        rfl

theorem cell23_334643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_334643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334643 prefixEnd_334643 := by exact prefixLift 334643
  have htrace : WordTrace (prefixWord ++ tailWord_334643) baseStart_334643 baseEnd_334643 := by
    simpa [prefixWord, tailWord_334643, baseEnd_334643] using wordTrace_append hprefix tailTrace_334643
  have hstable : (prefixWord ++ tailWord_334643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334643).length < 2 ^ (prefixWord ++ tailWord_334643).sum := by decide
  have hdescent : baseEnd_334643 < baseStart_334643 := by decide
  rcases family_descends (prefixWord ++ tailWord_334643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334689 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 7]
def baseStart_334689 : Nat := 118140960795 + 334689 * 2 ^ 59
def prefixEnd_334689 : Nat := 4983230072969 + 3 ^ 40 * 334689 * 2
def baseEnd_334689 : Nat := 19095147419194029049811

theorem tailTrace_334689 : CollatzResearch.WordTrace tailWord_334689 prefixEnd_334689 19095147419194029049811 := by
  unfold tailWord_334689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207110684486388175543121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8138073789657592117028747 12207110684486388175543121)
  ·
    refine ⟨9155333013364791131657341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12207110684486388175543121 9155333013364791131657341)
    ·
      refine ⟨3433249880011796674371503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9155333013364791131657341 3433249880011796674371503)
      ·
        refine ⟨5149874820017695011557255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433249880011796674371503 5149874820017695011557255)
        ·
          refine ⟨7724812230026542517335883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149874820017695011557255 7724812230026542517335883)
          ·
            refine ⟨11587218345039813776003825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724812230026542517335883 11587218345039813776003825)
            ·
              refine ⟨8690413758779860332002869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11587218345039813776003825 8690413758779860332002869)
              ·
                refine ⟨814726289885611906125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8690413758779860332002869 814726289885611906125269)
                ·
                  refine ⟨19095147419194029049811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 814726289885611906125269 19095147419194029049811)
                  ·
                    rfl

theorem cell23_334689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_334689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334689 prefixEnd_334689 := by exact prefixLift 334689
  have htrace : WordTrace (prefixWord ++ tailWord_334689) baseStart_334689 baseEnd_334689 := by
    simpa [prefixWord, tailWord_334689, baseEnd_334689] using wordTrace_append hprefix tailTrace_334689
  have hstable : (prefixWord ++ tailWord_334689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334689).length < 2 ^ (prefixWord ++ tailWord_334689).sum := by decide
  have hdescent : baseEnd_334689 < baseStart_334689 := by decide
  rcases family_descends (prefixWord ++ tailWord_334689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334700 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_334700 : Nat := 118140960795 + 334700 * 2 ^ 59
def prefixEnd_334700 : Nat := 4983230072969 + 3 ^ 40 * 334700 * 2
def baseEnd_334700 : Nat := 171861975059945718410749

theorem tailTrace_334700 : CollatzResearch.WordTrace tailWord_334700 prefixEnd_334700 171861975059945718410749 := by
  unfold tailWord_334700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103755943723268527096777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8138341258297691369462369 6103755943723268527096777)
  ·
    refine ⟨4577816957792451395322583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6103755943723268527096777 4577816957792451395322583)
    ·
      refine ⟨6866725436688677092983875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577816957792451395322583 6866725436688677092983875)
      ·
        refine ⟨10300088155033015639475813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6866725436688677092983875 10300088155033015639475813)
        ·
          refine ⟨1931266529068690432401715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10300088155033015639475813 1931266529068690432401715)
          ·
            refine ⟨2896899793603035648602573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931266529068690432401715 2896899793603035648602573)
            ·
              refine ⟨1086337422601138368225965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2896899793603035648602573 1086337422601138368225965)
              ·
                refine ⟨407376533475426888084737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1086337422601138368225965 407376533475426888084737)
                ·
                  refine ⟨305532400106570166063553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407376533475426888084737 305532400106570166063553)
                  ·
                    refine ⟨229149300079927624547665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305532400106570166063553 229149300079927624547665)
                    ·
                      refine ⟨171861975059945718410749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229149300079927624547665 171861975059945718410749)
                      ·
                        rfl

theorem cell23_334700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_334700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334700 prefixEnd_334700 := by exact prefixLift 334700
  have htrace : WordTrace (prefixWord ++ tailWord_334700) baseStart_334700 baseEnd_334700 := by
    simpa [prefixWord, tailWord_334700, baseEnd_334700] using wordTrace_append hprefix tailTrace_334700
  have hstable : (prefixWord ++ tailWord_334700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334700).length < 2 ^ (prefixWord ++ tailWord_334700).sum := by decide
  have hdescent : baseEnd_334700 < baseStart_334700 := by decide
  rcases family_descends (prefixWord ++ tailWord_334700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334719 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 7]
def baseStart_334719 : Nat := 118140960795 + 334719 * 2 ^ 59
def prefixEnd_334719 : Nat := 4983230072969 + 3 ^ 40 * 334719 * 2
def baseEnd_334719 : Nat := 57290577064127048024387

theorem tailTrace_334719 : CollatzResearch.WordTrace tailWord_334719 prefixEnd_334719 57290577064127048024387 := by
  unfold tailWord_334719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208204874377703299135211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8138803249585135532756807 12208204874377703299135211)
  ·
    refine ⟨18312307311566554948702817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12208204874377703299135211 18312307311566554948702817)
    ·
      refine ⟨13734230483674916211527113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18312307311566554948702817 13734230483674916211527113)
      ·
        refine ⟨10300672862756187158645335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13734230483674916211527113 10300672862756187158645335)
        ·
          refine ⟨15451009294134280737968003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10300672862756187158645335 15451009294134280737968003)
          ·
            refine ⟨23176513941201421106952005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15451009294134280737968003 23176513941201421106952005)
            ·
              refine ⟨4345596363975266457553501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23176513941201421106952005 4345596363975266457553501)
              ·
                refine ⟨1629598636490724921582563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4345596363975266457553501 1629598636490724921582563)
                ·
                  refine ⟨2444397954736087382373845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629598636490724921582563 2444397954736087382373845)
                  ·
                    refine ⟨57290577064127048024387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2444397954736087382373845 57290577064127048024387)
                    ·
                      rfl

theorem cell23_334719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_334719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334719 prefixEnd_334719 := by exact prefixLift 334719
  have htrace : WordTrace (prefixWord ++ tailWord_334719) baseStart_334719 baseEnd_334719 := by
    simpa [prefixWord, tailWord_334719, baseEnd_334719] using wordTrace_append hprefix tailTrace_334719
  have hstable : (prefixWord ++ tailWord_334719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334719).length < 2 ^ (prefixWord ++ tailWord_334719).sum := by decide
  have hdescent : baseEnd_334719 < baseStart_334719 := by decide
  rcases family_descends (prefixWord ++ tailWord_334719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334756 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_334756 : Nat := 118140960795 + 334756 * 2 ^ 59
def prefixEnd_334756 : Nat := 4983230072969 + 3 ^ 40 * 334756 * 2
def baseEnd_334756 : Nat := 171890729976597499310491

theorem tailTrace_334756 : CollatzResearch.WordTrace tailWord_334756 prefixEnd_334756 171890729976597499310491 := by
  unfold tailWord_334756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104777187621829309116061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8139702916829105745488081 6104777187621829309116061)
  ·
    refine ⟨2289291445358185990918523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6104777187621829309116061 2289291445358185990918523)
    ·
      refine ⟨3433937168037278986377785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289291445358185990918523 3433937168037278986377785)
      ·
        refine ⟨2575452876027959239783339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3433937168037278986377785 2575452876027959239783339)
        ·
          refine ⟨3863179314041938859675009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575452876027959239783339 3863179314041938859675009)
          ·
            refine ⟨2897384485531454144756257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863179314041938859675009 2897384485531454144756257)
            ·
              refine ⟨2173038364148590608567193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897384485531454144756257 2173038364148590608567193)
              ·
                refine ⟨1629778773111442956425395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173038364148590608567193 1629778773111442956425395)
                ·
                  refine ⟨2444668159667164434638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629778773111442956425395 2444668159667164434638093)
                  ·
                    refine ⟨916750559875186662989285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444668159667164434638093 916750559875186662989285)
                    ·
                      refine ⟨171890729976597499310491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 916750559875186662989285 171890729976597499310491)
                      ·
                        rfl

theorem cell23_334756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_334756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334756 prefixEnd_334756 := by exact prefixLift 334756
  have htrace : WordTrace (prefixWord ++ tailWord_334756) baseStart_334756 baseEnd_334756 := by
    simpa [prefixWord, tailWord_334756, baseEnd_334756] using wordTrace_append hprefix tailTrace_334756
  have hstable : (prefixWord ++ tailWord_334756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334756).length < 2 ^ (prefixWord ++ tailWord_334756).sum := by decide
  have hdescent : baseEnd_334756 < baseStart_334756 := by decide
  rcases family_descends (prefixWord ++ tailWord_334756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334773 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_334773 : Nat := 118140960795 + 334773 * 2 ^ 59
def prefixEnd_334773 : Nat := 4983230072969 + 3 ^ 40 * 334773 * 2
def baseEnd_334773 : Nat := 171899459147723932797913

theorem tailTrace_334773 : CollatzResearch.WordTrace tailWord_334773 prefixEnd_334773 171899459147723932797913 := by
  unfold tailWord_334773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210174416182070521600973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8140116277454713681067315 12210174416182070521600973)
  ·
    refine ⟨4578815406068276445600365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12210174416182070521600973 4578815406068276445600365)
    ·
      refine ⟨1717055777275603667100137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4578815406068276445600365 1717055777275603667100137)
      ·
        refine ⟨1287791832956702750325103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717055777275603667100137 1287791832956702750325103)
        ·
          refine ⟨1931687749435054125487655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287791832956702750325103 1931687749435054125487655)
          ·
            refine ⟨2897531624152581188231483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931687749435054125487655 2897531624152581188231483)
            ·
              refine ⟨4346297436228871782347225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897531624152581188231483 4346297436228871782347225)
              ·
                refine ⟨3259723077171653836760419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4346297436228871782347225 3259723077171653836760419)
                ·
                  refine ⟨4889584615757480755140629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259723077171653836760419 4889584615757480755140629)
                  ·
                    refine ⟨229199278863631910397217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4889584615757480755140629 229199278863631910397217)
                    ·
                      refine ⟨171899459147723932797913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229199278863631910397217 171899459147723932797913)
                      ·
                        rfl

theorem cell23_334773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_334773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334773 prefixEnd_334773 := by exact prefixLift 334773
  have htrace : WordTrace (prefixWord ++ tailWord_334773) baseStart_334773 baseEnd_334773 := by
    simpa [prefixWord, tailWord_334773, baseEnd_334773] using wordTrace_append hprefix tailTrace_334773
  have hstable : (prefixWord ++ tailWord_334773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334773).length < 2 ^ (prefixWord ++ tailWord_334773).sum := by decide
  have hdescent : baseEnd_334773 < baseStart_334773 := by decide
  rcases family_descends (prefixWord ++ tailWord_334773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334796 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 8]
def baseStart_334796 : Nat := 118140960795 + 334796 * 2 ^ 59
def prefixEnd_334796 : Nat := 4983230072969 + 3 ^ 40 * 334796 * 2
def baseEnd_334796 : Nat := 19101252133641926978923

theorem tailTrace_334796 : CollatzResearch.WordTrace tailWord_334796 prefixEnd_334796 19101252133641926978923 := by
  unfold tailWord_334796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105506647549372724844121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8140675530065830299792161 6105506647549372724844121)
  ·
    refine ⟨4579129985662029543633091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6105506647549372724844121 4579129985662029543633091)
    ·
      refine ⟨6868694978493044315449637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579129985662029543633091 6868694978493044315449637)
      ·
        refine ⟨1287880308467445809146807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6868694978493044315449637 1287880308467445809146807)
        ·
          refine ⟨1931820462701168713720211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287880308467445809146807 1931820462701168713720211)
          ·
            refine ⟨2897730694051753070580317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931820462701168713720211 2897730694051753070580317)
            ·
              refine ⟨1086649010269407401467619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2897730694051753070580317 1086649010269407401467619)
              ·
                refine ⟨1629973515404111102201429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086649010269407401467619 1629973515404111102201429)
                ·
                  refine ⟨19101252133641926978923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1629973515404111102201429 19101252133641926978923)
                  ·
                    rfl

theorem cell23_334796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_334796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334796 prefixEnd_334796 := by exact prefixLift 334796
  have htrace : WordTrace (prefixWord ++ tailWord_334796) baseStart_334796 baseEnd_334796 := by
    simpa [prefixWord, tailWord_334796, baseEnd_334796] using wordTrace_append hprefix tailTrace_334796
  have hstable : (prefixWord ++ tailWord_334796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334796).length < 2 ^ (prefixWord ++ tailWord_334796).sum := by decide
  have hdescent : baseEnd_334796 < baseStart_334796 := by decide
  rcases family_descends (prefixWord ++ tailWord_334796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334877 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_334877 : Nat := 118140960795 + 334877 * 2 ^ 59
def prefixEnd_334877 : Nat := 4983230072969 + 3 ^ 40 * 334877 * 2
def baseEnd_334877 : Nat := 57317620378597175299145

theorem tailTrace_334877 : CollatzResearch.WordTrace tailWord_334877 prefixEnd_334877 57317620378597175299145 := by
  unfold tailWord_334877
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213967607805296283386885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8142645071870197522257923 12213967607805296283386885)
  ·
    refine ⟨2290118926463493053135041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12213967607805296283386885 2290118926463493053135041)
    ·
      refine ⟨1717589194847619789851281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2290118926463493053135041 1717589194847619789851281)
      ·
        refine ⟨1288191896135714842388461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717589194847619789851281 1288191896135714842388461)
        ·
          refine ⟨483071961050893065895673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1288191896135714842388461 483071961050893065895673)
          ·
            refine ⟨362303970788169799421755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483071961050893065895673 362303970788169799421755)
            ·
              refine ⟨543455956182254699132633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362303970788169799421755 543455956182254699132633)
              ·
                refine ⟨407591967136691024349475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543455956182254699132633 407591967136691024349475)
                ·
                  refine ⟨611387950705036536524213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407591967136691024349475 611387950705036536524213)
                  ·
                    refine ⟨57317620378597175299145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 611387950705036536524213 57317620378597175299145)
                    ·
                      rfl

theorem cell23_334877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_334877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334877 prefixEnd_334877 := by exact prefixLift 334877
  have htrace : WordTrace (prefixWord ++ tailWord_334877) baseStart_334877 baseEnd_334877 := by
    simpa [prefixWord, tailWord_334877, baseEnd_334877] using wordTrace_append hprefix tailTrace_334877
  have hstable : (prefixWord ++ tailWord_334877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334877).length < 2 ^ (prefixWord ++ tailWord_334877).sum := by decide
  have hdescent : baseEnd_334877 < baseStart_334877 := by decide
  rcases family_descends (prefixWord ++ tailWord_334877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334890 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_334890 : Nat := 118140960795 + 334890 * 2 ^ 59
def prefixEnd_334890 : Nat := 4983230072969 + 3 ^ 40 * 334890 * 2
def baseEnd_334890 : Nat := 57319845461433325011625

theorem tailTrace_334890 : CollatzResearch.WordTrace tailWord_334890 prefixEnd_334890 57319845461433325011625 := by
  unfold tailWord_334890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053610439189549875902531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8142961171172133002406749 3053610439189549875902531)
  ·
    refine ⟨4580415658784324813853797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053610439189549875902531 4580415658784324813853797)
    ·
      refine ⟨858827936022060902597587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4580415658784324813853797 858827936022060902597587)
      ·
        refine ⟨1288241904033091353896381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858827936022060902597587 1288241904033091353896381)
        ·
          refine ⟨483090714012409257711143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1288241904033091353896381 483090714012409257711143)
          ·
            refine ⟨724636071018613886566715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483090714012409257711143 724636071018613886566715)
            ·
              refine ⟨1086954106527920829850073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724636071018613886566715 1086954106527920829850073)
              ·
                refine ⟨815215579895940622387555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086954106527920829850073 815215579895940622387555)
                ·
                  refine ⟨1222823369843910933581333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815215579895940622387555 1222823369843910933581333)
                  ·
                    refine ⟨57319845461433325011625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1222823369843910933581333 57319845461433325011625)
                    ·
                      rfl

theorem cell23_334890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_334890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334890 prefixEnd_334890 := by exact prefixLift 334890
  have htrace : WordTrace (prefixWord ++ tailWord_334890) baseStart_334890 baseEnd_334890 := by
    simpa [prefixWord, tailWord_334890, baseEnd_334890] using wordTrace_append hprefix tailTrace_334890
  have hstable : (prefixWord ++ tailWord_334890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334890).length < 2 ^ (prefixWord ++ tailWord_334890).sum := by decide
  have hdescent : baseEnd_334890 < baseStart_334890 := by decide
  rcases family_descends (prefixWord ++ tailWord_334890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334923 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 9, 2]
def baseStart_334923 : Nat := 118140960795 + 334923 * 2 ^ 59
def prefixEnd_334923 : Nat := 4983230072969 + 3 ^ 40 * 334923 * 2
def baseEnd_334923 : Nat := 171976481245898345922223

theorem tailTrace_334923 : CollatzResearch.WordTrace tailWord_334923 prefixEnd_334923 171976481245898345922223 := by
  unfold tailWord_334923
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215645365638646139561423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8143763577092430759707615 12215645365638646139561423)
  ·
    refine ⟨18323468048457969209342135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215645365638646139561423 18323468048457969209342135)
    ·
      refine ⟨27485202072686953814013203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323468048457969209342135 27485202072686953814013203)
      ·
        refine ⟨41227803109030430721019805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27485202072686953814013203 41227803109030430721019805)
        ·
          refine ⟨15460426165886411520382427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41227803109030430721019805 15460426165886411520382427)
          ·
            refine ⟨23190639248829617280573641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460426165886411520382427 23190639248829617280573641)
            ·
              refine ⟨17392979436622212960430231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23190639248829617280573641 17392979436622212960430231)
              ·
                refine ⟨26089469154933319440645347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17392979436622212960430231 26089469154933319440645347)
                ·
                  refine ⟨39134203732399979160968021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26089469154933319440645347 39134203732399979160968021)
                  ·
                    refine ⟨229301974994531127896297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39134203732399979160968021 229301974994531127896297)
                    ·
                      refine ⟨171976481245898345922223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229301974994531127896297 171976481245898345922223)
                      ·
                        rfl

theorem cell23_334923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9, 2].length) (baseStart_334923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334923 prefixEnd_334923 := by exact prefixLift 334923
  have htrace : WordTrace (prefixWord ++ tailWord_334923) baseStart_334923 baseEnd_334923 := by
    simpa [prefixWord, tailWord_334923, baseEnd_334923] using wordTrace_append hprefix tailTrace_334923
  have hstable : (prefixWord ++ tailWord_334923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334923).length < 2 ^ (prefixWord ++ tailWord_334923).sum := by decide
  have hdescent : baseEnd_334923 < baseStart_334923 := by decide
  rcases family_descends (prefixWord ++ tailWord_334923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334930 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_334930 : Nat := 118140960795 + 334930 * 2 ^ 59
def prefixEnd_334930 : Nat := 4983230072969 + 3 ^ 40 * 334930 * 2
def baseEnd_334930 : Nat := 171980075610479818534691

theorem tailTrace_334930 : CollatzResearch.WordTrace tailWord_334930 prefixEnd_334930 171980075610479818534691 := by
  unfold tailWord_334930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053975169153321583766561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8143933784408857556710829 3053975169153321583766561)
  ·
    refine ⟨2290481376864991187824921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3053975169153321583766561 2290481376864991187824921)
    ·
      refine ⟨1717861032648743390868691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2290481376864991187824921 1717861032648743390868691)
      ·
        refine ⟨2576791548973115086303037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717861032648743390868691 2576791548973115086303037)
        ·
          refine ⟨966296830864918157363639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2576791548973115086303037 966296830864918157363639)
          ·
            refine ⟨1449445246297377236045459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966296830864918157363639 1449445246297377236045459)
            ·
              refine ⟨2174167869446065854068189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449445246297377236045459 2174167869446065854068189)
              ·
                refine ⟨815312951042274695275571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174167869446065854068189 815312951042274695275571)
                ·
                  refine ⟨1222969426563412042913357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815312951042274695275571 1222969426563412042913357)
                  ·
                    refine ⟨458613534961279516092509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1222969426563412042913357 458613534961279516092509)
                    ·
                      refine ⟨171980075610479818534691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458613534961279516092509 171980075610479818534691)
                      ·
                        rfl

theorem cell23_334930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_334930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334930 prefixEnd_334930 := by exact prefixLift 334930
  have htrace : WordTrace (prefixWord ++ tailWord_334930) baseStart_334930 baseEnd_334930 := by
    simpa [prefixWord, tailWord_334930, baseEnd_334930] using wordTrace_append hprefix tailTrace_334930
  have hstable : (prefixWord ++ tailWord_334930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334930).length < 2 ^ (prefixWord ++ tailWord_334930).sum := by decide
  have hdescent : baseEnd_334930 < baseStart_334930 := by decide
  rcases family_descends (prefixWord ++ tailWord_334930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334987 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 2, 2, 2]
def baseStart_334987 : Nat := 118140960795 + 334987 * 2 ^ 59
def prefixEnd_334987 : Nat := 4983230072969 + 3 ^ 40 * 334987 * 2
def baseEnd_334987 : Nat := 172009344007786095521929

theorem tailTrace_334987 : CollatzResearch.WordTrace tailWord_334987 prefixEnd_334987 172009344007786095521929 := by
  unfold tailWord_334987
  simp only [CollatzResearch.WordTrace]
  refine ⟨12217979637406785069891215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8145319758271190046594143 12217979637406785069891215)
  ·
    refine ⟨18326969456110177604836823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12217979637406785069891215 18326969456110177604836823)
    ·
      refine ⟨27490454184165266407255235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18326969456110177604836823 27490454184165266407255235)
      ·
        refine ⟨41235681276247899610882853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27490454184165266407255235 41235681276247899610882853)
        ·
          refine ⟨7731690239296481177040535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41235681276247899610882853 7731690239296481177040535)
          ·
            refine ⟨11597535358944721765560803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731690239296481177040535 11597535358944721765560803)
            ·
              refine ⟨17396303038417082648341205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11597535358944721765560803 17396303038417082648341205)
              ·
                refine ⟨407725852462900374570497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17396303038417082648341205 407725852462900374570497)
                ·
                  refine ⟨305794389347175280927873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407725852462900374570497 305794389347175280927873)
                  ·
                    refine ⟨229345792010381460695905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305794389347175280927873 229345792010381460695905)
                    ·
                      refine ⟨172009344007786095521929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229345792010381460695905 172009344007786095521929)
                      ·
                        rfl

theorem cell23_334987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2, 2].length) (baseStart_334987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_334987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_334987 prefixEnd_334987 := by exact prefixLift 334987
  have htrace : WordTrace (prefixWord ++ tailWord_334987) baseStart_334987 baseEnd_334987 := by
    simpa [prefixWord, tailWord_334987, baseEnd_334987] using wordTrace_append hprefix tailTrace_334987
  have hstable : (prefixWord ++ tailWord_334987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334987).length < 2 ^ (prefixWord ++ tailWord_334987).sum := by decide
  have hdescent : baseEnd_334987 < baseStart_334987 := by decide
  rcases family_descends (prefixWord ++ tailWord_334987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335003 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3]
def baseStart_335003 : Nat := 118140960795 + 335003 * 2 ^ 59
def prefixEnd_335003 : Nat := 4983230072969 + 3 ^ 40 * 335003 * 2
def baseEnd_335003 : Nat := 172017559698258032921855

theorem tailTrace_335003 : CollatzResearch.WordTrace tailWord_335003 prefixEnd_335003 172017559698258032921855 := by
  unfold tailWord_335003
  simp only [CollatzResearch.WordTrace]
  refine ⟨12218563205348819802473663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8145708803565879868315775 12218563205348819802473663)
  ·
    refine ⟨18327844808023229703710495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12218563205348819802473663 18327844808023229703710495)
    ·
      refine ⟨27491767212034844555565743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18327844808023229703710495 27491767212034844555565743)
      ·
        refine ⟨41237650818052266833348615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27491767212034844555565743 41237650818052266833348615)
        ·
          refine ⟨61856476227078400250022923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41237650818052266833348615 61856476227078400250022923)
          ·
            refine ⟨92784714340617600375034385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61856476227078400250022923 92784714340617600375034385)
            ·
              refine ⟨69588535755463200281275789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92784714340617600375034385 69588535755463200281275789)
              ·
                refine ⟨26095700908298700105478421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69588535755463200281275789 26095700908298700105478421)
                ·
                  refine ⟨1223235980076501567444301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26095700908298700105478421 1223235980076501567444301)
                  ·
                    refine ⟨458713492528688087791613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1223235980076501567444301 458713492528688087791613)
                    ·
                      refine ⟨172017559698258032921855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458713492528688087791613 172017559698258032921855)
                      ·
                        rfl

theorem cell23_335003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].length) (baseStart_335003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335003 prefixEnd_335003 := by exact prefixLift 335003
  have htrace : WordTrace (prefixWord ++ tailWord_335003) baseStart_335003 baseEnd_335003 := by
    simpa [prefixWord, tailWord_335003, baseEnd_335003] using wordTrace_append hprefix tailTrace_335003
  have hstable : (prefixWord ++ tailWord_335003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335003).length < 2 ^ (prefixWord ++ tailWord_335003).sum := by decide
  have hdescent : baseEnd_335003 < baseStart_335003 := by decide
  rcases family_descends (prefixWord ++ tailWord_335003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335023 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 4, 5]
def baseStart_335023 : Nat := 118140960795 + 335023 * 2 ^ 59
def prefixEnd_335023 : Nat := 4983230072969 + 3 ^ 40 * 335023 * 2
def baseEnd_335023 : Nat := 57342609770449318223921

theorem tailTrace_335023 : CollatzResearch.WordTrace tailWord_335023 prefixEnd_335023 57342609770449318223921 := by
  unfold tailWord_335023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219292665276363218201723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8146195110184242145467815 12219292665276363218201723)
  ·
    refine ⟨18328938997914544827302585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12219292665276363218201723 18328938997914544827302585)
    ·
      refine ⟨13746704248435908620476939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18328938997914544827302585 13746704248435908620476939)
      ·
        refine ⟨20620056372653862930715409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13746704248435908620476939 20620056372653862930715409)
        ·
          refine ⟨15465042279490397198036557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20620056372653862930715409 15465042279490397198036557)
          ·
            refine ⟨5799390854808898949263709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15465042279490397198036557 5799390854808898949263709)
            ·
              refine ⟨2174771570553337105973891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799390854808898949263709 2174771570553337105973891)
              ·
                refine ⟨3262157355830005658960837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174771570553337105973891 3262157355830005658960837)
                ·
                  refine ⟨611654504218126061055157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3262157355830005658960837 611654504218126061055157)
                  ·
                    refine ⟨57342609770449318223921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 611654504218126061055157 57342609770449318223921)
                    ·
                      rfl

theorem cell23_335023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_335023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335023 prefixEnd_335023 := by exact prefixLift 335023
  have htrace : WordTrace (prefixWord ++ tailWord_335023) baseStart_335023 baseEnd_335023 := by
    simpa [prefixWord, tailWord_335023, baseEnd_335023] using wordTrace_append hprefix tailTrace_335023
  have hstable : (prefixWord ++ tailWord_335023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335023).length < 2 ^ (prefixWord ++ tailWord_335023).sum := by decide
  have hdescent : baseEnd_335023 < baseStart_335023 := by decide
  rcases family_descends (prefixWord ++ tailWord_335023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335033 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_335033 : Nat := 118140960795 + 335033 * 2 ^ 59
def prefixEnd_335033 : Nat := 4983230072969 + 3 ^ 40 * 335033 * 2
def baseEnd_335033 : Nat := 172032964117892915546717

theorem tailTrace_335033 : CollatzResearch.WordTrace tailWord_335033 prefixEnd_335033 172032964117892915546717 := by
  unfold tailWord_335033
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219657395240134926065753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8146438263493423284043835 12219657395240134926065753)
  ·
    refine ⟨9164743046430101194549315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12219657395240134926065753 9164743046430101194549315)
    ·
      refine ⟨13747114569645151791823973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9164743046430101194549315 13747114569645151791823973)
      ·
        refine ⟨2577583981808465960966995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13747114569645151791823973 2577583981808465960966995)
        ·
          refine ⟨3866375972712698941450493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577583981808465960966995 3866375972712698941450493)
          ·
            refine ⟨1449890989767262103043935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3866375972712698941450493 1449890989767262103043935)
            ·
              refine ⟨2174836484650893154565903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449890989767262103043935 2174836484650893154565903)
              ·
                refine ⟨3262254726976339731848855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174836484650893154565903 3262254726976339731848855)
                ·
                  refine ⟨4893382090464509597773283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262254726976339731848855 4893382090464509597773283)
                  ·
                    refine ⟨7340073135696764396659925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893382090464509597773283 7340073135696764396659925)
                    ·
                      refine ⟨172032964117892915546717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7340073135696764396659925 172032964117892915546717)
                      ·
                        rfl

theorem cell23_335033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_335033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335033 prefixEnd_335033 := by exact prefixLift 335033
  have htrace : WordTrace (prefixWord ++ tailWord_335033) baseStart_335033 baseEnd_335033 := by
    simpa [prefixWord, tailWord_335033, baseEnd_335033] using wordTrace_append hprefix tailTrace_335033
  have hstable : (prefixWord ++ tailWord_335033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335033).length < 2 ^ (prefixWord ++ tailWord_335033).sum := by decide
  have hdescent : baseEnd_335033 < baseStart_335033 := by decide
  rcases family_descends (prefixWord ++ tailWord_335033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335038 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_335038 : Nat := 118140960795 + 335038 * 2 ^ 59
def prefixEnd_335038 : Nat := 4983230072969 + 3 ^ 40 * 335038 * 2
def baseEnd_335038 : Nat := 172035531521165395984195

theorem tailTrace_335038 : CollatzResearch.WordTrace tailWord_335038 prefixEnd_335038 172035531521165395984195 := by
  unfold tailWord_335038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527479970027752597499721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8146559840148013853331845 1527479970027752597499721)
  ·
    refine ⟨1145609977520814448124791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1527479970027752597499721 1145609977520814448124791)
    ·
      refine ⟨1718414966281221672187187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145609977520814448124791 1718414966281221672187187)
      ·
        refine ⟨2577622449421832508280781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718414966281221672187187 2577622449421832508280781)
        ·
          refine ⟨966608418533187190605293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2577622449421832508280781 966608418533187190605293)
          ·
            refine ⟨362478156949945196476985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 966608418533187190605293 362478156949945196476985)
            ·
              refine ⟨271858617712458897357739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362478156949945196476985 271858617712458897357739)
              ·
                refine ⟨407787926568688346036609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271858617712458897357739 407787926568688346036609)
                ·
                  refine ⟨305840944926516259527457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407787926568688346036609 305840944926516259527457)
                  ·
                    refine ⟨229380708694887194645593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305840944926516259527457 229380708694887194645593)
                    ·
                      refine ⟨172035531521165395984195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229380708694887194645593 172035531521165395984195)
                      ·
                        rfl

theorem cell23_335038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_335038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335038 prefixEnd_335038 := by exact prefixLift 335038
  have htrace : WordTrace (prefixWord ++ tailWord_335038) baseStart_335038 baseEnd_335038 := by
    simpa [prefixWord, tailWord_335038, baseEnd_335038] using wordTrace_append hprefix tailTrace_335038
  have hstable : (prefixWord ++ tailWord_335038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335038).length < 2 ^ (prefixWord ++ tailWord_335038).sum := by decide
  have hdescent : baseEnd_335038 < baseStart_335038 := by decide
  rcases family_descends (prefixWord ++ tailWord_335038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335043 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_335043 : Nat := 118140960795 + 335043 * 2 ^ 59
def prefixEnd_335043 : Nat := 4983230072969 + 3 ^ 40 * 335043 * 2
def baseEnd_335043 : Nat := 172038098924437876421671

theorem tailTrace_335043 : CollatzResearch.WordTrace tailWord_335043 prefixEnd_335043 172038098924437876421671 := by
  unfold tailWord_335043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12220022125203906633929783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8146681416802604422619855 12220022125203906633929783)
  ·
    refine ⟨18330033187805859950894675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12220022125203906633929783 18330033187805859950894675)
    ·
      refine ⟨27495049781708789926342013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18330033187805859950894675 27495049781708789926342013)
      ·
        refine ⟨10310643668140796222378255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27495049781708789926342013 10310643668140796222378255)
        ·
          refine ⟨15465965502211194333567383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310643668140796222378255 15465965502211194333567383)
          ·
            refine ⟨23198948253316791500351075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15465965502211194333567383 23198948253316791500351075)
            ·
              refine ⟨34798422379975187250526613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23198948253316791500351075 34798422379975187250526613)
              ·
                refine ⟨1631176049061336902368435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34798422379975187250526613 1631176049061336902368435)
                ·
                  refine ⟨2446764073592005353552653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631176049061336902368435 2446764073592005353552653)
                  ·
                    refine ⟨917536527597002007582245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446764073592005353552653 917536527597002007582245)
                    ·
                      refine ⟨172038098924437876421671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 917536527597002007582245 172038098924437876421671)
                      ·
                        rfl

theorem cell23_335043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_335043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335043 prefixEnd_335043 := by exact prefixLift 335043
  have htrace : WordTrace (prefixWord ++ tailWord_335043) baseStart_335043 baseEnd_335043 := by
    simpa [prefixWord, tailWord_335043, baseEnd_335043] using wordTrace_append hprefix tailTrace_335043
  have hstable : (prefixWord ++ tailWord_335043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335043).length < 2 ^ (prefixWord ++ tailWord_335043).sum := by decide
  have hdescent : baseEnd_335043 < baseStart_335043 := by decide
  rcases family_descends (prefixWord ++ tailWord_335043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335123 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_335123 : Nat := 118140960795 + 335123 * 2 ^ 59
def prefixEnd_335123 : Nat := 4983230072969 + 3 ^ 40 * 335123 * 2
def baseEnd_335123 : Nat := 172079177376797563421303

theorem tailTrace_335123 : CollatzResearch.WordTrace tailWord_335123 prefixEnd_335123 172079177376797563421303 := by
  unfold tailWord_335123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222939964914080296842023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148626643276053531228015 12222939964914080296842023)
  ·
    refine ⟨18334409947371120445263035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12222939964914080296842023 18334409947371120445263035)
    ·
      refine ⟨27501614921056680667894553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18334409947371120445263035 27501614921056680667894553)
      ·
        refine ⟨20626211190792510500920915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27501614921056680667894553 20626211190792510500920915)
        ·
          refine ⟨30939316786188765751381373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20626211190792510500920915 30939316786188765751381373)
          ·
            refine ⟨11602243794820787156768015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30939316786188765751381373 11602243794820787156768015)
            ·
              refine ⟨17403365692231180735152023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11602243794820787156768015 17403365692231180735152023)
              ·
                refine ⟨26105048538346771102728035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17403365692231180735152023 26105048538346771102728035)
                ·
                  refine ⟨39157572807520156654092053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26105048538346771102728035 39157572807520156654092053)
                  ·
                    refine ⟨1835511225352507343160565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39157572807520156654092053 1835511225352507343160565)
                    ·
                      refine ⟨172079177376797563421303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1835511225352507343160565 172079177376797563421303)
                      ·
                        rfl

theorem cell23_335123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_335123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335123 prefixEnd_335123 := by exact prefixLift 335123
  have htrace : WordTrace (prefixWord ++ tailWord_335123) baseStart_335123 baseEnd_335123 := by
    simpa [prefixWord, tailWord_335123, baseEnd_335123] using wordTrace_append hprefix tailTrace_335123
  have hstable : (prefixWord ++ tailWord_335123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335123).length < 2 ^ (prefixWord ++ tailWord_335123).sum := by decide
  have hdescent : baseEnd_335123 < baseStart_335123 := by decide
  rcases family_descends (prefixWord ++ tailWord_335123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335127 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_335127 : Nat := 118140960795 + 335127 * 2 ^ 59
def prefixEnd_335127 : Nat := 4983230072969 + 3 ^ 40 * 335127 * 2
def baseEnd_335127 : Nat := 172081231299415547771285

theorem tailTrace_335127 : CollatzResearch.WordTrace tailWord_335127 prefixEnd_335127 172081231299415547771285 := by
  unfold tailWord_335127
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223085856899588979987635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148723904599725986658423 12223085856899588979987635)
  ·
    refine ⟨18334628785349383469981453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12223085856899588979987635 18334628785349383469981453)
    ·
      refine ⟨6875485794506018801243045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18334628785349383469981453 6875485794506018801243045)
      ·
        refine ⟨1289153586469878525233071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6875485794506018801243045 1289153586469878525233071)
        ·
          refine ⟨1933730379704817787849607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289153586469878525233071 1933730379704817787849607)
          ·
            refine ⟨2900595569557226681774411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933730379704817787849607 2900595569557226681774411)
            ·
              refine ⟨4350893354335840022661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900595569557226681774411 4350893354335840022661617)
              ·
                refine ⟨3263170015751880016996213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4350893354335840022661617 3263170015751880016996213)
                ·
                  refine ⟨305922188976738751593395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263170015751880016996213 305922188976738751593395)
                  ·
                    refine ⟨458883283465108127390093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305922188976738751593395 458883283465108127390093)
                    ·
                      refine ⟨172081231299415547771285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458883283465108127390093 172081231299415547771285)
                      ·
                        rfl

theorem cell23_335127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_335127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335127 prefixEnd_335127 := by exact prefixLift 335127
  have htrace : WordTrace (prefixWord ++ tailWord_335127) baseStart_335127 baseEnd_335127 := by
    simpa [prefixWord, tailWord_335127, baseEnd_335127] using wordTrace_append hprefix tailTrace_335127
  have hstable : (prefixWord ++ tailWord_335127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335127).length < 2 ^ (prefixWord ++ tailWord_335127).sum := by decide
  have hdescent : baseEnd_335127 < baseStart_335127 := by decide
  rcases family_descends (prefixWord ++ tailWord_335127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335134 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_335134 : Nat := 118140960795 + 335134 * 2 ^ 59
def prefixEnd_335134 : Nat := 4983230072969 + 3 ^ 40 * 335134 * 2
def baseEnd_335134 : Nat := 19120536184888557820417

theorem tailTrace_335134 : CollatzResearch.WordTrace tailWord_335134 prefixEnd_335134 19120536184888557820417 := by
  unfold tailWord_335134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527917645984278646936557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8148894111916152783661637 1527917645984278646936557)
  ·
    refine ⟨572969117244104492601209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1527917645984278646936557 572969117244104492601209)
    ·
      refine ⟨429726837933078369450907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572969117244104492601209 429726837933078369450907)
      ·
        refine ⟨644590256899617554176361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429726837933078369450907 644590256899617554176361)
        ·
          refine ⟨483442692674713165632271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644590256899617554176361 483442692674713165632271)
          ·
            refine ⟨725164039012069748448407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483442692674713165632271 725164039012069748448407)
            ·
              refine ⟨1087746058518104622672611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725164039012069748448407 1087746058518104622672611)
              ·
                refine ⟨1631619087777156934008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087746058518104622672611 1631619087777156934008917)
                ·
                  refine ⟨19120536184888557820417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1631619087777156934008917 19120536184888557820417)
                  ·
                    rfl

theorem cell23_335134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_335134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335134 prefixEnd_335134 := by exact prefixLift 335134
  have htrace : WordTrace (prefixWord ++ tailWord_335134) baseStart_335134 baseEnd_335134 := by
    simpa [prefixWord, tailWord_335134, baseEnd_335134] using wordTrace_append hprefix tailTrace_335134
  have hstable : (prefixWord ++ tailWord_335134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335134).length < 2 ^ (prefixWord ++ tailWord_335134).sum := by decide
  have hdescent : baseEnd_335134 < baseStart_335134 := by decide
  rcases family_descends (prefixWord ++ tailWord_335134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335137 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_335137 : Nat := 118140960795 + 335137 * 2 ^ 59
def prefixEnd_335137 : Nat := 4983230072969 + 3 ^ 40 * 335137 * 2
def baseEnd_335137 : Nat := 172086366105960508646239

theorem tailTrace_335137 : CollatzResearch.WordTrace tailWord_335137 prefixEnd_335137 172086366105960508646239 := by
  unfold tailWord_335137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223450586863360687851665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8148967057908907125234443 12223450586863360687851665)
  ·
    refine ⟨9167587940147520515888749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12223450586863360687851665 9167587940147520515888749)
    ·
      refine ⟨3437845477555320193458281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9167587940147520515888749 3437845477555320193458281)
      ·
        refine ⟨2578384108166490145093711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3437845477555320193458281 2578384108166490145093711)
        ·
          refine ⟨3867576162249735217640567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578384108166490145093711 3867576162249735217640567)
          ·
            refine ⟨5801364243374602826460851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867576162249735217640567 5801364243374602826460851)
            ·
              refine ⟨8702046365061904239691277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801364243374602826460851 8702046365061904239691277)
              ·
                refine ⟨3263267386898214089884229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8702046365061904239691277 3263267386898214089884229)
                ·
                  refine ⟨611862635043415141853293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3263267386898214089884229 611862635043415141853293)
                  ·
                    refine ⟨229448488141280678194985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611862635043415141853293 229448488141280678194985)
                    ·
                      refine ⟨172086366105960508646239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229448488141280678194985 172086366105960508646239)
                      ·
                        rfl

theorem cell23_335137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_335137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335137 prefixEnd_335137 := by exact prefixLift 335137
  have htrace : WordTrace (prefixWord ++ tailWord_335137) baseStart_335137 baseEnd_335137 := by
    simpa [prefixWord, tailWord_335137, baseEnd_335137] using wordTrace_append hprefix tailTrace_335137
  have hstable : (prefixWord ++ tailWord_335137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335137).length < 2 ^ (prefixWord ++ tailWord_335137).sum := by decide
  have hdescent : baseEnd_335137 < baseStart_335137 := by decide
  rcases family_descends (prefixWord ++ tailWord_335137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335144 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_335144 : Nat := 118140960795 + 335144 * 2 ^ 59
def prefixEnd_335144 : Nat := 4983230072969 + 3 ^ 40 * 335144 * 2
def baseEnd_335144 : Nat := 172089960470541981258707

theorem tailTrace_335144 : CollatzResearch.WordTrace tailWord_335144 prefixEnd_335144 172089960470541981258707 := by
  unfold tailWord_335144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111852948919000441678243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8149137265225333922237657 6111852948919000441678243)
  ·
    refine ⟨9167779423378500662517365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111852948919000441678243 9167779423378500662517365)
    ·
      refine ⟨859479320941734437111003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9167779423378500662517365 859479320941734437111003)
      ·
        refine ⟨1289218981412601655666505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859479320941734437111003 1289218981412601655666505)
        ·
          refine ⟨966914236059451241749879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289218981412601655666505 966914236059451241749879)
          ·
            refine ⟨1450371354089176862624819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966914236059451241749879 1450371354089176862624819)
            ·
              refine ⟨2175557031133765293937229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450371354089176862624819 2175557031133765293937229)
              ·
                refine ⟨815833886675161985226461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175557031133765293937229 815833886675161985226461)
                ·
                  refine ⟨305937707503185744459923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815833886675161985226461 305937707503185744459923)
                  ·
                    refine ⟨458906561254778616689885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305937707503185744459923 458906561254778616689885)
                    ·
                      refine ⟨172089960470541981258707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458906561254778616689885 172089960470541981258707)
                      ·
                        rfl

theorem cell23_335144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_335144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335144 prefixEnd_335144 := by exact prefixLift 335144
  have htrace : WordTrace (prefixWord ++ tailWord_335144) baseStart_335144 baseEnd_335144 := by
    simpa [prefixWord, tailWord_335144, baseEnd_335144] using wordTrace_append hprefix tailTrace_335144
  have hstable : (prefixWord ++ tailWord_335144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335144).length < 2 ^ (prefixWord ++ tailWord_335144).sum := by decide
  have hdescent : baseEnd_335144 < baseStart_335144 := by decide
  rcases family_descends (prefixWord ++ tailWord_335144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335167 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_335167 : Nat := 118140960795 + 335167 * 2 ^ 59
def prefixEnd_335167 : Nat := 4983230072969 + 3 ^ 40 * 335167 * 2
def baseEnd_335167 : Nat := 172101770525595391271101

theorem tailTrace_335167 : CollatzResearch.WordTrace tailWord_335167 prefixEnd_335167 172101770525595391271101 := by
  unfold tailWord_335167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224544776754675811443755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8149696517836450540962503 12224544776754675811443755)
  ·
    refine ⟨18336817165132013717165633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224544776754675811443755 18336817165132013717165633)
    ·
      refine ⟨13752612873849010287874225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18336817165132013717165633 13752612873849010287874225)
      ·
        refine ⟨10314459655386757715905669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13752612873849010287874225 10314459655386757715905669)
        ·
          refine ⟨1933961185385017071732313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10314459655386757715905669 1933961185385017071732313)
          ·
            refine ⟨1450470889038762803799235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1933961185385017071732313 1450470889038762803799235)
            ·
              refine ⟨2175706333558144205698853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450470889038762803799235 2175706333558144205698853)
              ·
                refine ⟨407944937542152038568535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2175706333558144205698853 407944937542152038568535)
                ·
                  refine ⟨611917406313228057852803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407944937542152038568535 611917406313228057852803)
                  ·
                    refine ⟨917876109469842086779205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 611917406313228057852803 917876109469842086779205)
                    ·
                      refine ⟨172101770525595391271101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 917876109469842086779205 172101770525595391271101)
                      ·
                        rfl

theorem cell23_335167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_335167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335167 prefixEnd_335167 := by exact prefixLift 335167
  have htrace : WordTrace (prefixWord ++ tailWord_335167) baseStart_335167 baseEnd_335167 := by
    simpa [prefixWord, tailWord_335167, baseEnd_335167] using wordTrace_append hprefix tailTrace_335167
  have hstable : (prefixWord ++ tailWord_335167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335167).length < 2 ^ (prefixWord ++ tailWord_335167).sum := by decide
  have hdescent : baseEnd_335167 < baseStart_335167 := by decide
  rcases family_descends (prefixWord ++ tailWord_335167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335187 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 3]
def baseStart_335187 : Nat := 118140960795 + 335187 * 2 ^ 59
def prefixEnd_335187 : Nat := 4983230072969 + 3 ^ 40 * 335187 * 2
def baseEnd_335187 : Nat := 172112040138685313021009

theorem tailTrace_335187 : CollatzResearch.WordTrace tailWord_335187 prefixEnd_335187 172112040138685313021009 := by
  unfold tailWord_335187
  simp only [CollatzResearch.WordTrace]
  refine ⟨12225274236682219227171815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8150182824454812818114543 12225274236682219227171815)
  ·
    refine ⟨18337911355023328840757723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12225274236682219227171815 18337911355023328840757723)
    ·
      refine ⟨27506867032534993261136585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18337911355023328840757723 27506867032534993261136585)
      ·
        refine ⟨20630150274401244945852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27506867032534993261136585 20630150274401244945852439)
        ·
          refine ⟨30945225411601867418778659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20630150274401244945852439 30945225411601867418778659)
          ·
            refine ⟨46417838117402801128167989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30945225411601867418778659 46417838117402801128167989)
            ·
              refine ⟨4351672323506512605765749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46417838117402801128167989 4351672323506512605765749)
              ·
                refine ⟨407969280328735556790539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4351672323506512605765749 407969280328735556790539)
                ·
                  refine ⟨611953920493103335185809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407969280328735556790539 611953920493103335185809)
                  ·
                    refine ⟨458965440369827501389357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611953920493103335185809 458965440369827501389357)
                    ·
                      refine ⟨172112040138685313021009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 458965440369827501389357 172112040138685313021009)
                      ·
                        rfl

theorem cell23_335187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_335187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335187 prefixEnd_335187 := by exact prefixLift 335187
  have htrace : WordTrace (prefixWord ++ tailWord_335187) baseStart_335187 baseEnd_335187 := by
    simpa [prefixWord, tailWord_335187, baseEnd_335187] using wordTrace_append hprefix tailTrace_335187
  have hstable : (prefixWord ++ tailWord_335187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335187).length < 2 ^ (prefixWord ++ tailWord_335187).sum := by decide
  have hdescent : baseEnd_335187 < baseStart_335187 := by decide
  rcases family_descends (prefixWord ++ tailWord_335187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335201 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_335201 : Nat := 118140960795 + 335201 * 2 ^ 59
def prefixEnd_335201 : Nat := 4983230072969 + 3 ^ 40 * 335201 * 2
def baseEnd_335201 : Nat := 172119228867848258245945

theorem tailTrace_335201 : CollatzResearch.WordTrace tailWord_335201 prefixEnd_335201 172119228867848258245945 := by
  unfold tailWord_335201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12225784858631499618181457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8150523239087666412120971 12225784858631499618181457)
  ·
    refine ⟨9169338643973624713636093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12225784858631499618181457 9169338643973624713636093)
    ·
      refine ⟨3438501991490109267613535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9169338643973624713636093 3438501991490109267613535)
      ·
        refine ⟨5157752987235163901420303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438501991490109267613535 5157752987235163901420303)
        ·
          refine ⟨7736629480852745852130455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5157752987235163901420303 7736629480852745852130455)
          ·
            refine ⟨11604944221279118778195683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7736629480852745852130455 11604944221279118778195683)
            ·
              refine ⟨17407416331918678167293525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11604944221279118778195683 17407416331918678167293525)
              ·
                refine ⟨203993160139672009772971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17407416331918678167293525 203993160139672009772971)
                ·
                  refine ⟨305989740209508014659457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203993160139672009772971 305989740209508014659457)
                  ·
                    refine ⟨229492305157131010994593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305989740209508014659457 229492305157131010994593)
                    ·
                      refine ⟨172119228867848258245945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229492305157131010994593 172119228867848258245945)
                      ·
                        rfl

theorem cell23_335201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_335201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335201 prefixEnd_335201 := by exact prefixLift 335201
  have htrace : WordTrace (prefixWord ++ tailWord_335201) baseStart_335201 baseEnd_335201 := by
    simpa [prefixWord, tailWord_335201, baseEnd_335201] using wordTrace_append hprefix tailTrace_335201
  have hstable : (prefixWord ++ tailWord_335201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335201).length < 2 ^ (prefixWord ++ tailWord_335201).sum := by decide
  have hdescent : baseEnd_335201 < baseStart_335201 := by decide
  rcases family_descends (prefixWord ++ tailWord_335201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335207 : List Nat := [1, 1, 5, 1, 4, 1, 2, 8]
def baseStart_335207 : Nat := 118140960795 + 335207 * 2 ^ 59
def prefixEnd_335207 : Nat := 4983230072969 + 3 ^ 40 * 335207 * 2
def baseEnd_335207 : Nat := 6374900361176860547071

theorem tailTrace_335207 : CollatzResearch.WordTrace tailWord_335207 prefixEnd_335207 6374900361176860547071 := by
  unfold tailWord_335207
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226003696609762642899875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8150669131073175095266583 12226003696609762642899875)
  ·
    refine ⟨18339005544914643964349813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12226003696609762642899875 18339005544914643964349813)
    ·
      refine ⟨1719281769835747871657795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18339005544914643964349813 1719281769835747871657795)
      ·
        refine ⟨2578922654753621807486693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719281769835747871657795 2578922654753621807486693)
        ·
          refine ⟨483547997766304088903755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2578922654753621807486693 483547997766304088903755)
          ·
            refine ⟨725321996649456133355633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483547997766304088903755 725321996649456133355633)
            ·
              refine ⟨543991497487092100016725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725321996649456133355633 543991497487092100016725)
              ·
                refine ⟨6374900361176860547071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 543991497487092100016725 6374900361176860547071)
                ·
                  rfl

theorem cell23_335207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 8].length) (baseStart_335207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335207 prefixEnd_335207 := by exact prefixLift 335207
  have htrace : WordTrace (prefixWord ++ tailWord_335207) baseStart_335207 baseEnd_335207 := by
    simpa [prefixWord, tailWord_335207, baseEnd_335207] using wordTrace_append hprefix tailTrace_335207
  have hstable : (prefixWord ++ tailWord_335207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335207).length < 2 ^ (prefixWord ++ tailWord_335207).sum := by decide
  have hdescent : baseEnd_335207 < baseStart_335207 := by decide
  rcases family_descends (prefixWord ++ tailWord_335207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335252 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_335252 : Nat := 118140960795 + 335252 * 2 ^ 59
def prefixEnd_335252 : Nat := 4983230072969 + 3 ^ 40 * 335252 * 2
def baseEnd_335252 : Nat := 172145416381227558708211

theorem tailTrace_335252 : CollatzResearch.WordTrace tailWord_335252 prefixEnd_335252 172145416381227558708211 := by
  unfold tailWord_335252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113822490723367664144005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8151763320964490218858673 6113822490723367664144005)
  ·
    refine ⟨1146341717010631437027001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6113822490723367664144005 1146341717010631437027001)
    ·
      refine ⟨859756287757973577770251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1146341717010631437027001 859756287757973577770251)
      ·
        refine ⟨1289634431636960366655377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859756287757973577770251 1289634431636960366655377)
        ·
          refine ⟨967225823727720274991533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289634431636960366655377 967225823727720274991533)
          ·
            refine ⟨362709683897895103121825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967225823727720274991533 362709683897895103121825)
            ·
              refine ⟨272032262923421327341369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362709683897895103121825 272032262923421327341369)
              ·
                refine ⟨204024197192565995506027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272032262923421327341369 204024197192565995506027)
                ·
                  refine ⟨306036295788848993259041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204024197192565995506027 306036295788848993259041)
                  ·
                    refine ⟨229527221841636744944281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306036295788848993259041 229527221841636744944281)
                    ·
                      refine ⟨172145416381227558708211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229527221841636744944281 172145416381227558708211)
                      ·
                        rfl

theorem cell23_335252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_335252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335252 prefixEnd_335252 := by exact prefixLift 335252
  have htrace : WordTrace (prefixWord ++ tailWord_335252) baseStart_335252 baseEnd_335252 := by
    simpa [prefixWord, tailWord_335252, baseEnd_335252] using wordTrace_append hprefix tailTrace_335252
  have hstable : (prefixWord ++ tailWord_335252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335252).length < 2 ^ (prefixWord ++ tailWord_335252).sum := by decide
  have hdescent : baseEnd_335252 < baseStart_335252 := by decide
  rcases family_descends (prefixWord ++ tailWord_335252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335290 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_335290 : Nat := 118140960795 + 335290 * 2 ^ 59
def prefixEnd_335290 : Nat := 4983230072969 + 3 ^ 40 * 335290 * 2
def baseEnd_335290 : Nat := 172164928646098410033035

theorem tailTrace_335290 : CollatzResearch.WordTrace tailWord_335290 prefixEnd_335290 172164928646098410033035 := by
  unfold tailWord_335290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057257738827266954542831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8152687303539378545447549 3057257738827266954542831)
  ·
    refine ⟨4585886608240900431814247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3057257738827266954542831 4585886608240900431814247)
    ·
      refine ⟨6878829912361350647721371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585886608240900431814247 6878829912361350647721371)
      ·
        refine ⟨10318244868542025971582057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878829912361350647721371 10318244868542025971582057)
        ·
          refine ⟨7738683651406519478686543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10318244868542025971582057 7738683651406519478686543)
          ·
            refine ⟨11608025477109779218029815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7738683651406519478686543 11608025477109779218029815)
            ·
              refine ⟨17412038215664668827044723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608025477109779218029815 17412038215664668827044723)
              ·
                refine ⟨26118057323497003240567085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17412038215664668827044723 26118057323497003240567085)
                ·
                  refine ⟨9794271496311376215212657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26118057323497003240567085 9794271496311376215212657)
                  ·
                    refine ⟨7345703622233532161409493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9794271496311376215212657 7345703622233532161409493)
                    ·
                      refine ⟨172164928646098410033035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7345703622233532161409493 172164928646098410033035)
                      ·
                        rfl

theorem cell23_335290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_335290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335290 prefixEnd_335290 := by exact prefixLift 335290
  have htrace : WordTrace (prefixWord ++ tailWord_335290) baseStart_335290 baseEnd_335290 := by
    simpa [prefixWord, tailWord_335290, baseEnd_335290] using wordTrace_append hprefix tailTrace_335290
  have hstable : (prefixWord ++ tailWord_335290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335290).length < 2 ^ (prefixWord ++ tailWord_335290).sum := by decide
  have hdescent : baseEnd_335290 < baseStart_335290 := by decide
  rcases family_descends (prefixWord ++ tailWord_335290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335307 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3]
def baseStart_335307 : Nat := 118140960795 + 335307 * 2 ^ 59
def prefixEnd_335307 : Nat := 4983230072969 + 3 ^ 40 * 335307 * 2
def baseEnd_335307 : Nat := 172173657817224843520457

theorem tailTrace_335307 : CollatzResearch.WordTrace tailWord_335307 prefixEnd_335307 172173657817224843520457 := by
  unfold tailWord_335307
  simp only [CollatzResearch.WordTrace]
  refine ⟨12229650996247479721540175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8153100664164986481026783 12229650996247479721540175)
  ·
    refine ⟨18344476494371219582310263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12229650996247479721540175 18344476494371219582310263)
    ·
      refine ⟨27516714741556829373465395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18344476494371219582310263 27516714741556829373465395)
      ·
        refine ⟨41275072112335244060198093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27516714741556829373465395 41275072112335244060198093)
        ·
          refine ⟨15478152042125716522574285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41275072112335244060198093 15478152042125716522574285)
          ·
            refine ⟨5804307015797143695965357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15478152042125716522574285 5804307015797143695965357)
            ·
              refine ⟨2176615130923928885987009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5804307015797143695965357 2176615130923928885987009)
              ·
                refine ⟨1632461348192946664490257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176615130923928885987009 1632461348192946664490257)
                ·
                  refine ⟨1224346011144709998367693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632461348192946664490257 1224346011144709998367693)
                  ·
                    refine ⟨459129754179266249387885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1224346011144709998367693 459129754179266249387885)
                    ·
                      refine ⟨172173657817224843520457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 459129754179266249387885 172173657817224843520457)
                      ·
                        rfl

theorem cell23_335307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].length) (baseStart_335307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335307 prefixEnd_335307 := by exact prefixLift 335307
  have htrace : WordTrace (prefixWord ++ tailWord_335307) baseStart_335307 baseEnd_335307 := by
    simpa [prefixWord, tailWord_335307, baseEnd_335307] using wordTrace_append hprefix tailTrace_335307
  have hstable : (prefixWord ++ tailWord_335307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335307).length < 2 ^ (prefixWord ++ tailWord_335307).sum := by decide
  have hdescent : baseEnd_335307 < baseStart_335307 := by decide
  rcases family_descends (prefixWord ++ tailWord_335307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335308 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_335308 : Nat := 118140960795 + 335308 * 2 ^ 59
def prefixEnd_335308 : Nat := 4983230072969 + 3 ^ 40 * 335308 * 2
def baseEnd_335308 : Nat := 172174171297879339607953

theorem tailTrace_335308 : CollatzResearch.WordTrace tailWord_335308 prefixEnd_335308 172174171297879339607953 := by
  unfold tailWord_335308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114843734621928446163289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8153124979495904594884385 6114843734621928446163289)
  ·
    refine ⟨4586132800966446334622467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6114843734621928446163289 4586132800966446334622467)
    ·
      refine ⟨6879199201449669501933701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4586132800966446334622467 6879199201449669501933701)
      ·
        refine ⟨1289849850271813031612569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6879199201449669501933701 1289849850271813031612569)
        ·
          refine ⟨967387387703859773709427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289849850271813031612569 967387387703859773709427)
          ·
            refine ⟨1451081081555789660564141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967387387703859773709427 1451081081555789660564141)
            ·
              refine ⟨544155405583421122711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451081081555789660564141 544155405583421122711553)
              ·
                refine ⟨408116554187565842033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544155405583421122711553 408116554187565842033665)
                ·
                  refine ⟨306087415640674381525249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408116554187565842033665 306087415640674381525249)
                  ·
                    refine ⟨229565561730505786143937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306087415640674381525249 229565561730505786143937)
                    ·
                      refine ⟨172174171297879339607953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229565561730505786143937 172174171297879339607953)
                      ·
                        rfl

theorem cell23_335308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_335308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335308 prefixEnd_335308 := by exact prefixLift 335308
  have htrace : WordTrace (prefixWord ++ tailWord_335308) baseStart_335308 baseEnd_335308 := by
    simpa [prefixWord, tailWord_335308, baseEnd_335308] using wordTrace_append hprefix tailTrace_335308
  have hstable : (prefixWord ++ tailWord_335308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335308).length < 2 ^ (prefixWord ++ tailWord_335308).sum := by decide
  have hdescent : baseEnd_335308 < baseStart_335308 := by decide
  rcases family_descends (prefixWord ++ tailWord_335308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335325 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_335325 : Nat := 118140960795 + 335325 * 2 ^ 59
def prefixEnd_335325 : Nat := 4983230072969 + 3 ^ 40 * 335325 * 2
def baseEnd_335325 : Nat := 172182900469005773095375

theorem tailTrace_335325 : CollatzResearch.WordTrace tailWord_335325 prefixEnd_335325 172182900469005773095375 := by
  unfold tailWord_335325
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230307510182268795695429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8153538340121512530463619 12230307510182268795695429)
  ·
    refine ⟨2293182658159175399192893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12230307510182268795695429 2293182658159175399192893)
    ·
      refine ⟨859943496809690774697335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2293182658159175399192893 859943496809690774697335)
      ·
        refine ⟨1289915245214536162046003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859943496809690774697335 1289915245214536162046003)
        ·
          refine ⟨1934872867821804243069005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289915245214536162046003 1934872867821804243069005)
          ·
            refine ⟨725577325433176591150877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934872867821804243069005 725577325433176591150877)
            ·
              refine ⟨272091497037441221681579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725577325433176591150877 272091497037441221681579)
              ·
                refine ⟨408137245556161832522369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272091497037441221681579 408137245556161832522369)
                ·
                  refine ⟨306102934167121374391777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408137245556161832522369 306102934167121374391777)
                  ·
                    refine ⟨229577200625341030793833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306102934167121374391777 229577200625341030793833)
                    ·
                      refine ⟨172182900469005773095375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229577200625341030793833 172182900469005773095375)
                      ·
                        rfl

theorem cell23_335325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_335325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335325 prefixEnd_335325 := by exact prefixLift 335325
  have htrace : WordTrace (prefixWord ++ tailWord_335325) baseStart_335325 baseEnd_335325 := by
    simpa [prefixWord, tailWord_335325, baseEnd_335325] using wordTrace_append hprefix tailTrace_335325
  have hstable : (prefixWord ++ tailWord_335325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335325).length < 2 ^ (prefixWord ++ tailWord_335325).sum := by decide
  have hdescent : baseEnd_335325 < baseStart_335325 := by decide
  rcases family_descends (prefixWord ++ tailWord_335325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335421 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 6]
def baseStart_335421 : Nat := 118140960795 + 335421 * 2 ^ 59
def prefixEnd_335421 : Nat := 4983230072969 + 3 ^ 40 * 335421 * 2
def baseEnd_335421 : Nat := 19136910512426377499437

theorem tailTrace_335421 : CollatzResearch.WordTrace tailWord_335421 prefixEnd_335421 19136910512426377499437 := by
  unfold tailWord_335421
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233808917834477191190117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8155872611889651460793411 12233808917834477191190117)
  ·
    refine ⟨2293839172093964473348147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12233808917834477191190117 2293839172093964473348147)
    ·
      refine ⟨3440758758140946710022221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293839172093964473348147 3440758758140946710022221)
      ·
        refine ⟨1290284534302855016258333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3440758758140946710022221 1290284534302855016258333)
        ·
          refine ⟨483856700363570631096875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1290284534302855016258333 483856700363570631096875)
          ·
            refine ⟨725785050545355946645313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483856700363570631096875 725785050545355946645313)
            ·
              refine ⟨544338787909016959983985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725785050545355946645313 544338787909016959983985)
              ·
                refine ⟨408254090931762719987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544338787909016959983985 408254090931762719987989)
                ·
                  refine ⟨19136910512426377499437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 408254090931762719987989 19136910512426377499437)
                  ·
                    rfl

theorem cell23_335421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_335421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335421 prefixEnd_335421 := by exact prefixLift 335421
  have htrace : WordTrace (prefixWord ++ tailWord_335421) baseStart_335421 baseEnd_335421 := by
    simpa [prefixWord, tailWord_335421, baseEnd_335421] using wordTrace_append hprefix tailTrace_335421
  have hstable : (prefixWord ++ tailWord_335421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335421).length < 2 ^ (prefixWord ++ tailWord_335421).sum := by decide
  have hdescent : baseEnd_335421 < baseStart_335421 := by decide
  rcases family_descends (prefixWord ++ tailWord_335421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335424 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2]
def baseStart_335424 : Nat := 118140960795 + 335424 * 2 ^ 59
def prefixEnd_335424 : Nat := 4983230072969 + 3 ^ 40 * 335424 * 2
def baseEnd_335424 : Nat := 172233735053800885757419

theorem tailTrace_335424 : CollatzResearch.WordTrace tailWord_335424 prefixEnd_335424 172233735053800885757419 := by
  unfold tailWord_335424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6116959168411804351774663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8155945557882405802366217 6116959168411804351774663)
  ·
    refine ⟨9175438752617706527661995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6116959168411804351774663 9175438752617706527661995)
    ·
      refine ⟨13763158128926559791492993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175438752617706527661995 13763158128926559791492993)
      ·
        refine ⟨10322368596694919843619745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13763158128926559791492993 10322368596694919843619745)
        ·
          refine ⟨7741776447521189882714809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10322368596694919843619745 7741776447521189882714809)
          ·
            refine ⟨5806332335640892412036107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741776447521189882714809 5806332335640892412036107)
            ·
              refine ⟨8709498503461338618054161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806332335640892412036107 8709498503461338618054161)
              ·
                refine ⟨6532123877596003963540621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8709498503461338618054161 6532123877596003963540621)
                ·
                  refine ⟨2449546454098501486327733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6532123877596003963540621 2449546454098501486327733)
                  ·
                    refine ⟨229644980071734514343225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2449546454098501486327733 229644980071734514343225)
                    ·
                      refine ⟨172233735053800885757419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229644980071734514343225 172233735053800885757419)
                      ·
                        rfl

theorem cell23_335424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_335424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335424 prefixEnd_335424 := by exact prefixLift 335424
  have htrace : WordTrace (prefixWord ++ tailWord_335424) baseStart_335424 baseEnd_335424 := by
    simpa [prefixWord, tailWord_335424, baseEnd_335424] using wordTrace_append hprefix tailTrace_335424
  have hstable : (prefixWord ++ tailWord_335424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335424).length < 2 ^ (prefixWord ++ tailWord_335424).sum := by decide
  have hdescent : baseEnd_335424 < baseStart_335424 := by decide
  rcases family_descends (prefixWord ++ tailWord_335424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335467 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_335467 : Nat := 118140960795 + 335467 * 2 ^ 59
def prefixEnd_335467 : Nat := 4983230072969 + 3 ^ 40 * 335467 * 2
def baseEnd_335467 : Nat := 172255814721944217519721

theorem tailTrace_335467 : CollatzResearch.WordTrace tailWord_335467 prefixEnd_335467 172255814721944217519721 := by
  unfold tailWord_335467
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235486675667827047364655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8156991117111884698243103 12235486675667827047364655)
  ·
    refine ⟨18353230013501740571046983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12235486675667827047364655 18353230013501740571046983)
    ·
      refine ⟨27529845020252610856570475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18353230013501740571046983 27529845020252610856570475)
      ·
        refine ⟨41294767530378916284855713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27529845020252610856570475 41294767530378916284855713)
        ·
          refine ⟨30971075647784187213641785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41294767530378916284855713 30971075647784187213641785)
          ·
            refine ⟨23228306735838140410231339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30971075647784187213641785 23228306735838140410231339)
            ·
              refine ⟨34842460103757210615347009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23228306735838140410231339 34842460103757210615347009)
              ·
                refine ⟨26131845077817907961510257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34842460103757210615347009 26131845077817907961510257)
                ·
                  refine ⟨19598883808363430971132693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26131845077817907961510257 19598883808363430971132693)
                  ·
                    refine ⟨918697678517035826771845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19598883808363430971132693 918697678517035826771845)
                    ·
                      refine ⟨172255814721944217519721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 918697678517035826771845 172255814721944217519721)
                      ·
                        rfl

theorem cell23_335467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_335467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335467 prefixEnd_335467 := by exact prefixLift 335467
  have htrace : WordTrace (prefixWord ++ tailWord_335467) baseStart_335467 baseEnd_335467 := by
    simpa [prefixWord, tailWord_335467, baseEnd_335467] using wordTrace_append hprefix tailTrace_335467
  have hstable : (prefixWord ++ tailWord_335467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335467).length < 2 ^ (prefixWord ++ tailWord_335467).sum := by decide
  have hdescent : baseEnd_335467 < baseStart_335467 := by decide
  rcases family_descends (prefixWord ++ tailWord_335467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335471 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 7, 2, 2]
def baseStart_335471 : Nat := 118140960795 + 335471 * 2 ^ 59
def prefixEnd_335471 : Nat := 4983230072969 + 3 ^ 40 * 335471 * 2
def baseEnd_335471 : Nat := 172257868644562201869703

theorem tailTrace_335471 : CollatzResearch.WordTrace tailWord_335471 prefixEnd_335471 172257868644562201869703 := by
  unfold tailWord_335471
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235632567653335730510267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8157088378435557153673511 12235632567653335730510267)
  ·
    refine ⟨18353448851480003595765401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12235632567653335730510267 18353448851480003595765401)
    ·
      refine ⟨13765086638610002696824051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18353448851480003595765401 13765086638610002696824051)
      ·
        refine ⟨20647629957915004045236077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13765086638610002696824051 20647629957915004045236077)
        ·
          refine ⟨7742861234218126516963529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20647629957915004045236077 7742861234218126516963529)
          ·
            refine ⟨5807145925663594887722647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7742861234218126516963529 5807145925663594887722647)
            ·
              refine ⟨8710718888495392331583971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807145925663594887722647 8710718888495392331583971)
              ·
                refine ⟨13066078332743088497375957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8710718888495392331583971 13066078332743088497375957)
                ·
                  refine ⟨306236210923666136657249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13066078332743088497375957 306236210923666136657249)
                  ·
                    refine ⟨229677158192749602492937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306236210923666136657249 229677158192749602492937)
                    ·
                      refine ⟨172257868644562201869703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229677158192749602492937 172257868644562201869703)
                      ·
                        rfl

theorem cell23_335471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 2, 2].length) (baseStart_335471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335471 prefixEnd_335471 := by exact prefixLift 335471
  have htrace : WordTrace (prefixWord ++ tailWord_335471) baseStart_335471 baseEnd_335471 := by
    simpa [prefixWord, tailWord_335471, baseEnd_335471] using wordTrace_append hprefix tailTrace_335471
  have hstable : (prefixWord ++ tailWord_335471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335471).length < 2 ^ (prefixWord ++ tailWord_335471).sum := by decide
  have hdescent : baseEnd_335471 < baseStart_335471 := by decide
  rcases family_descends (prefixWord ++ tailWord_335471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335488 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2]
def baseStart_335488 : Nat := 118140960795 + 335488 * 2 ^ 59
def prefixEnd_335488 : Nat := 4983230072969 + 3 ^ 40 * 335488 * 2
def baseEnd_335488 : Nat := 172266597815688635357125

theorem tailTrace_335488 : CollatzResearch.WordTrace tailWord_335488 prefixEnd_335488 172266597815688635357125 := by
  unfold tailWord_335488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118126304295873816939559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8157501739061165089252745 6118126304295873816939559)
  ·
    refine ⟨9177189456443810725409339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118126304295873816939559 9177189456443810725409339)
    ·
      refine ⟨13765784184665716088114009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9177189456443810725409339 13765784184665716088114009)
      ·
        refine ⟨10324338138499287066085507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13765784184665716088114009 10324338138499287066085507)
        ·
          refine ⟨15486507207748930599128261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10324338138499287066085507 15486507207748930599128261)
          ·
            refine ⟨2903720101452924487336549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15486507207748930599128261 2903720101452924487336549)
            ·
              refine ⟨544447519022423341375603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2903720101452924487336549 544447519022423341375603)
              ·
                refine ⟨816671278533635012063405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544447519022423341375603 816671278533635012063405)
                ·
                  refine ⟨306251729450113129523777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816671278533635012063405 306251729450113129523777)
                  ·
                    refine ⟨229688797087584847142833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306251729450113129523777 229688797087584847142833)
                    ·
                      refine ⟨172266597815688635357125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229688797087584847142833 172266597815688635357125)
                      ·
                        rfl

theorem cell23_335488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_335488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335488 prefixEnd_335488 := by exact prefixLift 335488
  have htrace : WordTrace (prefixWord ++ tailWord_335488) baseStart_335488 baseEnd_335488 := by
    simpa [prefixWord, tailWord_335488, baseEnd_335488] using wordTrace_append hprefix tailTrace_335488
  have hstable : (prefixWord ++ tailWord_335488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335488).length < 2 ^ (prefixWord ++ tailWord_335488).sum := by decide
  have hdescent : baseEnd_335488 < baseStart_335488 := by decide
  rcases family_descends (prefixWord ++ tailWord_335488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335511 : List Nat := [1, 1, 3, 3, 2, 4, 2, 7]
def baseStart_335511 : Nat := 118140960795 + 335511 * 2 ^ 59
def prefixEnd_335511 : Nat := 4983230072969 + 3 ^ 40 * 335511 * 2
def baseEnd_335511 : Nat := 6380681772990446124797

theorem tailTrace_335511 : CollatzResearch.WordTrace tailWord_335511 prefixEnd_335511 6380681772990446124797 := by
  unfold tailWord_335511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237091487508422561966387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8158060991672281707977591 12237091487508422561966387)
  ·
    refine ⟨18355637231262633842949581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12237091487508422561966387 18355637231262633842949581)
    ·
      refine ⟨6883363961723487691106093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18355637231262633842949581 6883363961723487691106093)
      ·
        refine ⟨2581261485646307884164785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6883363961723487691106093 2581261485646307884164785)
        ·
          refine ⟨1935946114234730913123589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581261485646307884164785 1935946114234730913123589)
          ·
            refine ⟨362989896419012046210673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1935946114234730913123589 362989896419012046210673)
            ·
              refine ⟨272242422314259034658005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362989896419012046210673 272242422314259034658005)
              ·
                refine ⟨6380681772990446124797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 272242422314259034658005 6380681772990446124797)
                ·
                  rfl

theorem cell23_335511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 7].length) (baseStart_335511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335511 prefixEnd_335511 := by exact prefixLift 335511
  have htrace : WordTrace (prefixWord ++ tailWord_335511) baseStart_335511 baseEnd_335511 := by
    simpa [prefixWord, tailWord_335511, baseEnd_335511] using wordTrace_append hprefix tailTrace_335511
  have hstable : (prefixWord ++ tailWord_335511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335511).length < 2 ^ (prefixWord ++ tailWord_335511).sum := by decide
  have hdescent : baseEnd_335511 < baseStart_335511 := by decide
  rcases family_descends (prefixWord ++ tailWord_335511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335578 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_335578 : Nat := 118140960795 + 335578 * 2 ^ 59
def prefixEnd_335578 : Nat := 4983230072969 + 3 ^ 40 * 335578 * 2
def baseEnd_335578 : Nat := 172312811074593283231711

theorem tailTrace_335578 : CollatzResearch.WordTrace tailWord_335578 prefixEnd_335578 172312811074593283231711 := by
  unfold tailWord_335578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059883794566423251163847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8159690118843795336436925 3059883794566423251163847)
  ·
    refine ⟨4589825691849634876745771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059883794566423251163847 4589825691849634876745771)
    ·
      refine ⟨6884738537774452315118657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589825691849634876745771 6884738537774452315118657)
      ·
        refine ⟨5163553903330839236338993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884738537774452315118657 5163553903330839236338993)
        ·
          refine ⟨3872665427498129427254245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163553903330839236338993 3872665427498129427254245)
          ·
            refine ⟨726124767655899267610171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3872665427498129427254245 726124767655899267610171)
            ·
              refine ⟨1089187151483848901415257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726124767655899267610171 1089187151483848901415257)
              ·
                refine ⟨816890363612886676061443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089187151483848901415257 816890363612886676061443)
                ·
                  refine ⟨1225335545419330014092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816890363612886676061443 1225335545419330014092165)
                  ·
                    refine ⟨229750414766124377642281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1225335545419330014092165 229750414766124377642281)
                    ·
                      refine ⟨172312811074593283231711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229750414766124377642281 172312811074593283231711)
                      ·
                        rfl

theorem cell23_335578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_335578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335578 prefixEnd_335578 := by exact prefixLift 335578
  have htrace : WordTrace (prefixWord ++ tailWord_335578) baseStart_335578 baseEnd_335578 := by
    simpa [prefixWord, tailWord_335578, baseEnd_335578] using wordTrace_append hprefix tailTrace_335578
  have hstable : (prefixWord ++ tailWord_335578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335578).length < 2 ^ (prefixWord ++ tailWord_335578).sum := by decide
  have hdescent : baseEnd_335578 < baseStart_335578 := by decide
  rcases family_descends (prefixWord ++ tailWord_335578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335594 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_335594 : Nat := 118140960795 + 335594 * 2 ^ 59
def prefixEnd_335594 : Nat := 4983230072969 + 3 ^ 40 * 335594 * 2
def baseEnd_335594 : Nat := 172321026765065220631637

theorem tailTrace_335594 : CollatzResearch.WordTrace tailWord_335594 prefixEnd_335594 172321026765065220631637 := by
  unfold tailWord_335594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060029686551931934309459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8160079164138485158158557 3060029686551931934309459)
  ·
    refine ⟨4590044529827897901464189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060029686551931934309459 4590044529827897901464189)
    ·
      refine ⟨1721266698685461713049071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4590044529827897901464189 1721266698685461713049071)
      ·
        refine ⟨2581900048028192569573607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721266698685461713049071 2581900048028192569573607)
        ·
          refine ⟨3872850072042288854360411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581900048028192569573607 3872850072042288854360411)
          ·
            refine ⟨5809275108063433281540617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872850072042288854360411 5809275108063433281540617)
            ·
              refine ⟨4356956331047574961155463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5809275108063433281540617 4356956331047574961155463)
              ·
                refine ⟨6535434496571362441733195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356956331047574961155463 6535434496571362441733195)
                ·
                  refine ⟨9803151744857043662599793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535434496571362441733195 9803151744857043662599793)
                  ·
                    refine ⟨7352363808642782746949845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9803151744857043662599793 7352363808642782746949845)
                    ·
                      refine ⟨172321026765065220631637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7352363808642782746949845 172321026765065220631637)
                      ·
                        rfl

theorem cell23_335594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_335594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335594 prefixEnd_335594 := by exact prefixLift 335594
  have htrace : WordTrace (prefixWord ++ tailWord_335594) baseStart_335594 baseEnd_335594 := by
    simpa [prefixWord, tailWord_335594, baseEnd_335594] using wordTrace_append hprefix tailTrace_335594
  have hstable : (prefixWord ++ tailWord_335594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335594).length < 2 ^ (prefixWord ++ tailWord_335594).sum := by decide
  have hdescent : baseEnd_335594 < baseStart_335594 := by decide
  rcases family_descends (prefixWord ++ tailWord_335594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335651 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4]
def baseStart_335651 : Nat := 118140960795 + 335651 * 2 ^ 59
def prefixEnd_335651 : Nat := 4983230072969 + 3 ^ 40 * 335651 * 2
def baseEnd_335651 : Nat := 172350295162371497618875

theorem tailTrace_335651 : CollatzResearch.WordTrace tailWord_335651 prefixEnd_335651 172350295162371497618875 := by
  unfold tailWord_335651
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242197707001226472062807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8161465138000817648041871 12242197707001226472062807)
  ·
    refine ⟨18363296560501839708094211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242197707001226472062807 18363296560501839708094211)
    ·
      refine ⟨27544944840752759562141317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18363296560501839708094211 27544944840752759562141317)
      ·
        refine ⟨5164677157641142417901497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27544944840752759562141317 5164677157641142417901497)
        ·
          refine ⟨3873507868230856813426123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5164677157641142417901497 3873507868230856813426123)
          ·
            refine ⟨5810261802346285220139185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873507868230856813426123 5810261802346285220139185)
            ·
              refine ⟨4357696351759713915104389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810261802346285220139185 4357696351759713915104389)
              ·
                refine ⟨817068065954946359082073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4357696351759713915104389 817068065954946359082073)
                ·
                  refine ⟨612801049466209769311555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817068065954946359082073 612801049466209769311555)
                  ·
                    refine ⟨919201574199314653967333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 612801049466209769311555 919201574199314653967333)
                    ·
                      refine ⟨172350295162371497618875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 919201574199314653967333 172350295162371497618875)
                      ·
                        rfl

theorem cell23_335651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_335651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335651 prefixEnd_335651 := by exact prefixLift 335651
  have htrace : WordTrace (prefixWord ++ tailWord_335651) baseStart_335651 baseEnd_335651 := by
    simpa [prefixWord, tailWord_335651, baseEnd_335651] using wordTrace_append hprefix tailTrace_335651
  have hstable : (prefixWord ++ tailWord_335651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335651).length < 2 ^ (prefixWord ++ tailWord_335651).sum := by decide
  have hdescent : baseEnd_335651 < baseStart_335651 := by decide
  rcases family_descends (prefixWord ++ tailWord_335651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335668 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_335668 : Nat := 118140960795 + 335668 * 2 ^ 59
def prefixEnd_335668 : Nat := 4983230072969 + 3 ^ 40 * 335668 * 2
def baseEnd_335668 : Nat := 172359024333497931106297

theorem tailTrace_335668 : CollatzResearch.WordTrace tailWord_335668 prefixEnd_335668 172359024333497931106297 := by
  unfold tailWord_335668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121408873969819187715829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8161878498626425583621105 6121408873969819187715829)
  ·
    refine ⟨573882081934670548848359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6121408873969819187715829 573882081934670548848359)
    ·
      refine ⟨860823122902005823272539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573882081934670548848359 860823122902005823272539)
      ·
        refine ⟨1291234684353008734908809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860823122902005823272539 1291234684353008734908809)
        ·
          refine ⟨968426013264756551181607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291234684353008734908809 968426013264756551181607)
          ·
            refine ⟨1452639019897134826772411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968426013264756551181607 1452639019897134826772411)
            ·
              refine ⟨2178958529845702240158617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452639019897134826772411 2178958529845702240158617)
              ·
                refine ⟨1634218897384276680118963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178958529845702240158617 1634218897384276680118963)
                ·
                  refine ⟨2451328346076415020178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634218897384276680118963 2451328346076415020178445)
                  ·
                    refine ⟨919248129778655632566917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451328346076415020178445 919248129778655632566917)
                    ·
                      refine ⟨172359024333497931106297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 919248129778655632566917 172359024333497931106297)
                      ·
                        rfl

theorem cell23_335668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_335668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335668 prefixEnd_335668 := by exact prefixLift 335668
  have htrace : WordTrace (prefixWord ++ tailWord_335668) baseStart_335668 baseEnd_335668 := by
    simpa [prefixWord, tailWord_335668, baseEnd_335668] using wordTrace_append hprefix tailTrace_335668
  have hstable : (prefixWord ++ tailWord_335668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335668).length < 2 ^ (prefixWord ++ tailWord_335668).sum := by decide
  have hdescent : baseEnd_335668 < baseStart_335668 := by decide
  rcases family_descends (prefixWord ++ tailWord_335668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335671 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_335671 : Nat := 118140960795 + 335671 * 2 ^ 59
def prefixEnd_335671 : Nat := 4983230072969 + 3 ^ 40 * 335671 * 2
def baseEnd_335671 : Nat := 172360564775461419368783

theorem tailTrace_335671 : CollatzResearch.WordTrace tailWord_335671 prefixEnd_335671 172360564775461419368783 := by
  unfold tailWord_335671
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242927166928769887790867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8161951444619179925193911 12242927166928769887790867)
  ·
    refine ⟨18364390750393154831686301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242927166928769887790867 18364390750393154831686301)
    ·
      refine ⟨6886646531397433061882363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18364390750393154831686301 6886646531397433061882363)
      ·
        refine ⟨10329969797096149592823545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886646531397433061882363 10329969797096149592823545)
        ·
          refine ⟨7747477347822112194617659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10329969797096149592823545 7747477347822112194617659)
          ·
            refine ⟨11621216021733168291926489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747477347822112194617659 11621216021733168291926489)
            ·
              refine ⟨8715912016299876218944867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11621216021733168291926489 8715912016299876218944867)
              ·
                refine ⟨13073868024449814328417301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8715912016299876218944867 13073868024449814328417301)
                ·
                  refine ⟨612837563646085046644561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13073868024449814328417301 612837563646085046644561)
                  ·
                    refine ⟨459628172734563784983421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 612837563646085046644561 459628172734563784983421)
                    ·
                      refine ⟨172360564775461419368783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 459628172734563784983421 172360564775461419368783)
                      ·
                        rfl

theorem cell23_335671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_335671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335671 prefixEnd_335671 := by exact prefixLift 335671
  have htrace : WordTrace (prefixWord ++ tailWord_335671) baseStart_335671 baseEnd_335671 := by
    simpa [prefixWord, tailWord_335671, baseEnd_335671] using wordTrace_append hprefix tailTrace_335671
  have hstable : (prefixWord ++ tailWord_335671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335671).length < 2 ^ (prefixWord ++ tailWord_335671).sum := by decide
  have hdescent : baseEnd_335671 < baseStart_335671 := by decide
  rcases family_descends (prefixWord ++ tailWord_335671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335712 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 1, 4]
def baseStart_335712 : Nat := 118140960795 + 335712 * 2 ^ 59
def prefixEnd_335712 : Nat := 4983230072969 + 3 ^ 40 * 335712 * 2
def baseEnd_335712 : Nat := 57460539160765252985365

theorem tailTrace_335712 : CollatzResearch.WordTrace tailWord_335712 prefixEnd_335712 57460539160765252985365 := by
  unfold tailWord_335712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122211279890116945016695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8162948373186822593355593 6122211279890116945016695)
  ·
    refine ⟨9183316919835175417525043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122211279890116945016695 9183316919835175417525043)
    ·
      refine ⟨13774975379752763126287565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183316919835175417525043 13774975379752763126287565)
      ·
        refine ⟨5165615767407286172357837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13774975379752763126287565 5165615767407286172357837)
        ·
          refine ⟨1937105912777732314634189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5165615767407286172357837 1937105912777732314634189)
          ·
            refine ⟨726414717291649617987821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1937105912777732314634189 726414717291649617987821)
            ·
              refine ⟨272405518984368606745433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726414717291649617987821 272405518984368606745433)
              ·
                refine ⟨204304139238276455059075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272405518984368606745433 204304139238276455059075)
                ·
                  refine ⟨306456208857414682588613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204304139238276455059075 306456208857414682588613)
                  ·
                    refine ⟨57460539160765252985365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 306456208857414682588613 57460539160765252985365)
                    ·
                      rfl

theorem cell23_335712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_335712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335712 prefixEnd_335712 := by exact prefixLift 335712
  have htrace : WordTrace (prefixWord ++ tailWord_335712) baseStart_335712 baseEnd_335712 := by
    simpa [prefixWord, tailWord_335712, baseEnd_335712] using wordTrace_append hprefix tailTrace_335712
  have hstable : (prefixWord ++ tailWord_335712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335712).length < 2 ^ (prefixWord ++ tailWord_335712).sum := by decide
  have hdescent : baseEnd_335712 < baseStart_335712 := by decide
  rcases family_descends (prefixWord ++ tailWord_335712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335728 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2]
def baseStart_335728 : Nat := 118140960795 + 335728 * 2 ^ 59
def prefixEnd_335728 : Nat := 4983230072969 + 3 ^ 40 * 335728 * 2
def baseEnd_335728 : Nat := 172389833172767696356021

theorem tailTrace_335728 : CollatzResearch.WordTrace tailWord_335728 prefixEnd_335728 172389833172767696356021 := by
  unfold tailWord_335728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122503063861134311307919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8163337418481512415077225 6122503063861134311307919)
  ·
    refine ⟨9183754595791701466961879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122503063861134311307919 9183754595791701466961879)
    ·
      refine ⟨13775631893687552200442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183754595791701466961879 13775631893687552200442819)
      ·
        refine ⟨20663447840531328300664229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775631893687552200442819 20663447840531328300664229)
        ·
          refine ⟨3874396470099624056374543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20663447840531328300664229 3874396470099624056374543)
          ·
            refine ⟨5811594705149436084561815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874396470099624056374543 5811594705149436084561815)
            ·
              refine ⟨8717392057724154126842723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811594705149436084561815 8717392057724154126842723)
              ·
                refine ⟨13076088086586231190264085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717392057724154126842723 13076088086586231190264085)
                ·
                  refine ⟨612941629058729587043629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13076088086586231190264085 612941629058729587043629)
                  ·
                    refine ⟨229853110897023595141361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 612941629058729587043629 229853110897023595141361)
                    ·
                      refine ⟨172389833172767696356021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229853110897023595141361 172389833172767696356021)
                      ·
                        rfl

theorem cell23_335728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2].length) (baseStart_335728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335728 prefixEnd_335728 := by exact prefixLift 335728
  have htrace : WordTrace (prefixWord ++ tailWord_335728) baseStart_335728 baseEnd_335728 := by
    simpa [prefixWord, tailWord_335728, baseEnd_335728] using wordTrace_append hprefix tailTrace_335728
  have hstable : (prefixWord ++ tailWord_335728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335728).length < 2 ^ (prefixWord ++ tailWord_335728).sum := by decide
  have hdescent : baseEnd_335728 < baseStart_335728 := by decide
  rcases family_descends (prefixWord ++ tailWord_335728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335738 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_335738 : Nat := 118140960795 + 335738 * 2 ^ 59
def prefixEnd_335738 : Nat := 4983230072969 + 3 ^ 40 * 335738 * 2
def baseEnd_335738 : Nat := 57464989326437552410325

theorem tailTrace_335738 : CollatzResearch.WordTrace tailWord_335738 prefixEnd_335738 57464989326437552410325 := by
  unfold tailWord_335738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061342714421510082619967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8163580571790693553653245 3061342714421510082619967)
  ·
    refine ⟨4592014071632265123929951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3061342714421510082619967 4592014071632265123929951)
    ·
      refine ⟨6888021107448397685894927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592014071632265123929951 6888021107448397685894927)
      ·
        refine ⟨10332031661172596528842391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888021107448397685894927 10332031661172596528842391)
        ·
          refine ⟨15498047491758894793263587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332031661172596528842391 15498047491758894793263587)
          ·
            refine ⟨23247071237638342189895381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15498047491758894793263587 23247071237638342189895381)
            ·
              refine ⟨544853232132148645075673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23247071237638342189895381 544853232132148645075673)
              ·
                refine ⟨408639924099111483806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544853232132148645075673 408639924099111483806755)
                ·
                  refine ⟨612959886148667225710133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408639924099111483806755 612959886148667225710133)
                  ·
                    refine ⟨57464989326437552410325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 612959886148667225710133 57464989326437552410325)
                    ·
                      rfl

theorem cell23_335738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_335738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335738 prefixEnd_335738 := by exact prefixLift 335738
  have htrace : WordTrace (prefixWord ++ tailWord_335738) baseStart_335738 baseEnd_335738 := by
    simpa [prefixWord, tailWord_335738, baseEnd_335738] using wordTrace_append hprefix tailTrace_335738
  have hstable : (prefixWord ++ tailWord_335738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335738).length < 2 ^ (prefixWord ++ tailWord_335738).sum := by decide
  have hdescent : baseEnd_335738 < baseStart_335738 := by decide
  rcases family_descends (prefixWord ++ tailWord_335738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335762 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_335762 : Nat := 118140960795 + 335762 * 2 ^ 59
def prefixEnd_335762 : Nat := 4983230072969 + 3 ^ 40 * 335762 * 2
def baseEnd_335762 : Nat := 172407291515020563330865

theorem tailTrace_335762 : CollatzResearch.WordTrace tailWord_335762 prefixEnd_335762 172407291515020563330865 := by
  unfold tailWord_335762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061561552399773107338385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8164164139732728286235693 3061561552399773107338385)
  ·
    refine ⟨2296171164299829830503789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3061561552399773107338385 2296171164299829830503789)
    ·
      refine ⟨861064186612436186438921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2296171164299829830503789 861064186612436186438921)
      ·
        refine ⟨645798139959327139829191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 861064186612436186438921 645798139959327139829191)
        ·
          refine ⟨968697209938990709743787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645798139959327139829191 968697209938990709743787)
          ·
            refine ⟨1453045814908486064615681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968697209938990709743787 1453045814908486064615681)
            ·
              refine ⟨1089784361181364548461761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453045814908486064615681 1089784361181364548461761)
              ·
                refine ⟨817338270886023411346321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089784361181364548461761 817338270886023411346321)
                ·
                  refine ⟨613003703164517558509741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817338270886023411346321 613003703164517558509741)
                  ·
                    refine ⟨229876388686694084441153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613003703164517558509741 229876388686694084441153)
                    ·
                      refine ⟨172407291515020563330865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229876388686694084441153 172407291515020563330865)
                      ·
                        rfl

theorem cell23_335762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_335762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335762 prefixEnd_335762 := by exact prefixLift 335762
  have htrace : WordTrace (prefixWord ++ tailWord_335762) baseStart_335762 baseEnd_335762 := by
    simpa [prefixWord, tailWord_335762, baseEnd_335762] using wordTrace_append hprefix tailTrace_335762
  have hstable : (prefixWord ++ tailWord_335762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335762).length < 2 ^ (prefixWord ++ tailWord_335762).sum := by decide
  have hdescent : baseEnd_335762 < baseStart_335762 := by decide
  rcases family_descends (prefixWord ++ tailWord_335762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335796 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_335796 : Nat := 118140960795 + 335796 * 2 ^ 59
def prefixEnd_335796 : Nat := 4983230072969 + 3 ^ 40 * 335796 * 2
def baseEnd_335796 : Nat := 172424749857273430305709

theorem tailTrace_335796 : CollatzResearch.WordTrace tailWord_335796 prefixEnd_335796 172424749857273430305709 := by
  unfold tailWord_335796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123743145737958118045621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8164990860983944157394161 6123743145737958118045621)
  ·
    refine ⟨574100919912933573566777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6123743145737958118045621 574100919912933573566777)
    ·
      refine ⟨430575689934700180175083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574100919912933573566777 430575689934700180175083)
      ·
        refine ⟨645863534902050270262625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430575689934700180175083 645863534902050270262625)
        ·
          refine ⟨484397651176537702696969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645863534902050270262625 484397651176537702696969)
          ·
            refine ⟨363298238382403277022727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484397651176537702696969 363298238382403277022727)
            ·
              refine ⟨544947357573604915534091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363298238382403277022727 544947357573604915534091)
              ·
                refine ⟨817421036360407373301137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544947357573604915534091 817421036360407373301137)
                ·
                  refine ⟨613065777270305529975853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 817421036360407373301137 613065777270305529975853)
                  ·
                    refine ⟨229899666476364573740945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613065777270305529975853 229899666476364573740945)
                    ·
                      refine ⟨172424749857273430305709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 229899666476364573740945 172424749857273430305709)
                      ·
                        rfl

theorem cell23_335796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_335796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335796 prefixEnd_335796 := by exact prefixLift 335796
  have htrace : WordTrace (prefixWord ++ tailWord_335796) baseStart_335796 baseEnd_335796 := by
    simpa [prefixWord, tailWord_335796, baseEnd_335796] using wordTrace_append hprefix tailTrace_335796
  have hstable : (prefixWord ++ tailWord_335796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335796).length < 2 ^ (prefixWord ++ tailWord_335796).sum := by decide
  have hdescent : baseEnd_335796 < baseStart_335796 := by decide
  rcases family_descends (prefixWord ++ tailWord_335796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335808 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_335808 : Nat := 118140960795 + 335808 * 2 ^ 59
def prefixEnd_335808 : Nat := 4983230072969 + 3 ^ 40 * 335808 * 2
def baseEnd_335808 : Nat := 172430911625127383355653

theorem tailTrace_335808 : CollatzResearch.WordTrace tailWord_335808 prefixEnd_335808 172430911625127383355653 := by
  unfold tailWord_335808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123961983716221142764039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8165282644954961523685385 6123961983716221142764039)
  ·
    refine ⟨9185942975574331714146059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123961983716221142764039 9185942975574331714146059)
    ·
      refine ⟨13778914463361497571219089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185942975574331714146059 13778914463361497571219089)
      ·
        refine ⟨10334185847521123178414317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13778914463361497571219089 10334185847521123178414317)
        ·
          refine ⟨3875319692820421191905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10334185847521123178414317 3875319692820421191905369)
          ·
            refine ⟨2906489769615315893929027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875319692820421191905369 2906489769615315893929027)
            ·
              refine ⟨4359734654422973840893541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906489769615315893929027 4359734654422973840893541)
              ·
                refine ⟨817450247704307595167539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4359734654422973840893541 817450247704307595167539)
                ·
                  refine ⟨1226175371556461392751309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817450247704307595167539 1226175371556461392751309)
                  ·
                    refine ⟨459815764333673022281741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1226175371556461392751309 459815764333673022281741)
                    ·
                      refine ⟨172430911625127383355653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 459815764333673022281741 172430911625127383355653)
                      ·
                        rfl

theorem cell23_335808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_335808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335808 prefixEnd_335808 := by exact prefixLift 335808
  have htrace : WordTrace (prefixWord ++ tailWord_335808) baseStart_335808 baseEnd_335808 := by
    simpa [prefixWord, tailWord_335808, baseEnd_335808] using wordTrace_append hprefix tailTrace_335808
  have hstable : (prefixWord ++ tailWord_335808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335808).length < 2 ^ (prefixWord ++ tailWord_335808).sum := by decide
  have hdescent : baseEnd_335808 < baseStart_335808 := by decide
  rcases family_descends (prefixWord ++ tailWord_335808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335825 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_335825 : Nat := 118140960795 + 335825 * 2 ^ 59
def prefixEnd_335825 : Nat := 4983230072969 + 3 ^ 40 * 335825 * 2
def baseEnd_335825 : Nat := 172439640796253816843075

theorem tailTrace_335825 : CollatzResearch.WordTrace tailWord_335825 prefixEnd_335825 172439640796253816843075 := by
  unfold tailWord_335825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248544008370854188896929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8165696005580569459264619 12248544008370854188896929)
  ·
    refine ⟨9186408006278140641672697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12248544008370854188896929 9186408006278140641672697)
    ·
      refine ⟨6889806004708605481254523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9186408006278140641672697 6889806004708605481254523)
      ·
        refine ⟨10334709007062908221881785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6889806004708605481254523 10334709007062908221881785)
        ·
          refine ⟨7751031755297181166411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10334709007062908221881785 7751031755297181166411339)
          ·
            refine ⟨11626547632945771749617009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7751031755297181166411339 11626547632945771749617009)
            ·
              refine ⟨8719910724709328812212757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626547632945771749617009 8719910724709328812212757)
              ·
                refine ⟨408745815220749788072473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8719910724709328812212757 408745815220749788072473)
                ·
                  refine ⟨306559361415562341054355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408745815220749788072473 306559361415562341054355)
                  ·
                    refine ⟨459839042123343511581533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306559361415562341054355 459839042123343511581533)
                    ·
                      refine ⟨172439640796253816843075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 459839042123343511581533 172439640796253816843075)
                      ·
                        rfl

theorem cell23_335825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_335825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335825 prefixEnd_335825 := by exact prefixLift 335825
  have htrace : WordTrace (prefixWord ++ tailWord_335825) baseStart_335825 baseEnd_335825 := by
    simpa [prefixWord, tailWord_335825, baseEnd_335825] using wordTrace_append hprefix tailTrace_335825
  have hstable : (prefixWord ++ tailWord_335825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335825).length < 2 ^ (prefixWord ++ tailWord_335825).sum := by decide
  have hdescent : baseEnd_335825 < baseStart_335825 := by decide
  rcases family_descends (prefixWord ++ tailWord_335825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335836 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_335836 : Nat := 118140960795 + 335836 * 2 ^ 59
def prefixEnd_335836 : Nat := 4983230072969 + 3 ^ 40 * 335836 * 2
def baseEnd_335836 : Nat := 57481763027817757935175

theorem tailTrace_335836 : CollatzResearch.WordTrace tailWord_335836 prefixEnd_335836 57481763027817757935175 := by
  unfold tailWord_335836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124472605665501533773681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8165963474220668711698241 6124472605665501533773681)
  ·
    refine ⟨4593354454249126150330261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6124472605665501533773681 4593354454249126150330261)
    ·
      refine ⟨215313490042927788296731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4593354454249126150330261 215313490042927788296731)
      ·
        refine ⟨322970235064391682445097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215313490042927788296731 322970235064391682445097)
        ·
          refine ⟨242227676298293761833823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322970235064391682445097 242227676298293761833823)
          ·
            refine ⟨363341514447440642750735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242227676298293761833823 363341514447440642750735)
            ·
              refine ⟨545012271671160964126103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363341514447440642750735 545012271671160964126103)
              ·
                refine ⟨817518407506741446189155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545012271671160964126103 817518407506741446189155)
                ·
                  refine ⟨1226277611260112169283733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817518407506741446189155 1226277611260112169283733)
                  ·
                    refine ⟨57481763027817757935175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1226277611260112169283733 57481763027817757935175)
                    ·
                      rfl

theorem cell23_335836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_335836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335836 prefixEnd_335836 := by exact prefixLift 335836
  have htrace : WordTrace (prefixWord ++ tailWord_335836) baseStart_335836 baseEnd_335836 := by
    simpa [prefixWord, tailWord_335836, baseEnd_335836] using wordTrace_append hprefix tailTrace_335836
  have hstable : (prefixWord ++ tailWord_335836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335836).length < 2 ^ (prefixWord ++ tailWord_335836).sum := by decide
  have hdescent : baseEnd_335836 < baseStart_335836 := by decide
  rcases family_descends (prefixWord ++ tailWord_335836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335851 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_335851 : Nat := 118140960795 + 335851 * 2 ^ 59
def prefixEnd_335851 : Nat := 4983230072969 + 3 ^ 40 * 335851 * 2
def baseEnd_335851 : Nat := 172452991293270715117955

theorem tailTrace_335851 : CollatzResearch.WordTrace tailWord_335851 prefixEnd_335851 172452991293270715117955 := by
  unfold tailWord_335851
  simp only [CollatzResearch.WordTrace]
  refine ⟨12249492306276660629343407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166328204184440419562271 12249492306276660629343407)
  ·
    refine ⟨18374238459414990944015111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12249492306276660629343407 18374238459414990944015111)
    ·
      refine ⟨27561357689122486416022667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18374238459414990944015111 27561357689122486416022667)
      ·
        refine ⟨41342036533683729624034001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27561357689122486416022667 41342036533683729624034001)
        ·
          refine ⟨31006527400262797218025501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41342036533683729624034001 31006527400262797218025501)
          ·
            refine ⟨11627447775098548956759563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31006527400262797218025501 11627447775098548956759563)
            ·
              refine ⟨17441171662647823435139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627447775098548956759563 17441171662647823435139345)
              ·
                refine ⟨13080878746985867576354509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17441171662647823435139345 13080878746985867576354509)
                ·
                  refine ⟨4905329530119700341132941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13080878746985867576354509 4905329530119700341132941)
                  ·
                    refine ⟨1839498573794887627924853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4905329530119700341132941 1839498573794887627924853)
                    ·
                      refine ⟨172452991293270715117955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1839498573794887627924853 172452991293270715117955)
                      ·
                        rfl

theorem cell23_335851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_335851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335851 prefixEnd_335851 := by exact prefixLift 335851
  have htrace : WordTrace (prefixWord ++ tailWord_335851) baseStart_335851 baseEnd_335851 := by
    simpa [prefixWord, tailWord_335851, baseEnd_335851] using wordTrace_append hprefix tailTrace_335851
  have hstable : (prefixWord ++ tailWord_335851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335851).length < 2 ^ (prefixWord ++ tailWord_335851).sum := by decide
  have hdescent : baseEnd_335851 < baseStart_335851 := by decide
  rcases family_descends (prefixWord ++ tailWord_335851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335868 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_335868 : Nat := 118140960795 + 335868 * 2 ^ 59
def prefixEnd_335868 : Nat := 4983230072969 + 3 ^ 40 * 335868 * 2
def baseEnd_335868 : Nat := 172461720464397148605377

theorem tailTrace_335868 : CollatzResearch.WordTrace tailWord_335868 prefixEnd_335868 172461720464397148605377 := by
  unfold tailWord_335868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125056173607536266356129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8166741564810048355141505 6125056173607536266356129)
  ·
    refine ⟨4593792130205652199767097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6125056173607536266356129 4593792130205652199767097)
    ·
      refine ⟨3445344097654239149825323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4593792130205652199767097 3445344097654239149825323)
      ·
        refine ⟨5168016146481358724737985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445344097654239149825323 5168016146481358724737985)
        ·
          refine ⟨3876012109861019043553489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5168016146481358724737985 3876012109861019043553489)
          ·
            refine ⟨2907009082395764282665117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3876012109861019043553489 2907009082395764282665117)
            ·
              refine ⟨1090128405898411605999419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2907009082395764282665117 1090128405898411605999419)
              ·
                refine ⟨1635192608847617408999129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090128405898411605999419 1635192608847617408999129)
                ·
                  refine ⟨1226394456635713056749347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1635192608847617408999129 1226394456635713056749347)
                  ·
                    refine ⟨1839591684953569585124021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1226394456635713056749347 1839591684953569585124021)
                    ·
                      refine ⟨172461720464397148605377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1839591684953569585124021 172461720464397148605377)
                      ·
                        rfl

theorem cell23_335868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_335868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335868 prefixEnd_335868 := by exact prefixLift 335868
  have htrace : WordTrace (prefixWord ++ tailWord_335868) baseStart_335868 baseEnd_335868 := by
    simpa [prefixWord, tailWord_335868, baseEnd_335868] using wordTrace_append hprefix tailTrace_335868
  have hstable : (prefixWord ++ tailWord_335868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335868).length < 2 ^ (prefixWord ++ tailWord_335868).sum := by decide
  have hdescent : baseEnd_335868 < baseStart_335868 := by decide
  rcases family_descends (prefixWord ++ tailWord_335868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335871 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 9]
def baseStart_335871 : Nat := 118140960795 + 335871 * 2 ^ 59
def prefixEnd_335871 : Nat := 4983230072969 + 3 ^ 40 * 335871 * 2
def baseEnd_335871 : Nat := 19162584545151181874207

theorem tailTrace_335871 : CollatzResearch.WordTrace tailWord_335871 prefixEnd_335871 19162584545151181874207 := by
  unfold tailWord_335871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12250221766204204045071467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8166814510802802696714311 12250221766204204045071467)
  ·
    refine ⟨18375332649306306067607201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12250221766204204045071467 18375332649306306067607201)
    ·
      refine ⟨13781499486979729550705401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18375332649306306067607201 13781499486979729550705401)
      ·
        refine ⟨10336124615234797163029051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13781499486979729550705401 10336124615234797163029051)
        ·
          refine ⟨15504186922852195744543577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10336124615234797163029051 15504186922852195744543577)
          ·
            refine ⟨11628140192139146808407683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15504186922852195744543577 11628140192139146808407683)
            ·
              refine ⟨17442210288208720212611525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11628140192139146808407683 17442210288208720212611525)
              ·
                refine ⟨3270414429039135039864661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17442210288208720212611525 3270414429039135039864661)
                ·
                  refine ⟨19162584545151181874207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3270414429039135039864661 19162584545151181874207)
                  ·
                    rfl

theorem cell23_335871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 9].length) (baseStart_335871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335871 prefixEnd_335871 := by exact prefixLift 335871
  have htrace : WordTrace (prefixWord ++ tailWord_335871) baseStart_335871 baseEnd_335871 := by
    simpa [prefixWord, tailWord_335871, baseEnd_335871] using wordTrace_append hprefix tailTrace_335871
  have hstable : (prefixWord ++ tailWord_335871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335871).length < 2 ^ (prefixWord ++ tailWord_335871).sum := by decide
  have hdescent : baseEnd_335871 < baseStart_335871 := by decide
  rcases family_descends (prefixWord ++ tailWord_335871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_335975 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_335975 : Nat := 118140960795 + 335975 * 2 ^ 59
def prefixEnd_335975 : Nat := 4983230072969 + 3 ^ 40 * 335975 * 2
def baseEnd_335975 : Nat := 172516662894428229967385

theorem tailTrace_335975 : CollatzResearch.WordTrace tailWord_335975 prefixEnd_335975 172516662894428229967385 := by
  unfold tailWord_335975
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254014957827429806857379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8169343305218286537904919 12254014957827429806857379)
  ·
    refine ⟨18381022436741144710286069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12254014957827429806857379 18381022436741144710286069)
    ·
      refine ⟨1723220853444482316589319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18381022436741144710286069 1723220853444482316589319)
      ·
        refine ⟨2584831280166723474883979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723220853444482316589319 2584831280166723474883979)
        ·
          refine ⟨3877246920250085212325969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584831280166723474883979 3877246920250085212325969)
          ·
            refine ⟨2907935190187563909244477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3877246920250085212325969 2907935190187563909244477)
            ·
              refine ⟨1090475696320336465966679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2907935190187563909244477 1090475696320336465966679)
              ·
                refine ⟨1635713544480504698950019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090475696320336465966679 1635713544480504698950019)
                ·
                  refine ⟨2453570316720757048425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635713544480504698950019 2453570316720757048425029)
                  ·
                    refine ⟨460044434385141946579693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453570316720757048425029 460044434385141946579693)
                    ·
                      refine ⟨172516662894428229967385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460044434385141946579693 172516662894428229967385)
                      ·
                        rfl

theorem cell23_335975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_335975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_335975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_335975 prefixEnd_335975 := by exact prefixLift 335975
  have htrace : WordTrace (prefixWord ++ tailWord_335975) baseStart_335975 baseEnd_335975 := by
    simpa [prefixWord, tailWord_335975, baseEnd_335975] using wordTrace_append hprefix tailTrace_335975
  have hstable : (prefixWord ++ tailWord_335975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_335975).length < 2 ^ (prefixWord ++ tailWord_335975).sum := by decide
  have hdescent : baseEnd_335975 < baseStart_335975 := by decide
  rcases family_descends (prefixWord ++ tailWord_335975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336032 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2]
def baseStart_336032 : Nat := 118140960795 + 336032 * 2 ^ 59
def prefixEnd_336032 : Nat := 4983230072969 + 3 ^ 40 * 336032 * 2
def baseEnd_336032 : Nat := 172545931291734506954623

theorem tailTrace_336032 : CollatzResearch.WordTrace tailWord_336032 prefixEnd_336032 172545931291734506954623 := by
  unfold tailWord_336032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128046959310464270841175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8170729279080619027788233 6128046959310464270841175)
  ·
    refine ⟨9192070438965696406261763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6128046959310464270841175 9192070438965696406261763)
    ·
      refine ⟨13788105658448544609392645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192070438965696406261763 13788105658448544609392645)
      ·
        refine ⟨2585269810959102114261121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13788105658448544609392645 2585269810959102114261121)
        ·
          refine ⟨1938952358219326585695841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2585269810959102114261121 1938952358219326585695841)
          ·
            refine ⟨1454214268664494939271881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1938952358219326585695841 1454214268664494939271881)
            ·
              refine ⟨1090660701498371204453911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1454214268664494939271881 1090660701498371204453911)
              ·
                refine ⟨1635991052247556806680867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090660701498371204453911 1635991052247556806680867)
                ·
                  refine ⟨2453986578371335210021301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635991052247556806680867 2453986578371335210021301)
                  ·
                    refine ⟨230061241722312675939497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2453986578371335210021301 230061241722312675939497)
                    ·
                      refine ⟨172545931291734506954623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230061241722312675939497 172545931291734506954623)
                      ·
                        rfl

theorem cell23_336032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_336032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336032 prefixEnd_336032 := by exact prefixLift 336032
  have htrace : WordTrace (prefixWord ++ tailWord_336032) baseStart_336032 baseEnd_336032 := by
    simpa [prefixWord, tailWord_336032, baseEnd_336032] using wordTrace_append hprefix tailTrace_336032
  have hstable : (prefixWord ++ tailWord_336032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336032).length < 2 ^ (prefixWord ++ tailWord_336032).sum := by decide
  have hdescent : baseEnd_336032 < baseStart_336032 := by decide
  rcases family_descends (prefixWord ++ tailWord_336032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336056 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_336056 : Nat := 118140960795 + 336056 * 2 ^ 59
def prefixEnd_336056 : Nat := 4983230072969 + 3 ^ 40 * 336056 * 2
def baseEnd_336056 : Nat := 172558254827442413054513

theorem tailTrace_336056 : CollatzResearch.WordTrace tailWord_336056 prefixEnd_336056 172558254827442413054513 := by
  unfold tailWord_336056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128484635266990320278011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8171312847022653760370681 6128484635266990320278011)
  ·
    refine ⟨9192726952900485480417017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6128484635266990320278011 9192726952900485480417017)
    ·
      refine ⟨6894545214675364110312763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9192726952900485480417017 6894545214675364110312763)
      ·
        refine ⟨10341817822013046165469145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894545214675364110312763 10341817822013046165469145)
        ·
          refine ⟨7756363366509784624101859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10341817822013046165469145 7756363366509784624101859)
          ·
            refine ⟨11634545049764676936152789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7756363366509784624101859 11634545049764676936152789)
            ·
              refine ⟨272684649603859615691081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11634545049764676936152789 272684649603859615691081)
              ·
                refine ⟨204513487202894711768311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272684649603859615691081 204513487202894711768311)
                ·
                  refine ⟨306770230804342067652467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204513487202894711768311 306770230804342067652467)
                  ·
                    refine ⟨460155346206513101478701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306770230804342067652467 460155346206513101478701)
                    ·
                      refine ⟨172558254827442413054513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460155346206513101478701 172558254827442413054513)
                      ·
                        rfl

theorem cell23_336056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_336056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336056 prefixEnd_336056 := by exact prefixLift 336056
  have htrace : WordTrace (prefixWord ++ tailWord_336056) baseStart_336056 baseEnd_336056 := by
    simpa [prefixWord, tailWord_336056, baseEnd_336056] using wordTrace_append hprefix tailTrace_336056
  have hstable : (prefixWord ++ tailWord_336056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336056).length < 2 ^ (prefixWord ++ tailWord_336056).sum := by decide
  have hdescent : baseEnd_336056 < baseStart_336056 := by decide
  rcases family_descends (prefixWord ++ tailWord_336056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336075 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_336075 : Nat := 118140960795 + 336075 * 2 ^ 59
def prefixEnd_336075 : Nat := 4983230072969 + 3 ^ 40 * 336075 * 2
def baseEnd_336075 : Nat := 172568010959877838716925

theorem tailTrace_336075 : CollatzResearch.WordTrace tailWord_336075 prefixEnd_336075 172568010959877838716925 := by
  unfold tailWord_336075
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257662257465146885497679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8171774838310097923665119 12257662257465146885497679)
  ·
    refine ⟨18386493386197720328246519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12257662257465146885497679 18386493386197720328246519)
    ·
      refine ⟨27579740079296580492369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386493386197720328246519 27579740079296580492369779)
      ·
        refine ⟨41369610118944870738554669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27579740079296580492369779 41369610118944870738554669)
        ·
          refine ⟨15513603794604326526958001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41369610118944870738554669 15513603794604326526958001)
          ·
            refine ⟨11635202845953244895218501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513603794604326526958001 11635202845953244895218501)
            ·
              refine ⟨2181600533616233417853469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11635202845953244895218501 2181600533616233417853469)
              ·
                refine ⟨818100200106087531695051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181600533616233417853469 818100200106087531695051)
                ·
                  refine ⟨1227150300159131297542577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818100200106087531695051 1227150300159131297542577)
                  ·
                    refine ⟨920362725119348473156933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1227150300159131297542577 920362725119348473156933)
                    ·
                      refine ⟨172568010959877838716925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 920362725119348473156933 172568010959877838716925)
                      ·
                        rfl

theorem cell23_336075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_336075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336075 prefixEnd_336075 := by exact prefixLift 336075
  have htrace : WordTrace (prefixWord ++ tailWord_336075) baseStart_336075 baseEnd_336075 := by
    simpa [prefixWord, tailWord_336075, baseEnd_336075] using wordTrace_append hprefix tailTrace_336075
  have hstable : (prefixWord ++ tailWord_336075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336075).length < 2 ^ (prefixWord ++ tailWord_336075).sum := by decide
  have hdescent : baseEnd_336075 < baseStart_336075 := by decide
  rcases family_descends (prefixWord ++ tailWord_336075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336076 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_336076 : Nat := 118140960795 + 336076 * 2 ^ 59
def prefixEnd_336076 : Nat := 4983230072969 + 3 ^ 40 * 336076 * 2
def baseEnd_336076 : Nat := 57522841480177444934807

theorem tailTrace_336076 : CollatzResearch.WordTrace tailWord_336076 prefixEnd_336076 57522841480177444934807 := by
  unfold tailWord_336076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128849365230762028142041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8171799153641016037522721 6128849365230762028142041)
  ·
    refine ⟨4596637023923071521106531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6128849365230762028142041 4596637023923071521106531)
    ·
      refine ⟨6894955535884607281659797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596637023923071521106531 6894955535884607281659797)
      ·
        refine ⟨323201040744590966327803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6894955535884607281659797 323201040744590966327803)
        ·
          refine ⟨484801561116886449491705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323201040744590966327803 484801561116886449491705)
          ·
            refine ⟨363601170837664837118779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484801561116886449491705 363601170837664837118779)
            ·
              refine ⟨545401756256497255678169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363601170837664837118779 545401756256497255678169)
              ·
                refine ⟨409051317192372941758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545401756256497255678169 409051317192372941758627)
                ·
                  refine ⟨613576975788559412637941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409051317192372941758627 613576975788559412637941)
                  ·
                    refine ⟨57522841480177444934807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 613576975788559412637941 57522841480177444934807)
                    ·
                      rfl

theorem cell23_336076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_336076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336076 prefixEnd_336076 := by exact prefixLift 336076
  have htrace : WordTrace (prefixWord ++ tailWord_336076) baseStart_336076 baseEnd_336076 := by
    simpa [prefixWord, tailWord_336076, baseEnd_336076] using wordTrace_append hprefix tailTrace_336076
  have hstable : (prefixWord ++ tailWord_336076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336076).length < 2 ^ (prefixWord ++ tailWord_336076).sum := by decide
  have hdescent : baseEnd_336076 < baseStart_336076 := by decide
  rcases family_descends (prefixWord ++ tailWord_336076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336096 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 1, 2, 2]
def baseStart_336096 : Nat := 118140960795 + 336096 * 2 ^ 59
def prefixEnd_336096 : Nat := 4983230072969 + 3 ^ 40 * 336096 * 2
def baseEnd_336096 : Nat := 172578794053622256554329

theorem tailTrace_336096 : CollatzResearch.WordTrace tailWord_336096 prefixEnd_336096 172578794053622256554329 := by
  unfold tailWord_336096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129214095194533736006071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8172285460259378314674761 6129214095194533736006071)
  ·
    refine ⟨9193821142791800604009107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129214095194533736006071 9193821142791800604009107)
    ·
      refine ⟨13790731714187700906013661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193821142791800604009107 13790731714187700906013661)
      ·
        refine ⟨5171524392820387839755123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13790731714187700906013661 5171524392820387839755123)
        ·
          refine ⟨7757286589230581759632685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5171524392820387839755123 7757286589230581759632685)
          ·
            refine ⟨2908982470961468159862257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7757286589230581759632685 2908982470961468159862257)
            ·
              refine ⟨2181736853221101119896693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908982470961468159862257 2181736853221101119896693)
              ·
                refine ⟨204537829989478229990315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2181736853221101119896693 204537829989478229990315)
                ·
                  refine ⟨306806744984217344985473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204537829989478229990315 306806744984217344985473)
                  ·
                    refine ⟨230105058738163008739105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306806744984217344985473 230105058738163008739105)
                    ·
                      refine ⟨172578794053622256554329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230105058738163008739105 172578794053622256554329)
                      ·
                        rfl

theorem cell23_336096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_336096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336096 prefixEnd_336096 := by exact prefixLift 336096
  have htrace : WordTrace (prefixWord ++ tailWord_336096) baseStart_336096 baseEnd_336096 := by
    simpa [prefixWord, tailWord_336096, baseEnd_336096] using wordTrace_append hprefix tailTrace_336096
  have hstable : (prefixWord ++ tailWord_336096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336096).length < 2 ^ (prefixWord ++ tailWord_336096).sum := by decide
  have hdescent : baseEnd_336096 < baseStart_336096 := by decide
  rcases family_descends (prefixWord ++ tailWord_336096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336112 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_336112 : Nat := 118140960795 + 336112 * 2 ^ 59
def prefixEnd_336112 : Nat := 4983230072969 + 3 ^ 40 * 336112 * 2
def baseEnd_336112 : Nat := 172587009744094193954255

theorem tailTrace_336112 : CollatzResearch.WordTrace tailWord_336112 prefixEnd_336112 172587009744094193954255 := by
  unfold tailWord_336112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129505879165551102297295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8172674505554068136396393 6129505879165551102297295)
  ·
    refine ⟨9194258818748326653445943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129505879165551102297295 9194258818748326653445943)
    ·
      refine ⟨13791388228122489980168915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194258818748326653445943 13791388228122489980168915)
      ·
        refine ⟨20687082342183734970253373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13791388228122489980168915 20687082342183734970253373)
        ·
          refine ⟨7757655878318900613845015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20687082342183734970253373 7757655878318900613845015)
          ·
            refine ⟨11636483817478350920767523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757655878318900613845015 11636483817478350920767523)
            ·
              refine ⟨17454725726217526381151285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11636483817478350920767523 17454725726217526381151285)
              ·
                refine ⟨1636380536832893098232933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17454725726217526381151285 1636380536832893098232933)
                ·
                  refine ⟨306821350656167455918675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636380536832893098232933 306821350656167455918675)
                  ·
                    refine ⟨460232025984251183878013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306821350656167455918675 460232025984251183878013)
                    ·
                      refine ⟨172587009744094193954255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460232025984251183878013 172587009744094193954255)
                      ·
                        rfl

theorem cell23_336112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_336112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336112 prefixEnd_336112 := by exact prefixLift 336112
  have htrace : WordTrace (prefixWord ++ tailWord_336112) baseStart_336112 baseEnd_336112 := by
    simpa [prefixWord, tailWord_336112, baseEnd_336112] using wordTrace_append hprefix tailTrace_336112
  have hstable : (prefixWord ++ tailWord_336112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336112).length < 2 ^ (prefixWord ++ tailWord_336112).sum := by decide
  have hdescent : baseEnd_336112 < baseStart_336112 := by decide
  rcases family_descends (prefixWord ++ tailWord_336112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336113 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_336113 : Nat := 118140960795 + 336113 * 2 ^ 59
def prefixEnd_336113 : Nat := 4983230072969 + 3 ^ 40 * 336113 * 2
def baseEnd_336113 : Nat := 172587523224748690041751

theorem tailTrace_336113 : CollatzResearch.WordTrace tailWord_336113 prefixEnd_336113 172587523224748690041751 := by
  unfold tailWord_336113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259048231327479375380993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8172698820884986250253995 12259048231327479375380993)
  ·
    refine ⟨9194286173495609531535745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12259048231327479375380993 9194286173495609531535745)
    ·
      refine ⟨6895714630121707148651809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9194286173495609531535745 6895714630121707148651809)
      ·
        refine ⟨5171785972591280361488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6895714630121707148651809 5171785972591280361488857)
        ·
          refine ⟨3878839479443460271116643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171785972591280361488857 3878839479443460271116643)
          ·
            refine ⟨5818259219165190406674965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878839479443460271116643 5818259219165190406674965)
            ·
              refine ⟨272730900898368300312889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5818259219165190406674965 272730900898368300312889)
              ·
                refine ⟨204548175673776225234667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272730900898368300312889 204548175673776225234667)
                ·
                  refine ⟨306822263510664337852001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204548175673776225234667 306822263510664337852001)
                  ·
                    refine ⟨230116697632998253389001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306822263510664337852001 230116697632998253389001)
                    ·
                      refine ⟨172587523224748690041751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230116697632998253389001 172587523224748690041751)
                      ·
                        rfl

theorem cell23_336113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_336113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336113 prefixEnd_336113 := by exact prefixLift 336113
  have htrace : WordTrace (prefixWord ++ tailWord_336113) baseStart_336113 baseEnd_336113 := by
    simpa [prefixWord, tailWord_336113, baseEnd_336113] using wordTrace_append hprefix tailTrace_336113
  have hstable : (prefixWord ++ tailWord_336113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336113).length < 2 ^ (prefixWord ++ tailWord_336113).sum := by decide
  have hdescent : baseEnd_336113 < baseStart_336113 := by decide
  rcases family_descends (prefixWord ++ tailWord_336113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336129 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_336129 : Nat := 118140960795 + 336129 * 2 ^ 59
def prefixEnd_336129 : Nat := 4983230072969 + 3 ^ 40 * 336129 * 2
def baseEnd_336129 : Nat := 172595738915220627441677

theorem tailTrace_336129 : CollatzResearch.WordTrace tailWord_336129 prefixEnd_336129 172595738915220627441677 := by
  unfold tailWord_336129
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259631799269514107963441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173087866179676071975627 12259631799269514107963441)
  ·
    refine ⟨9194723849452135580972581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12259631799269514107963441 9194723849452135580972581)
    ·
      refine ⟨1724010721772275421432359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9194723849452135580972581 1724010721772275421432359)
      ·
        refine ⟨2586016082658413132148539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724010721772275421432359 2586016082658413132148539)
        ·
          refine ⟨3879024123987619698222809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586016082658413132148539 3879024123987619698222809)
          ·
            refine ⟨2909268092990714773667107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879024123987619698222809 2909268092990714773667107)
            ·
              refine ⟨4363902139486072160500661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909268092990714773667107 4363902139486072160500661)
              ·
                refine ⟨409115825576819265046937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4363902139486072160500661 409115825576819265046937)
                ·
                  refine ⟨306836869182614448785203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409115825576819265046937 306836869182614448785203)
                  ·
                    refine ⟨460255303773921673177805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306836869182614448785203 460255303773921673177805)
                    ·
                      refine ⟨172595738915220627441677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460255303773921673177805 172595738915220627441677)
                      ·
                        rfl

theorem cell23_336129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_336129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336129 prefixEnd_336129 := by exact prefixLift 336129
  have htrace : WordTrace (prefixWord ++ tailWord_336129) baseStart_336129 baseEnd_336129 := by
    simpa [prefixWord, tailWord_336129, baseEnd_336129] using wordTrace_append hprefix tailTrace_336129
  have hstable : (prefixWord ++ tailWord_336129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336129).length < 2 ^ (prefixWord ++ tailWord_336129).sum := by decide
  have hdescent : baseEnd_336129 < baseStart_336129 := by decide
  rcases family_descends (prefixWord ++ tailWord_336129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336139 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 1, 3, 2]
def baseStart_336139 : Nat := 118140960795 + 336139 * 2 ^ 59
def prefixEnd_336139 : Nat := 4983230072969 + 3 ^ 40 * 336139 * 2
def baseEnd_336139 : Nat := 172600873721765588316631

theorem tailTrace_336139 : CollatzResearch.WordTrace tailWord_336139 prefixEnd_336139 172600873721765588316631 := by
  unfold tailWord_336139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259996529233285815827471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173331019488857210551647 12259996529233285815827471)
  ·
    refine ⟨18389994793849928723741207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259996529233285815827471 18389994793849928723741207)
    ·
      refine ⟨27584992190774893085611811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389994793849928723741207 27584992190774893085611811)
      ·
        refine ⟨41377488286162339628417717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27584992190774893085611811 41377488286162339628417717)
        ·
          refine ⟨3879139526827719340164161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41377488286162339628417717 3879139526827719340164161)
          ·
            refine ⟨2909354645120789505123121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879139526827719340164161 2909354645120789505123121)
            ·
              refine ⟨2182015983840592128842341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909354645120789505123121 2182015983840592128842341)
              ·
                refine ⟨409127996970111024157939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2182015983840592128842341 409127996970111024157939)
                ·
                  refine ⟨613691995455166536236909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409127996970111024157939 613691995455166536236909)
                  ·
                    refine ⟨230134498295687451088841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613691995455166536236909 230134498295687451088841)
                    ·
                      refine ⟨172600873721765588316631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230134498295687451088841 172600873721765588316631)
                      ·
                        rfl

theorem cell23_336139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3, 2].length) (baseStart_336139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336139 prefixEnd_336139 := by exact prefixLift 336139
  have htrace : WordTrace (prefixWord ++ tailWord_336139) baseStart_336139 baseEnd_336139 := by
    simpa [prefixWord, tailWord_336139, baseEnd_336139] using wordTrace_append hprefix tailTrace_336139
  have hstable : (prefixWord ++ tailWord_336139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336139).length < 2 ^ (prefixWord ++ tailWord_336139).sum := by decide
  have hdescent : baseEnd_336139 < baseStart_336139 := by decide
  rcases family_descends (prefixWord ++ tailWord_336139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336155 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_336155 : Nat := 118140960795 + 336155 * 2 ^ 59
def prefixEnd_336155 : Nat := 4983230072969 + 3 ^ 40 * 336155 * 2
def baseEnd_336155 : Nat := 172609089412237525716557

theorem tailTrace_336155 : CollatzResearch.WordTrace tailWord_336155 prefixEnd_336155 172609089412237525716557 := by
  unfold tailWord_336155
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260580097175320548409919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8173720064783547032273279 12260580097175320548409919)
  ·
    refine ⟨18390870145762980822614879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260580097175320548409919 18390870145762980822614879)
    ·
      refine ⟨27586305218644471233922319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390870145762980822614879 27586305218644471233922319)
      ·
        refine ⟨41379457827966706850883479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27586305218644471233922319 41379457827966706850883479)
        ·
          refine ⟨62069186741950060276325219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41379457827966706850883479 62069186741950060276325219)
          ·
            refine ⟨93103780112925090414487829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62069186741950060276325219 93103780112925090414487829)
            ·
              refine ⟨4364239692793363613179117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93103780112925090414487829 4364239692793363613179117)
              ·
                refine ⟨1636589884797511354942169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364239692793363613179117 1636589884797511354942169)
                ·
                  refine ⟨1227442413598133516206627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636589884797511354942169 1227442413598133516206627)
                  ·
                    refine ⟨1841163620397200274309941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1227442413598133516206627 1841163620397200274309941)
                    ·
                      refine ⟨172609089412237525716557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1841163620397200274309941 172609089412237525716557)
                      ·
                        rfl

theorem cell23_336155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_336155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336155 prefixEnd_336155 := by exact prefixLift 336155
  have htrace : WordTrace (prefixWord ++ tailWord_336155) baseStart_336155 baseEnd_336155 := by
    simpa [prefixWord, tailWord_336155, baseEnd_336155] using wordTrace_append hprefix tailTrace_336155
  have hstable : (prefixWord ++ tailWord_336155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336155).length < 2 ^ (prefixWord ++ tailWord_336155).sum := by decide
  have hdescent : baseEnd_336155 < baseStart_336155 := by decide
  rcases family_descends (prefixWord ++ tailWord_336155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336162 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_336162 : Nat := 118140960795 + 336162 * 2 ^ 59
def prefixEnd_336162 : Nat := 4983230072969 + 3 ^ 40 * 336162 * 2
def baseEnd_336162 : Nat := 57537561258939666109675

theorem tailTrace_336162 : CollatzResearch.WordTrace tailWord_336162 prefixEnd_336162 57537561258939666109675 := by
  unfold tailWord_336162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065208852037490185978685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8173890272099973829276493 3065208852037490185978685)
  ·
    refine ⟨1149453319514058819742007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3065208852037490185978685 1149453319514058819742007)
    ·
      refine ⟨1724179979271088229613011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149453319514058819742007 1724179979271088229613011)
      ·
        refine ⟨2586269968906632344419517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724179979271088229613011 2586269968906632344419517)
        ·
          refine ⟨969851238339987129157319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2586269968906632344419517 969851238339987129157319)
          ·
            refine ⟨1454776857509980693735979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969851238339987129157319 1454776857509980693735979)
            ·
              refine ⟨2182165286264971040603969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454776857509980693735979 2182165286264971040603969)
              ·
                refine ⟨1636623964698728280452977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182165286264971040603969 1636623964698728280452977)
                ·
                  refine ⟨1227467973524046210339733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1636623964698728280452977 1227467973524046210339733)
                  ·
                    refine ⟨57537561258939666109675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1227467973524046210339733 57537561258939666109675)
                    ·
                      rfl

theorem cell23_336162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_336162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336162 prefixEnd_336162 := by exact prefixLift 336162
  have htrace : WordTrace (prefixWord ++ tailWord_336162) baseStart_336162 baseEnd_336162 := by
    simpa [prefixWord, tailWord_336162, baseEnd_336162] using wordTrace_append hprefix tailTrace_336162
  have hstable : (prefixWord ++ tailWord_336162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336162).length < 2 ^ (prefixWord ++ tailWord_336162).sum := by decide
  have hdescent : baseEnd_336162 < baseStart_336162 := by decide
  rcases family_descends (prefixWord ++ tailWord_336162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336175 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 7]
def baseStart_336175 : Nat := 118140960795 + 336175 * 2 ^ 59
def prefixEnd_336175 : Nat := 4983230072969 + 3 ^ 40 * 336175 * 2
def baseEnd_336175 : Nat := 19179928780591938607385

theorem tailTrace_336175 : CollatzResearch.WordTrace tailWord_336175 prefixEnd_336175 19179928780591938607385 := by
  unfold tailWord_336175
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261309557102863964137979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8174206371401909309425319 12261309557102863964137979)
  ·
    refine ⟨18391964335654295946206969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12261309557102863964137979 18391964335654295946206969)
    ·
      refine ⟨13793973251740721959655227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18391964335654295946206969 13793973251740721959655227)
      ·
        refine ⟨20690959877611082939482841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13793973251740721959655227 20690959877611082939482841)
        ·
          refine ⟨15518219908208312204612131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20690959877611082939482841 15518219908208312204612131)
          ·
            refine ⟨23277329862312468306918197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518219908208312204612131 23277329862312468306918197)
            ·
              refine ⟨2182249674591793903773581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23277329862312468306918197 2182249674591793903773581)
              ·
                refine ⟨818343627971922713915093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2182249674591793903773581 818343627971922713915093)
                ·
                  refine ⟨19179928780591938607385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 818343627971922713915093 19179928780591938607385)
                  ·
                    rfl

theorem cell23_336175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 7].length) (baseStart_336175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336175 prefixEnd_336175 := by exact prefixLift 336175
  have htrace : WordTrace (prefixWord ++ tailWord_336175) baseStart_336175 baseEnd_336175 := by
    simpa [prefixWord, tailWord_336175, baseEnd_336175] using wordTrace_append hprefix tailTrace_336175
  have hstable : (prefixWord ++ tailWord_336175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336175).length < 2 ^ (prefixWord ++ tailWord_336175).sum := by decide
  have hdescent : baseEnd_336175 < baseStart_336175 := by decide
  rcases family_descends (prefixWord ++ tailWord_336175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336186 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_336186 : Nat := 118140960795 + 336186 * 2 ^ 59
def prefixEnd_336186 : Nat := 4983230072969 + 3 ^ 40 * 336186 * 2
def baseEnd_336186 : Nat := 172625007312526904428915

theorem tailTrace_336186 : CollatzResearch.WordTrace tailWord_336186 prefixEnd_336186 172625007312526904428915 := by
  unfold tailWord_336186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065427690015753210697103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8174473840042008561858941 3065427690015753210697103)
  ·
    refine ⟨4598141535023629816045655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065427690015753210697103 4598141535023629816045655)
    ·
      refine ⟨6897212302535444724068483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598141535023629816045655 6897212302535444724068483)
      ·
        refine ⟨10345818453803167086102725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897212302535444724068483 10345818453803167086102725)
        ·
          refine ⟨1939840960088093828644261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10345818453803167086102725 1939840960088093828644261)
          ·
            refine ⟨363720180016517592870799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1939840960088093828644261 363720180016517592870799)
            ·
              refine ⟨545580270024776389306199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363720180016517592870799 545580270024776389306199)
              ·
                refine ⟨818370405037164583959299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545580270024776389306199 818370405037164583959299)
                ·
                  refine ⟨1227555607555746875938949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818370405037164583959299 1227555607555746875938949)
                  ·
                    refine ⟨230166676416702539238553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227555607555746875938949 230166676416702539238553)
                    ·
                      refine ⟨172625007312526904428915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230166676416702539238553 172625007312526904428915)
                      ·
                        rfl

theorem cell23_336186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_336186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336186 prefixEnd_336186 := by exact prefixLift 336186
  have htrace : WordTrace (prefixWord ++ tailWord_336186) baseStart_336186 baseEnd_336186 := by
    simpa [prefixWord, tailWord_336186, baseEnd_336186] using wordTrace_append hprefix tailTrace_336186
  have hstable : (prefixWord ++ tailWord_336186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336186).length < 2 ^ (prefixWord ++ tailWord_336186).sum := by decide
  have hdescent : baseEnd_336186 < baseStart_336186 := by decide
  rcases family_descends (prefixWord ++ tailWord_336186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336209 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 5]
def baseStart_336209 : Nat := 118140960795 + 336209 * 2 ^ 59
def prefixEnd_336209 : Nat := 4983230072969 + 3 ^ 40 * 336209 * 2
def baseEnd_336209 : Nat := 19181868596397812715701

theorem tailTrace_336209 : CollatzResearch.WordTrace tailWord_336209 prefixEnd_336209 19181868596397812715701 := by
  unfold tailWord_336209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262549638979687770875681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8175033092653125180583787 12262549638979687770875681)
  ·
    refine ⟨9196912229234765828156761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12262549638979687770875681 9196912229234765828156761)
    ·
      refine ⟨6897684171926074371117571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9196912229234765828156761 6897684171926074371117571)
      ·
        refine ⟨10346526257889111556676357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897684171926074371117571 10346526257889111556676357)
        ·
          refine ⟨1939973673354208416876817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10346526257889111556676357 1939973673354208416876817)
          ·
            refine ⟨1454980255015656312657613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939973673354208416876817 1454980255015656312657613)
            ·
              refine ⟨545617595630871117246605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1454980255015656312657613 545617595630871117246605)
              ·
                refine ⟨204606598361576668967477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545617595630871117246605 204606598361576668967477)
                ·
                  refine ⟨19181868596397812715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204606598361576668967477 19181868596397812715701)
                  ·
                    rfl

theorem cell23_336209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 5].length) (baseStart_336209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336209 prefixEnd_336209 := by exact prefixLift 336209
  have htrace : WordTrace (prefixWord ++ tailWord_336209) baseStart_336209 baseEnd_336209 := by
    simpa [prefixWord, tailWord_336209, baseEnd_336209] using wordTrace_append hprefix tailTrace_336209
  have hstable : (prefixWord ++ tailWord_336209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336209).length < 2 ^ (prefixWord ++ tailWord_336209).sum := by decide
  have hdescent : baseEnd_336209 < baseStart_336209 := by decide
  rcases family_descends (prefixWord ++ tailWord_336209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336225 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_336225 : Nat := 118140960795 + 336225 * 2 ^ 59
def prefixEnd_336225 : Nat := 4983230072969 + 3 ^ 40 * 336225 * 2
def baseEnd_336225 : Nat := 172645033058052251841235

theorem tailTrace_336225 : CollatzResearch.WordTrace tailWord_336225 prefixEnd_336225 172645033058052251841235 := by
  unfold tailWord_336225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263133206921722503458129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8175422137947815002305419 12263133206921722503458129)
  ·
    refine ⟨9197349905191291877593597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12263133206921722503458129 9197349905191291877593597)
    ·
      refine ⟨3449006214446734454097599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9197349905191291877593597 3449006214446734454097599)
      ·
        refine ⟨5173509321670101681146399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449006214446734454097599 5173509321670101681146399)
        ·
          refine ⟨7760263982505152521719599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173509321670101681146399 7760263982505152521719599)
          ·
            refine ⟨11640395973757728782579399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760263982505152521719599 11640395973757728782579399)
            ·
              refine ⟨17460593960636593173869099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640395973757728782579399 17460593960636593173869099)
              ·
                refine ⟨26190890940954889760803649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460593960636593173869099 26190890940954889760803649)
                ·
                  refine ⟨19643168205716167320602737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26190890940954889760803649 19643168205716167320602737)
                  ·
                    refine ⟨14732376154287125490452053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19643168205716167320602737 14732376154287125490452053)
                    ·
                      refine ⟨172645033058052251841235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 14732376154287125490452053 172645033058052251841235)
                      ·
                        rfl

theorem cell23_336225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_336225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336225 prefixEnd_336225 := by exact prefixLift 336225
  have htrace : WordTrace (prefixWord ++ tailWord_336225) baseStart_336225 baseEnd_336225 := by
    simpa [prefixWord, tailWord_336225, baseEnd_336225] using wordTrace_append hprefix tailTrace_336225
  have hstable : (prefixWord ++ tailWord_336225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336225).length < 2 ^ (prefixWord ++ tailWord_336225).sum := by decide
  have hdescent : baseEnd_336225 < baseStart_336225 := by decide
  rcases family_descends (prefixWord ++ tailWord_336225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336232 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_336232 : Nat := 118140960795 + 336232 * 2 ^ 59
def prefixEnd_336232 : Nat := 4983230072969 + 3 ^ 40 * 336232 * 2
def baseEnd_336232 : Nat := 172648627422633724453703

theorem tailTrace_336232 : CollatzResearch.WordTrace tailWord_336232 prefixEnd_336232 172648627422633724453703 := by
  unfold tailWord_336232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131694258948181349481475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8175592345264241799308633 6131694258948181349481475)
  ·
    refine ⟨9197541388422272024222213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6131694258948181349481475 9197541388422272024222213)
    ·
      refine ⟨1724539010329176004541665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9197541388422272024222213 1724539010329176004541665)
      ·
        refine ⟨1293404257746882003406249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724539010329176004541665 1293404257746882003406249)
        ·
          refine ⟨970053193310161502554687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1293404257746882003406249 970053193310161502554687)
          ·
            refine ⟨1455079789965242253832031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970053193310161502554687 1455079789965242253832031)
            ·
              refine ⟨2182619684947863380748047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455079789965242253832031 2182619684947863380748047)
              ·
                refine ⟨3273929527421795071122071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182619684947863380748047 3273929527421795071122071)
                ·
                  refine ⟨4910894291132692606683107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273929527421795071122071 4910894291132692606683107)
                  ·
                    refine ⟨7366341436699038910024661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910894291132692606683107 7366341436699038910024661)
                    ·
                      refine ⟨172648627422633724453703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7366341436699038910024661 172648627422633724453703)
                      ·
                        rfl

theorem cell23_336232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_336232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336232 prefixEnd_336232 := by exact prefixLift 336232
  have htrace : WordTrace (prefixWord ++ tailWord_336232) baseStart_336232 baseEnd_336232 := by
    simpa [prefixWord, tailWord_336232, baseEnd_336232] using wordTrace_append hprefix tailTrace_336232
  have hstable : (prefixWord ++ tailWord_336232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336232).length < 2 ^ (prefixWord ++ tailWord_336232).sum := by decide
  have hdescent : baseEnd_336232 < baseStart_336232 := by decide
  rcases family_descends (prefixWord ++ tailWord_336232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336279 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_336279 : Nat := 118140960795 + 336279 * 2 ^ 59
def prefixEnd_336279 : Nat := 4983230072969 + 3 ^ 40 * 336279 * 2
def baseEnd_336279 : Nat := 172672761013395040565987

theorem tailTrace_336279 : CollatzResearch.WordTrace tailWord_336279 prefixEnd_336279 172672761013395040565987 := by
  unfold tailWord_336279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265102748726089725923891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8176735165817393150615927 12265102748726089725923891)
  ·
    refine ⟨18397654123089134588885837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12265102748726089725923891 18397654123089134588885837)
    ·
      refine ⟨6899120296158425470832189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18397654123089134588885837 6899120296158425470832189)
      ·
        refine ⟨2587170111059409551562071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6899120296158425470832189 2587170111059409551562071)
        ·
          refine ⟨3880755166589114327343107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587170111059409551562071 3880755166589114327343107)
          ·
            refine ⟨5821132749883671491014661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880755166589114327343107 5821132749883671491014661)
            ·
              refine ⟨1091462390603188404565249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5821132749883671491014661 1091462390603188404565249)
              ·
                refine ⟨818596792952391303423937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091462390603188404565249 818596792952391303423937)
                ·
                  refine ⟨613947594714293477567953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818596792952391303423937 613947594714293477567953)
                  ·
                    refine ⟨460460696035720108175965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 613947594714293477567953 460460696035720108175965)
                    ·
                      refine ⟨172672761013395040565987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460460696035720108175965 172672761013395040565987)
                      ·
                        rfl

theorem cell23_336279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_336279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336279 prefixEnd_336279 := by exact prefixLift 336279
  have htrace : WordTrace (prefixWord ++ tailWord_336279) baseStart_336279 baseEnd_336279 := by
    simpa [prefixWord, tailWord_336279, baseEnd_336279] using wordTrace_append hprefix tailTrace_336279
  have hstable : (prefixWord ++ tailWord_336279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336279).length < 2 ^ (prefixWord ++ tailWord_336279).sum := by decide
  have hdescent : baseEnd_336279 < baseStart_336279 := by decide
  rcases family_descends (prefixWord ++ tailWord_336279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336366 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_336366 : Nat := 118140960795 + 336366 * 2 ^ 59
def prefixEnd_336366 : Nat := 4983230072969 + 3 ^ 40 * 336366 * 2
def baseEnd_336366 : Nat := 172717433830336200178087

theorem tailTrace_336366 : CollatzResearch.WordTrace tailWord_336366 prefixEnd_336366 172717433830336200178087 := by
  unfold tailWord_336366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533534487426362948042619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8178850599607269056227301 1533534487426362948042619)
  ·
    refine ⟨2300301731139544422063929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533534487426362948042619 2300301731139544422063929)
    ·
      refine ⟨1725226298354658316547947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300301731139544422063929 1725226298354658316547947)
      ·
        refine ⟨2587839447531987474821921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725226298354658316547947 2587839447531987474821921)
        ·
          refine ⟨1940879585648990606116441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2587839447531987474821921 1940879585648990606116441)
          ·
            refine ⟨1455659689236742954587331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1940879585648990606116441 1455659689236742954587331)
            ·
              refine ⟨2183489533855114431880997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455659689236742954587331 2183489533855114431880997)
              ·
                refine ⟨409404287597833955977687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2183489533855114431880997 409404287597833955977687)
                ·
                  refine ⟨614106431396750933966531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409404287597833955977687 614106431396750933966531)
                  ·
                    refine ⟨921159647095126400949797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 614106431396750933966531 921159647095126400949797)
                    ·
                      refine ⟨172717433830336200178087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 921159647095126400949797 172717433830336200178087)
                      ·
                        rfl

theorem cell23_336366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_336366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336366 prefixEnd_336366 := by exact prefixLift 336366
  have htrace : WordTrace (prefixWord ++ tailWord_336366) baseStart_336366 baseEnd_336366 := by
    simpa [prefixWord, tailWord_336366, baseEnd_336366] using wordTrace_append hprefix tailTrace_336366
  have hstable : (prefixWord ++ tailWord_336366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336366).length < 2 ^ (prefixWord ++ tailWord_336366).sum := by decide
  have hdescent : baseEnd_336366 < baseStart_336366 := by decide
  rcases family_descends (prefixWord ++ tailWord_336366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336459 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3]
def baseStart_336459 : Nat := 118140960795 + 336459 * 2 ^ 59
def prefixEnd_336459 : Nat := 4983230072969 + 3 ^ 40 * 336459 * 2
def baseEnd_336459 : Nat := 172765187531204336315159

theorem tailTrace_336459 : CollatzResearch.WordTrace tailWord_336459 prefixEnd_336459 172765187531204336315159 := by
  unfold tailWord_336459
  simp only [CollatzResearch.WordTrace]
  refine ⟨12271667888073980467476431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8181111925382653644984287 12271667888073980467476431)
  ·
    refine ⟨18407501832110970701214647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12271667888073980467476431 18407501832110970701214647)
    ·
      refine ⟨27611252748166456051821971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18407501832110970701214647 27611252748166456051821971)
      ·
        refine ⟨41416879122249684077732957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27611252748166456051821971 41416879122249684077732957)
        ·
          refine ⟨15531329670843631529149859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41416879122249684077732957 15531329670843631529149859)
          ·
            refine ⟨23296994506265447293724789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531329670843631529149859 23296994506265447293724789)
            ·
              refine ⟨2184093234962385683786699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23296994506265447293724789 2184093234962385683786699)
              ·
                refine ⟨3276139852443578525680049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184093234962385683786699 3276139852443578525680049)
                ·
                  refine ⟨2457104889332683894260037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3276139852443578525680049 2457104889332683894260037)
                  ·
                    refine ⟨460707166749878230173757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457104889332683894260037 460707166749878230173757)
                    ·
                      refine ⟨172765187531204336315159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460707166749878230173757 172765187531204336315159)
                      ·
                        rfl

theorem cell23_336459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].length) (baseStart_336459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336459 prefixEnd_336459 := by exact prefixLift 336459
  have htrace : WordTrace (prefixWord ++ tailWord_336459) baseStart_336459 baseEnd_336459 := by
    simpa [prefixWord, tailWord_336459, baseEnd_336459] using wordTrace_append hprefix tailTrace_336459
  have hstable : (prefixWord ++ tailWord_336459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336459).length < 2 ^ (prefixWord ++ tailWord_336459).sum := by decide
  have hdescent : baseEnd_336459 < baseStart_336459 := by decide
  rcases family_descends (prefixWord ++ tailWord_336459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336469 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_336469 : Nat := 118140960795 + 336469 * 2 ^ 59
def prefixEnd_336469 : Nat := 4983230072969 + 3 ^ 40 * 336469 * 2
def baseEnd_336469 : Nat := 172770322337749297190113

theorem tailTrace_336469 : CollatzResearch.WordTrace tailWord_336469 prefixEnd_336469 172770322337749297190113 := by
  unfold tailWord_336469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272032618037752175340461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8181355078691834783560307 12272032618037752175340461)
  ·
    refine ⟨4602012231764157065752673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12272032618037752175340461 4602012231764157065752673)
    ·
      refine ⟨3451509173823117799314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4602012231764157065752673 3451509173823117799314505)
      ·
        refine ⟨2588631880367338349485879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451509173823117799314505 2588631880367338349485879)
        ·
          refine ⟨3882947820551007524228819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588631880367338349485879 3882947820551007524228819)
          ·
            refine ⟨5824421730826511286343229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882947820551007524228819 5824421730826511286343229)
            ·
              refine ⟨2184158149059941732378711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5824421730826511286343229 2184158149059941732378711)
              ·
                refine ⟨3276237223589912598568067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184158149059941732378711 3276237223589912598568067)
                ·
                  refine ⟨4914355835384868897852101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276237223589912598568067 4914355835384868897852101)
                  ·
                    refine ⟨921441719134662918347269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914355835384868897852101 921441719134662918347269)
                    ·
                      refine ⟨172770322337749297190113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 921441719134662918347269 172770322337749297190113)
                      ·
                        rfl

theorem cell23_336469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_336469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336469 prefixEnd_336469 := by exact prefixLift 336469
  have htrace : WordTrace (prefixWord ++ tailWord_336469) baseStart_336469 baseEnd_336469 := by
    simpa [prefixWord, tailWord_336469, baseEnd_336469] using wordTrace_append hprefix tailTrace_336469
  have hstable : (prefixWord ++ tailWord_336469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336469).length < 2 ^ (prefixWord ++ tailWord_336469).sum := by decide
  have hdescent : baseEnd_336469 < baseStart_336469 := by decide
  rcases family_descends (prefixWord ++ tailWord_336469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336489 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_336489 : Nat := 118140960795 + 336489 * 2 ^ 59
def prefixEnd_336489 : Nat := 4983230072969 + 3 ^ 40 * 336489 * 2
def baseEnd_336489 : Nat := 172780591950839218940021

theorem tailTrace_336489 : CollatzResearch.WordTrace tailWord_336489 prefixEnd_336489 172780591950839218940021 := by
  unfold tailWord_336489
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272762077965295591068521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8181841385310197060712347 12272762077965295591068521)
  ·
    refine ⟨9204571558473971693301391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12272762077965295591068521 9204571558473971693301391)
    ·
      refine ⟨13806857337710957539952087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204571558473971693301391 13806857337710957539952087)
      ·
        refine ⟨20710286006566436309928131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13806857337710957539952087 20710286006566436309928131)
        ·
          refine ⟨31065429009849654464892197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20710286006566436309928131 31065429009849654464892197)
          ·
            refine ⟨5824767939346810212167287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31065429009849654464892197 5824767939346810212167287)
            ·
              refine ⟨8737151909020215318250931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824767939346810212167287 8737151909020215318250931)
              ·
                refine ⟨13105727863530322977376397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737151909020215318250931 13105727863530322977376397)
                ·
                  refine ⟨4914647948823871116516149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13105727863530322977376397 4914647948823871116516149)
                  ·
                    refine ⟨460748245202237917173389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4914647948823871116516149 460748245202237917173389)
                    ·
                      refine ⟨172780591950839218940021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460748245202237917173389 172780591950839218940021)
                      ·
                        rfl

theorem cell23_336489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_336489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336489 prefixEnd_336489 := by exact prefixLift 336489
  have htrace : WordTrace (prefixWord ++ tailWord_336489) baseStart_336489 baseEnd_336489 := by
    simpa [prefixWord, tailWord_336489, baseEnd_336489] using wordTrace_append hprefix tailTrace_336489
  have hstable : (prefixWord ++ tailWord_336489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336489).length < 2 ^ (prefixWord ++ tailWord_336489).sum := by decide
  have hdescent : baseEnd_336489 < baseStart_336489 := by decide
  rcases family_descends (prefixWord ++ tailWord_336489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336519 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_336519 : Nat := 118140960795 + 336519 * 2 ^ 59
def prefixEnd_336519 : Nat := 4983230072969 + 3 ^ 40 * 336519 * 2
def baseEnd_336519 : Nat := 172795996370474101564883

theorem tailTrace_336519 : CollatzResearch.WordTrace tailWord_336519 prefixEnd_336519 172795996370474101564883 := by
  unfold tailWord_336519
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273856267856610714660611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8182570845237740476440407 12273856267856610714660611)
  ·
    refine ⟨18410784401784916071990917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12273856267856610714660611 18410784401784916071990917)
    ·
      refine ⟨3452022075334671763498297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18410784401784916071990917 3452022075334671763498297)
      ·
        refine ⟨2589016556501003822623723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3452022075334671763498297 2589016556501003822623723)
        ·
          refine ⟨3883524834751505733935585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589016556501003822623723 3883524834751505733935585)
          ·
            refine ⟨2912643626063629300451689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3883524834751505733935585 2912643626063629300451689)
            ·
              refine ⟨2184482719547721975338767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912643626063629300451689 2184482719547721975338767)
              ·
                refine ⟨3276724079321582963008151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184482719547721975338767 3276724079321582963008151)
                ·
                  refine ⟨4915086118982374444512227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276724079321582963008151 4915086118982374444512227)
                  ·
                    refine ⟨7372629178473561666768341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915086118982374444512227 7372629178473561666768341)
                    ·
                      refine ⟨172795996370474101564883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7372629178473561666768341 172795996370474101564883)
                      ·
                        rfl

theorem cell23_336519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_336519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336519 prefixEnd_336519 := by exact prefixLift 336519
  have htrace : WordTrace (prefixWord ++ tailWord_336519) baseStart_336519 baseEnd_336519 := by
    simpa [prefixWord, tailWord_336519, baseEnd_336519] using wordTrace_append hprefix tailTrace_336519
  have hstable : (prefixWord ++ tailWord_336519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336519).length < 2 ^ (prefixWord ++ tailWord_336519).sum := by decide
  have hdescent : baseEnd_336519 < baseStart_336519 := by decide
  rcases family_descends (prefixWord ++ tailWord_336519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336549 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_336549 : Nat := 118140960795 + 336549 * 2 ^ 59
def prefixEnd_336549 : Nat := 4983230072969 + 3 ^ 40 * 336549 * 2
def baseEnd_336549 : Nat := 172811400790108984189745

theorem tailTrace_336549 : CollatzResearch.WordTrace tailWord_336549 prefixEnd_336549 172811400790108984189745 := by
  unfold tailWord_336549
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274950457747925838252701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8183300305165283892168467 12274950457747925838252701)
  ·
    refine ⟨4603106421655472189344763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12274950457747925838252701 4603106421655472189344763)
    ·
      refine ⟨6904659632483208284017145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603106421655472189344763 6904659632483208284017145)
      ·
        refine ⟨5178494724362406213012859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6904659632483208284017145 5178494724362406213012859)
        ·
          refine ⟨7767742086543609319519289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5178494724362406213012859 7767742086543609319519289)
          ·
            refine ⟨5825806564907706989639467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7767742086543609319519289 5825806564907706989639467)
            ·
              refine ⟨8738709847361560484459201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825806564907706989639467 8738709847361560484459201)
              ·
                refine ⟨6554032385521170363344401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8738709847361560484459201 6554032385521170363344401)
                ·
                  refine ⟨4915524289140877772508301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554032385521170363344401 4915524289140877772508301)
                  ·
                    refine ⟨1843321608427829164690613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4915524289140877772508301 1843321608427829164690613)
                    ·
                      refine ⟨172811400790108984189745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1843321608427829164690613 172811400790108984189745)
                      ·
                        rfl

theorem cell23_336549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_336549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336549 prefixEnd_336549 := by exact prefixLift 336549
  have htrace : WordTrace (prefixWord ++ tailWord_336549) baseStart_336549 baseEnd_336549 := by
    simpa [prefixWord, tailWord_336549, baseEnd_336549] using wordTrace_append hprefix tailTrace_336549
  have hstable : (prefixWord ++ tailWord_336549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336549).length < 2 ^ (prefixWord ++ tailWord_336549).sum := by decide
  have hdescent : baseEnd_336549 < baseStart_336549 := by decide
  rcases family_descends (prefixWord ++ tailWord_336549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336573 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_336573 : Nat := 118140960795 + 336573 * 2 ^ 59
def prefixEnd_336573 : Nat := 4983230072969 + 3 ^ 40 * 336573 * 2
def baseEnd_336573 : Nat := 57607908108605630096545

theorem tailTrace_336573 : CollatzResearch.WordTrace tailWord_336573 prefixEnd_336573 57607908108605630096545 := by
  unfold tailWord_336573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12275825809660977937126373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8183883873107318624750915 12275825809660977937126373)
  ·
    refine ⟨2301717339311433363211195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12275825809660977937126373 2301717339311433363211195)
    ·
      refine ⟨3452576008967150044816793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301717339311433363211195 3452576008967150044816793)
      ·
        refine ⟨2589432006725362533612595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3452576008967150044816793 2589432006725362533612595)
        ·
          refine ⟨3884148010088043800418893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589432006725362533612595 3884148010088043800418893)
          ·
            refine ⟨1456555503783016425157085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3884148010088043800418893 1456555503783016425157085)
            ·
              refine ⟨546208313918631159433907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1456555503783016425157085 546208313918631159433907)
              ·
                refine ⟨819312470877946739150861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546208313918631159433907 819312470877946739150861)
                ·
                  refine ⟨307242176579230027181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819312470877946739150861 307242176579230027181573)
                  ·
                    refine ⟨57607908108605630096545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307242176579230027181573 57607908108605630096545)
                    ·
                      rfl

theorem cell23_336573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_336573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336573 prefixEnd_336573 := by exact prefixLift 336573
  have htrace : WordTrace (prefixWord ++ tailWord_336573) baseStart_336573 baseEnd_336573 := by
    simpa [prefixWord, tailWord_336573, baseEnd_336573] using wordTrace_append hprefix tailTrace_336573
  have hstable : (prefixWord ++ tailWord_336573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336573).length < 2 ^ (prefixWord ++ tailWord_336573).sum := by decide
  have hdescent : baseEnd_336573 < baseStart_336573 := by decide
  rcases family_descends (prefixWord ++ tailWord_336573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
