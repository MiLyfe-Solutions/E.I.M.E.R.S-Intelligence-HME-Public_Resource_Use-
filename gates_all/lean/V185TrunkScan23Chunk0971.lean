import V185TrunkScan23Chunk0970

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5747783 : List Nat := [1, 1, 4, 1, 3, 2, 4, 7]
def baseStart_5747783 : Nat := 118140960795 + 5747783 * 2 ^ 59
def prefixEnd_5747783 : Nat := 4983230072969 + 3 ^ 40 * 5747783 * 2
def baseEnd_5747783 : Nat := 109310199138577426158479

theorem tailTrace_5747783 : CollatzResearch.WordTrace tailWord_5747783 prefixEnd_5747783 109310199138577426158479 := by
  unfold tailWord_5747783
  simp only [CollatzResearch.WordTrace]
  refine ⟨209638868535771309028904003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139759245690514206019269335 209638868535771309028904003)
  ·
    refine ⟨314458302803656963543356005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209638868535771309028904003 314458302803656963543356005)
    ·
      refine ⟨58960931775685680664379251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314458302803656963543356005 58960931775685680664379251)
      ·
        refine ⟨88441397663528520996568877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58960931775685680664379251 88441397663528520996568877)
        ·
          refine ⟨33165524123823195373713329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88441397663528520996568877 33165524123823195373713329)
          ·
            refine ⟨24874143092867396530284997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33165524123823195373713329 24874143092867396530284997)
            ·
              refine ⟨4663901829912636849428437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24874143092867396530284997 4663901829912636849428437)
              ·
                refine ⟨109310199138577426158479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4663901829912636849428437 109310199138577426158479)
                ·
                  rfl

theorem cell23_5747783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 7].length) (baseStart_5747783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747783 prefixEnd_5747783 := by exact prefixLift 5747783
  have htrace : WordTrace (prefixWord ++ tailWord_5747783) baseStart_5747783 baseEnd_5747783 := by
    simpa [prefixWord, tailWord_5747783, baseEnd_5747783] using wordTrace_append hprefix tailTrace_5747783
  have hstable : (prefixWord ++ tailWord_5747783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747783).length < 2 ^ (prefixWord ++ tailWord_5747783).sum := by decide
  have hdescent : baseEnd_5747783 < baseStart_5747783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747793 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_5747793 : Nat := 118140960795 + 5747793 * 2 ^ 59
def prefixEnd_5747793 : Nat := 4983230072969 + 3 ^ 40 * 5747793 * 2
def baseEnd_5747793 : Nat := 2951380511548135467153887

theorem tailTrace_5747793 : CollatzResearch.WordTrace tailWord_5747793 prefixEnd_5747793 2951380511548135467153887 := by
  unfold tailWord_5747793
  simp only [CollatzResearch.WordTrace]
  refine ⟨209639233265735080736768033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139759488843823387157845355 209639233265735080736768033)
  ·
    refine ⟨157229424949301310552576025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209639233265735080736768033 157229424949301310552576025)
    ·
      refine ⟨117922068711975982914432019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157229424949301310552576025 117922068711975982914432019)
      ·
        refine ⟨176883103067963974371648029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117922068711975982914432019 176883103067963974371648029)
        ·
          refine ⟨66331163650486490389368011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176883103067963974371648029 66331163650486490389368011)
          ·
            refine ⟨99496745475729735584052017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66331163650486490389368011 99496745475729735584052017)
            ·
              refine ⟨74622559106797301688039013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99496745475729735584052017 74622559106797301688039013)
              ·
                refine ⟨13991729832524494066507315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74622559106797301688039013 13991729832524494066507315)
                ·
                  refine ⟨20987594748786741099760973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13991729832524494066507315 20987594748786741099760973)
                  ·
                    refine ⟨7870348030795027912410365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20987594748786741099760973 7870348030795027912410365)
                    ·
                      refine ⟨2951380511548135467153887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870348030795027912410365 2951380511548135467153887)
                      ·
                        rfl

theorem cell23_5747793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_5747793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747793 prefixEnd_5747793 := by exact prefixLift 5747793
  have htrace : WordTrace (prefixWord ++ tailWord_5747793) baseStart_5747793 baseEnd_5747793 := by
    simpa [prefixWord, tailWord_5747793, baseEnd_5747793] using wordTrace_append hprefix tailTrace_5747793
  have hstable : (prefixWord ++ tailWord_5747793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747793).length < 2 ^ (prefixWord ++ tailWord_5747793).sum := by decide
  have hdescent : baseEnd_5747793 < baseStart_5747793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747820 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_5747820 : Nat := 118140960795 + 5747820 * 2 ^ 59
def prefixEnd_5747820 : Nat := 4983230072969 + 3 ^ 40 * 5747820 * 2
def baseEnd_5747820 : Nat := 2951394375525806861516263

theorem tailTrace_5747820 : CollatzResearch.WordTrace tailWord_5747820 prefixEnd_5747820 2951394375525806861516263 := by
  unfold tailWord_5747820
  simp only [CollatzResearch.WordTrace]
  refine ⟨104820109018318632174000457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139760145357758176232000609 104820109018318632174000457)
  ·
    refine ⟨78615081763738974130500343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104820109018318632174000457 78615081763738974130500343)
    ·
      refine ⟨117922622645608461195750515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78615081763738974130500343 117922622645608461195750515)
      ·
        refine ⟨176883933968412691793625773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117922622645608461195750515 176883933968412691793625773)
        ·
          refine ⟨66331475238154759422609665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176883933968412691793625773 66331475238154759422609665)
          ·
            refine ⟨49748606428616069566957249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66331475238154759422609665 49748606428616069566957249)
            ·
              refine ⟨37311454821462052175217937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49748606428616069566957249 37311454821462052175217937)
              ·
                refine ⟨27983591116096539131413453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37311454821462052175217937 27983591116096539131413453)
                ·
                  refine ⟨10493846668536202174280045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27983591116096539131413453 10493846668536202174280045)
                  ·
                    refine ⟨3935192500701075815355017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10493846668536202174280045 3935192500701075815355017)
                    ·
                      refine ⟨2951394375525806861516263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935192500701075815355017 2951394375525806861516263)
                      ·
                        rfl

theorem cell23_5747820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_5747820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747820 prefixEnd_5747820 := by exact prefixLift 5747820
  have htrace : WordTrace (prefixWord ++ tailWord_5747820) baseStart_5747820 baseEnd_5747820 := by
    simpa [prefixWord, tailWord_5747820, baseEnd_5747820] using wordTrace_append hprefix tailTrace_5747820
  have hstable : (prefixWord ++ tailWord_5747820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747820).length < 2 ^ (prefixWord ++ tailWord_5747820).sum := by decide
  have hdescent : baseEnd_5747820 < baseStart_5747820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747856 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 11]
def baseStart_5747856 : Nat := 118140960795 + 5747856 * 2 ^ 59
def prefixEnd_5747856 : Nat := 4983230072969 + 3 ^ 40 * 5747856 * 2
def baseEnd_5747856 : Nat := 327934762314374302296233

theorem tailTrace_5747856 : CollatzResearch.WordTrace tailWord_5747856 prefixEnd_5747856 327934762314374302296233 := by
  unfold tailWord_5747856
  simp only [CollatzResearch.WordTrace]
  refine ⟨104820765532253421248155711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139761020709671228330874281 104820765532253421248155711)
  ·
    refine ⟨157231148298380131872233567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104820765532253421248155711 157231148298380131872233567)
    ·
      refine ⟨235846722447570197808350351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157231148298380131872233567 235846722447570197808350351)
      ·
        refine ⟨353770083671355296712525527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235846722447570197808350351 353770083671355296712525527)
        ·
          refine ⟨530655125507032945068788291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353770083671355296712525527 530655125507032945068788291)
          ·
            refine ⟨795982688260549417603182437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530655125507032945068788291 795982688260549417603182437)
            ·
              refine ⟨149246754048853015800596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 795982688260549417603182437 149246754048853015800596707)
              ·
                refine ⟨223870131073279523700895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149246754048853015800596707 223870131073279523700895061)
                ·
                  refine ⟨327934762314374302296233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 223870131073279523700895061 327934762314374302296233)
                  ·
                    rfl

theorem cell23_5747856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_5747856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747856 prefixEnd_5747856 := by exact prefixLift 5747856
  have htrace : WordTrace (prefixWord ++ tailWord_5747856) baseStart_5747856 baseEnd_5747856 := by
    simpa [prefixWord, tailWord_5747856, baseEnd_5747856] using wordTrace_append hprefix tailTrace_5747856
  have hstable : (prefixWord ++ tailWord_5747856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747856).length < 2 ^ (prefixWord ++ tailWord_5747856).sum := by decide
  have hdescent : baseEnd_5747856 < baseStart_5747856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747873 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 7]
def baseStart_5747873 : Nat := 118140960795 + 5747873 * 2 ^ 59
def prefixEnd_5747873 : Nat := 4983230072969 + 3 ^ 40 * 5747873 * 2
def baseEnd_5747873 : Nat := 327935732222277239350391

theorem tailTrace_5747873 : CollatzResearch.WordTrace tailWord_5747873 prefixEnd_5747873 327935732222277239350391 := by
  unfold tailWord_5747873
  simp only [CollatzResearch.WordTrace]
  refine ⟨209642151105445254399680273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139761434070296836266453515 209642151105445254399680273)
  ·
    refine ⟨157231613329083940799760205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209642151105445254399680273 157231613329083940799760205)
    ·
      refine ⟨58961854998406477799910077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157231613329083940799760205 58961854998406477799910077)
      ·
        refine ⟨22110695624402429174966279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58961854998406477799910077 22110695624402429174966279)
        ·
          refine ⟨33166043436603643762449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22110695624402429174966279 33166043436603643762449419)
          ·
            refine ⟨49749065154905465643674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33166043436603643762449419 49749065154905465643674129)
            ·
              refine ⟨37311798866179099232755597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49749065154905465643674129 37311798866179099232755597)
              ·
                refine ⟨13991924574817162212283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37311798866179099232755597 13991924574817162212283349)
                ·
                  refine ⟨327935732222277239350391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13991924574817162212283349 327935732222277239350391)
                  ·
                    rfl

theorem cell23_5747873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_5747873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747873 prefixEnd_5747873 := by exact prefixLift 5747873
  have htrace : WordTrace (prefixWord ++ tailWord_5747873) baseStart_5747873 baseEnd_5747873 := by
    simpa [prefixWord, tailWord_5747873, baseEnd_5747873] using wordTrace_append hprefix tailTrace_5747873
  have hstable : (prefixWord ++ tailWord_5747873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747873).length < 2 ^ (prefixWord ++ tailWord_5747873).sum := by decide
  have hdescent : baseEnd_5747873 < baseStart_5747873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747918 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_5747918 : Nat := 118140960795 + 5747918 * 2 ^ 59
def prefixEnd_5747918 : Nat := 4983230072969 + 3 ^ 40 * 5747918 * 2
def baseEnd_5747918 : Nat := 2951444696629947478090813

theorem tailTrace_5747918 : CollatzResearch.WordTrace tailWord_5747918 prefixEnd_5747918 2951444696629947478090813 := by
  unfold tailWord_5747918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26205474048785278385633551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139762528260188151390045605 26205474048785278385633551)
  ·
    refine ⟨39308211073177917578450327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26205474048785278385633551 39308211073177917578450327)
    ·
      refine ⟨58962316609766876367675491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39308211073177917578450327 58962316609766876367675491)
      ·
        refine ⟨88443474914650314551513237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58962316609766876367675491 88443474914650314551513237)
        ·
          refine ⟨4145787886624233494602183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88443474914650314551513237 4145787886624233494602183)
          ·
            refine ⟨6218681829936350241903275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145787886624233494602183 6218681829936350241903275)
            ·
              refine ⟨9328022744904525362854913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218681829936350241903275 9328022744904525362854913)
              ·
                refine ⟨6996017058678394022141185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9328022744904525362854913 6996017058678394022141185)
                ·
                  refine ⟨5247012794008795516605889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6996017058678394022141185 5247012794008795516605889)
                  ·
                    refine ⟨3935259595506596637454417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247012794008795516605889 3935259595506596637454417)
                    ·
                      refine ⟨2951444696629947478090813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935259595506596637454417 2951444696629947478090813)
                      ·
                        rfl

theorem cell23_5747918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_5747918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747918 prefixEnd_5747918 := by exact prefixLift 5747918
  have htrace : WordTrace (prefixWord ++ tailWord_5747918) baseStart_5747918 baseEnd_5747918 := by
    simpa [prefixWord, tailWord_5747918, baseEnd_5747918] using wordTrace_append hprefix tailTrace_5747918
  have hstable : (prefixWord ++ tailWord_5747918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747918).length < 2 ^ (prefixWord ++ tailWord_5747918).sum := by decide
  have hdescent : baseEnd_5747918 < baseStart_5747918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747953 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_5747953 : Nat := 118140960795 + 5747953 * 2 ^ 59
def prefixEnd_5747953 : Nat := 4983230072969 + 3 ^ 40 * 5747953 * 2
def baseEnd_5747953 : Nat := 2951462668452854841153151

theorem tailTrace_5747953 : CollatzResearch.WordTrace tailWord_5747953 prefixEnd_5747953 2951462668452854841153151 := by
  unfold tailWord_5747953
  simp only [CollatzResearch.WordTrace]
  refine ⟨209645068945155428062592513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139763379296770285375061675 209645068945155428062592513)
  ·
    refine ⟨157233801708866571046944385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209645068945155428062592513 157233801708866571046944385)
    ·
      refine ⟨117925351281649928285208289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157233801708866571046944385 117925351281649928285208289)
      ·
        refine ⟨88444013461237446213906217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117925351281649928285208289 88444013461237446213906217)
        ·
          refine ⟨66333010095928084660429663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88444013461237446213906217 66333010095928084660429663)
          ·
            refine ⟨99499515143892126990644495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66333010095928084660429663 99499515143892126990644495)
            ·
              refine ⟨149249272715838190485966743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99499515143892126990644495 149249272715838190485966743)
              ·
                refine ⟨223873909073757285728950115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149249272715838190485966743 223873909073757285728950115)
                ·
                  refine ⟨335810863610635928593425173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223873909073757285728950115 335810863610635928593425173)
                  ·
                    refine ⟨15741134231748559152816805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 335810863610635928593425173 15741134231748559152816805)
                    ·
                      refine ⟨2951462668452854841153151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15741134231748559152816805 2951462668452854841153151)
                      ·
                        rfl

theorem cell23_5747953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_5747953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747953 prefixEnd_5747953 := by exact prefixLift 5747953
  have htrace : WordTrace (prefixWord ++ tailWord_5747953) baseStart_5747953 baseEnd_5747953 := by
    simpa [prefixWord, tailWord_5747953, baseEnd_5747953] using wordTrace_append hprefix tailTrace_5747953
  have hstable : (prefixWord ++ tailWord_5747953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747953).length < 2 ^ (prefixWord ++ tailWord_5747953).sum := by decide
  have hdescent : baseEnd_5747953 < baseStart_5747953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5747997 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 6]
def baseStart_5747997 : Nat := 118140960795 + 5747997 * 2 ^ 59
def prefixEnd_5747997 : Nat := 4983230072969 + 3 ^ 40 * 5747997 * 2
def baseEnd_5747997 : Nat := 327942806844628074333661

theorem tailTrace_5747997 : CollatzResearch.WordTrace tailWord_5747997 prefixEnd_5747997 327942806844628074333661 := by
  unfold tailWord_5747997
  simp only [CollatzResearch.WordTrace]
  refine ⟨209646673756996023577194245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139764449171330682384796163 209646673756996023577194245)
  ·
    refine ⟨39308751329436754420723921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209646673756996023577194245 39308751329436754420723921)
    ·
      refine ⟨29481563497077565815542941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39308751329436754420723921 29481563497077565815542941)
      ·
        refine ⟨11055586311404087180828603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29481563497077565815542941 11055586311404087180828603)
        ·
          refine ⟨16583379467106130771242905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055586311404087180828603 16583379467106130771242905)
          ·
            refine ⟨12437534600329598078432179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16583379467106130771242905 12437534600329598078432179)
            ·
              refine ⟨18656301900494397117648269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12437534600329598078432179 18656301900494397117648269)
              ·
                refine ⟨6996113212685398919118101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18656301900494397117648269 6996113212685398919118101)
                ·
                  refine ⟨327942806844628074333661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6996113212685398919118101 327942806844628074333661)
                  ·
                    rfl

theorem cell23_5747997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_5747997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5747997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5747997 prefixEnd_5747997 := by exact prefixLift 5747997
  have htrace : WordTrace (prefixWord ++ tailWord_5747997) baseStart_5747997 baseEnd_5747997 := by
    simpa [prefixWord, tailWord_5747997, baseEnd_5747997] using wordTrace_append hprefix tailTrace_5747997
  have hstable : (prefixWord ++ tailWord_5747997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5747997).length < 2 ^ (prefixWord ++ tailWord_5747997).sum := by decide
  have hdescent : baseEnd_5747997 < baseStart_5747997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5747997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_5748024 : Nat := 118140960795 + 5748024 * 2 ^ 59
def prefixEnd_5748024 : Nat := 4983230072969 + 3 ^ 40 * 5748024 * 2
def baseEnd_5748024 : Nat := 2951499125579324063365325

theorem tailTrace_5748024 : CollatzResearch.WordTrace tailWord_5748024 prefixEnd_5748024 2951499125579324063365325 := by
  unfold tailWord_5748024
  simp only [CollatzResearch.WordTrace]
  refine ⟨104823829263949103594213563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139765105685265471458951417 104823829263949103594213563)
  ·
    refine ⟨157235743895923655391320345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104823829263949103594213563 157235743895923655391320345)
    ·
      refine ⟨117926807921942741543490259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157235743895923655391320345 117926807921942741543490259)
      ·
        refine ⟨176890211882914112315235389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117926807921942741543490259 176890211882914112315235389)
        ·
          refine ⟨66333829456092792118213271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176890211882914112315235389 66333829456092792118213271)
          ·
            refine ⟨99500744184139188177319907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66333829456092792118213271 99500744184139188177319907)
            ·
              refine ⟨149251116276208782265979861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99500744184139188177319907 149251116276208782265979861)
              ·
                refine ⟨3498073037723643334358903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149251116276208782265979861 3498073037723643334358903)
                ·
                  refine ⟨5247109556585465001538355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498073037723643334358903 5247109556585465001538355)
                  ·
                    refine ⟨7870664334878197502307533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247109556585465001538355 7870664334878197502307533)
                    ·
                      refine ⟨2951499125579324063365325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870664334878197502307533 2951499125579324063365325)
                      ·
                        rfl

theorem cell23_5748024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_5748024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748024 prefixEnd_5748024 := by exact prefixLift 5748024
  have htrace : WordTrace (prefixWord ++ tailWord_5748024) baseStart_5748024 baseEnd_5748024 := by
    simpa [prefixWord, tailWord_5748024, baseEnd_5748024] using wordTrace_append hprefix tailTrace_5748024
  have hstable : (prefixWord ++ tailWord_5748024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748024).length < 2 ^ (prefixWord ++ tailWord_5748024).sum := by decide
  have hdescent : baseEnd_5748024 < baseStart_5748024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748041 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 1, 1, 3]
def baseStart_5748041 : Nat := 118140960795 + 5748041 * 2 ^ 59
def prefixEnd_5748041 : Nat := 4983230072969 + 3 ^ 40 * 5748041 * 2
def baseEnd_5748041 : Nat := 2951507854750450496852747

theorem tailTrace_5748041 : CollatzResearch.WordTrace tailWord_5748041 prefixEnd_5748041 2951507854750450496852747 := by
  unfold tailWord_5748041
  simp only [CollatzResearch.WordTrace]
  refine ⟨209648278568836619091795977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139765519045891079394530651 209648278568836619091795977)
  ·
    refine ⟨157236208926627464318846983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209648278568836619091795977 157236208926627464318846983)
    ·
      refine ⟨235854313389941196478270475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157236208926627464318846983 235854313389941196478270475)
      ·
        refine ⟨353781470084911794717405713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235854313389941196478270475 353781470084911794717405713)
        ·
          refine ⟨265336102563683846038054285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353781470084911794717405713 265336102563683846038054285)
          ·
            refine ⟨99501038461381442264270357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265336102563683846038054285 99501038461381442264270357)
            ·
              refine ⟨4664111177877255106137673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99501038461381442264270357 4664111177877255106137673)
              ·
                refine ⟨3498083383407941329603255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664111177877255106137673 3498083383407941329603255)
                ·
                  refine ⟨5247125075111911994404883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498083383407941329603255 5247125075111911994404883)
                  ·
                    refine ⟨7870687612667867991607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247125075111911994404883 7870687612667867991607325)
                    ·
                      refine ⟨2951507854750450496852747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870687612667867991607325 2951507854750450496852747)
                      ·
                        rfl

theorem cell23_5748041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 1, 1, 3].length) (baseStart_5748041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748041 prefixEnd_5748041 := by exact prefixLift 5748041
  have htrace : WordTrace (prefixWord ++ tailWord_5748041) baseStart_5748041 baseEnd_5748041 := by
    simpa [prefixWord, tailWord_5748041, baseEnd_5748041] using wordTrace_append hprefix tailTrace_5748041
  have hstable : (prefixWord ++ tailWord_5748041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748041).length < 2 ^ (prefixWord ++ tailWord_5748041).sum := by decide
  have hdescent : baseEnd_5748041 < baseStart_5748041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748050 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5748050 : Nat := 118140960795 + 5748050 * 2 ^ 59
def prefixEnd_5748050 : Nat := 4983230072969 + 3 ^ 40 * 5748050 * 2
def baseEnd_5748050 : Nat := 2951512476076340961640205

theorem tailTrace_5748050 : CollatzResearch.WordTrace tailWord_5748050 prefixEnd_5748050 2951512476076340961640205 := by
  unfold tailWord_5748050
  simp only [CollatzResearch.WordTrace]
  refine ⟨52412151706451003407218401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139765737883869342419249069 52412151706451003407218401)
  ·
    refine ⟨39309113779838252555413801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52412151706451003407218401 39309113779838252555413801)
    ·
      refine ⟨29481835334878689416560351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39309113779838252555413801 29481835334878689416560351)
      ·
        refine ⟨44222753002318034124840527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29481835334878689416560351 44222753002318034124840527)
        ·
          refine ⟨66334129503477051187260791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44222753002318034124840527 66334129503477051187260791)
          ·
            refine ⟨99501194255215576780891187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66334129503477051187260791 99501194255215576780891187)
            ·
              refine ⟨149251791382823365171336781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99501194255215576780891187 149251791382823365171336781)
              ·
                refine ⟨55969421768558761939251293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149251791382823365171336781 55969421768558761939251293)
                ·
                  refine ⟨20988533163209535727219235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55969421768558761939251293 20988533163209535727219235)
                  ·
                    refine ⟨31482799744814303590828853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20988533163209535727219235 31482799744814303590828853)
                    ·
                      refine ⟨2951512476076340961640205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31482799744814303590828853 2951512476076340961640205)
                      ·
                        rfl

theorem cell23_5748050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5748050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748050 prefixEnd_5748050 := by exact prefixLift 5748050
  have htrace : WordTrace (prefixWord ++ tailWord_5748050) baseStart_5748050 baseEnd_5748050 := by
    simpa [prefixWord, tailWord_5748050, baseEnd_5748050] using wordTrace_append hprefix tailTrace_5748050
  have hstable : (prefixWord ++ tailWord_5748050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748050).length < 2 ^ (prefixWord ++ tailWord_5748050).sum := by decide
  have hdescent : baseEnd_5748050 < baseStart_5748050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748057 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_5748057 : Nat := 118140960795 + 5748057 * 2 ^ 59
def prefixEnd_5748057 : Nat := 4983230072969 + 3 ^ 40 * 5748057 * 2
def baseEnd_5748057 : Nat := 983838690146974144750891

theorem tailTrace_5748057 : CollatzResearch.WordTrace tailWord_5748057 prefixEnd_5748057 983838690146974144750891 := by
  unfold tailWord_5748057
  simp only [CollatzResearch.WordTrace]
  refine ⟨209648862136778653824378425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139765908091185769216252283 209648862136778653824378425)
  ·
    refine ⟨157236646602583990368283819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209648862136778653824378425 157236646602583990368283819)
    ·
      refine ⟨235854969903875985552425729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157236646602583990368283819 235854969903875985552425729)
      ·
        refine ⟨176891227427906989164319297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235854969903875985552425729 176891227427906989164319297)
        ·
          refine ⟨132668420570930241873239473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176891227427906989164319297 132668420570930241873239473)
          ·
            refine ⟨99501315428197681404929605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132668420570930241873239473 99501315428197681404929605)
            ·
              refine ⟨18656496642787065263424301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99501315428197681404929605 18656496642787065263424301)
              ·
                refine ⟨6996186241045149473784113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18656496642787065263424301 6996186241045149473784113)
                ·
                  refine ⟨5247139680783862105338085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6996186241045149473784113 5247139680783862105338085)
                  ·
                    refine ⟨983838690146974144750891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247139680783862105338085 983838690146974144750891)
                    ·
                      rfl

theorem cell23_5748057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_5748057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748057 prefixEnd_5748057 := by exact prefixLift 5748057
  have htrace : WordTrace (prefixWord ++ tailWord_5748057) baseStart_5748057 baseEnd_5748057 := by
    simpa [prefixWord, tailWord_5748057, baseEnd_5748057] using wordTrace_append hprefix tailTrace_5748057
  have hstable : (prefixWord ++ tailWord_5748057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748057).length < 2 ^ (prefixWord ++ tailWord_5748057).sum := by decide
  have hdescent : baseEnd_5748057 < baseStart_5748057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748064 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2]
def baseStart_5748064 : Nat := 118140960795 + 5748064 * 2 ^ 59
def prefixEnd_5748064 : Nat := 4983230072969 + 3 ^ 40 * 5748064 * 2
def baseEnd_5748064 : Nat := 2951519664805503906865141

theorem tailTrace_5748064 : CollatzResearch.WordTrace tailWord_5748064 prefixEnd_5748064 2951519664805503906865141 := by
  unfold tailWord_5748064
  simp only [CollatzResearch.WordTrace]
  refine ⟨104824558723876647009941623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139766078298502196013255497 104824558723876647009941623)
  ·
    refine ⟨157236838085814970514912435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104824558723876647009941623 157236838085814970514912435)
    ·
      refine ⟨235855257128722455772368653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157236838085814970514912435 235855257128722455772368653)
      ·
        refine ⟨88445721423270920914638245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235855257128722455772368653 88445721423270920914638245)
        ·
          refine ⟨16583572766863297671494671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88445721423270920914638245 16583572766863297671494671)
          ·
            refine ⟨24875359150294946507242007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16583572766863297671494671 24875359150294946507242007)
            ·
              refine ⟨37313038725442419760863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24875359150294946507242007 37313038725442419760863011)
              ·
                refine ⟨55969558088163629641294517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37313038725442419760863011 55969558088163629641294517)
                ·
                  refine ⟨5247146070765340278871361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55969558088163629641294517 5247146070765340278871361)
                  ·
                    refine ⟨3935359553074005209153521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247146070765340278871361 3935359553074005209153521)
                    ·
                      refine ⟨2951519664805503906865141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935359553074005209153521 2951519664805503906865141)
                      ·
                        rfl

theorem cell23_5748064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_5748064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748064 prefixEnd_5748064 := by exact prefixLift 5748064
  have htrace : WordTrace (prefixWord ++ tailWord_5748064) baseStart_5748064 baseEnd_5748064 := by
    simpa [prefixWord, tailWord_5748064, baseEnd_5748064] using wordTrace_append hprefix tailTrace_5748064
  have hstable : (prefixWord ++ tailWord_5748064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748064).length < 2 ^ (prefixWord ++ tailWord_5748064).sum := by decide
  have hdescent : baseEnd_5748064 < baseStart_5748064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748067 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5748067 : Nat := 118140960795 + 5748067 * 2 ^ 59
def prefixEnd_5748067 : Nat := 4983230072969 + 3 ^ 40 * 5748067 * 2
def baseEnd_5748067 : Nat := 2951521205247467395127627

theorem tailTrace_5748067 : CollatzResearch.WordTrace tailWord_5748067 prefixEnd_5748067 2951521205247467395127627 := by
  unfold tailWord_5748067
  simp only [CollatzResearch.WordTrace]
  refine ⟨209649226866742425532242455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139766151244494950354828303 209649226866742425532242455)
  ·
    refine ⟨314473840300113638298363683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209649226866742425532242455 314473840300113638298363683)
    ·
      refine ⟨471710760450170457447545525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314473840300113638298363683 471710760450170457447545525)
      ·
        refine ⟨44222883792203480385707393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 471710760450170457447545525 44222883792203480385707393)
        ·
          refine ⟨33167162844152610289280545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44222883792203480385707393 33167162844152610289280545)
          ·
            refine ⟨24875372133114457716960409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33167162844152610289280545 24875372133114457716960409)
            ·
              refine ⟨18656529099835843287720307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24875372133114457716960409 18656529099835843287720307)
              ·
                refine ⟨27984793649753764931580461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18656529099835843287720307 27984793649753764931580461)
                ·
                  refine ⟨10494297618657661849342673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27984793649753764931580461 10494297618657661849342673)
                  ·
                    refine ⟨7870723213993246387007005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10494297618657661849342673 7870723213993246387007005)
                    ·
                      refine ⟨2951521205247467395127627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870723213993246387007005 2951521205247467395127627)
                      ·
                        rfl

theorem cell23_5748067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5748067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748067 prefixEnd_5748067 := by exact prefixLift 5748067
  have htrace : WordTrace (prefixWord ++ tailWord_5748067) baseStart_5748067 baseEnd_5748067 := by
    simpa [prefixWord, tailWord_5748067, baseEnd_5748067] using wordTrace_append hprefix tailTrace_5748067
  have hstable : (prefixWord ++ tailWord_5748067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748067).length < 2 ^ (prefixWord ++ tailWord_5748067).sum := by decide
  have hdescent : baseEnd_5748067 < baseStart_5748067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748077 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5748077 : Nat := 118140960795 + 5748077 * 2 ^ 59
def prefixEnd_5748077 : Nat := 4983230072969 + 3 ^ 40 * 5748077 * 2
def baseEnd_5748077 : Nat := 2951526340054012356002581

theorem tailTrace_5748077 : CollatzResearch.WordTrace tailWord_5748077 prefixEnd_5748077 2951526340054012356002581 := by
  unfold tailWord_5748077
  simp only [CollatzResearch.WordTrace]
  refine ⟨209649591596706197240106485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139766394397804131493404323 209649591596706197240106485)
  ·
    refine ⟨19654649212191205991259983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209649591596706197240106485 19654649212191205991259983)
    ·
      refine ⟨29481973818286808986889975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19654649212191205991259983 29481973818286808986889975)
      ·
        refine ⟨44222960727430213480334963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29481973818286808986889975 44222960727430213480334963)
        ·
          refine ⟨66334441091145320220502445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44222960727430213480334963 66334441091145320220502445)
          ·
            refine ⟨24875415409179495082688417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66334441091145320220502445 24875415409179495082688417)
            ·
              refine ⟨18656561556884621312016313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24875415409179495082688417 18656561556884621312016313)
              ·
                refine ⟨13992421167663465984012235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18656561556884621312016313 13992421167663465984012235)
                ·
                  refine ⟨20988631751495198976018353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13992421167663465984012235 20988631751495198976018353)
                  ·
                    refine ⟨15741473813621399232013765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20988631751495198976018353 15741473813621399232013765)
                    ·
                      refine ⟨2951526340054012356002581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15741473813621399232013765 2951526340054012356002581)
                      ·
                        rfl

theorem cell23_5748077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5748077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748077 prefixEnd_5748077 := by exact prefixLift 5748077
  have htrace : WordTrace (prefixWord ++ tailWord_5748077) baseStart_5748077 baseEnd_5748077 := by
    simpa [prefixWord, tailWord_5748077, baseEnd_5748077] using wordTrace_append hprefix tailTrace_5748077
  have hstable : (prefixWord ++ tailWord_5748077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748077).length < 2 ^ (prefixWord ++ tailWord_5748077).sum := by decide
  have hdescent : baseEnd_5748077 < baseStart_5748077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748078 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5748078 : Nat := 118140960795 + 5748078 * 2 ^ 59
def prefixEnd_5748078 : Nat := 4983230072969 + 3 ^ 40 * 5748078 * 2
def baseEnd_5748078 : Nat := 983842284511555617363359

theorem tailTrace_5748078 : CollatzResearch.WordTrace tailWord_5748078 prefixEnd_5748078 983842284511555617363359 := by
  unfold tailWord_5748078
  simp only [CollatzResearch.WordTrace]
  refine ⟨26206203508712821801361611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139766418713135049607261925 26206203508712821801361611)
  ·
    refine ⟨39309305263069232702042417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26206203508712821801361611 39309305263069232702042417)
    ·
      refine ⟨29481978947301924526531813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39309305263069232702042417 29481978947301924526531813)
      ·
        refine ⟨5527871052619110848724715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29481978947301924526531813 5527871052619110848724715)
        ·
          refine ⟨8291806578928666273087073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527871052619110848724715 8291806578928666273087073)
          ·
            refine ⟨6218854934196499704815305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8291806578928666273087073 6218854934196499704815305)
            ·
              refine ⟨4664141200647374778611479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6218854934196499704815305 4664141200647374778611479)
              ·
                refine ⟨6996211800971062167917219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664141200647374778611479 6996211800971062167917219)
                ·
                  refine ⟨10494317701456593251875829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6996211800971062167917219 10494317701456593251875829)
                  ·
                    refine ⟨983842284511555617363359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10494317701456593251875829 983842284511555617363359)
                    ·
                      rfl

theorem cell23_5748078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5748078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748078 prefixEnd_5748078 := by exact prefixLift 5748078
  have htrace : WordTrace (prefixWord ++ tailWord_5748078) baseStart_5748078 baseEnd_5748078 := by
    simpa [prefixWord, tailWord_5748078, baseEnd_5748078] using wordTrace_append hprefix tailTrace_5748078
  have hstable : (prefixWord ++ tailWord_5748078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748078).length < 2 ^ (prefixWord ++ tailWord_5748078).sum := by decide
  have hdescent : baseEnd_5748078 < baseStart_5748078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748081 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_5748081 : Nat := 118140960795 + 5748081 * 2 ^ 59
def prefixEnd_5748081 : Nat := 4983230072969 + 3 ^ 40 * 5748081 * 2
def baseEnd_5748081 : Nat := 2951528393976630340352563

theorem tailTrace_5748081 : CollatzResearch.WordTrace tailWord_5748081 prefixEnd_5748081 2951528393976630340352563 := by
  unfold tailWord_5748081
  simp only [CollatzResearch.WordTrace]
  refine ⟨209649737488691705923252097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139766491659127803948834731 209649737488691705923252097)
  ·
    refine ⟨157237303116518779442439073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209649737488691705923252097 157237303116518779442439073)
    ·
      refine ⟨117927977337389084581829305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157237303116518779442439073 117927977337389084581829305)
      ·
        refine ⟨88445983003041813436371979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117927977337389084581829305 88445983003041813436371979)
        ·
          refine ⟨132668974504562720154557969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88445983003041813436371979 132668974504562720154557969)
          ·
            refine ⟨99501730878422040115918477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132668974504562720154557969 99501730878422040115918477)
            ·
              refine ⟨37313149079408265043469429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99501730878422040115918477 37313149079408265043469429)
              ·
                refine ⟨3498107726194524847825259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37313149079408265043469429 3498107726194524847825259)
                ·
                  refine ⟨5247161589291787271737889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498107726194524847825259 5247161589291787271737889)
                  ·
                    refine ⟨3935371191968840453803417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247161589291787271737889 3935371191968840453803417)
                    ·
                      refine ⟨2951528393976630340352563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935371191968840453803417 2951528393976630340352563)
                      ·
                        rfl

theorem cell23_5748081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_5748081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748081 prefixEnd_5748081 := by exact prefixLift 5748081
  have htrace : WordTrace (prefixWord ++ tailWord_5748081) baseStart_5748081 baseEnd_5748081 := by
    simpa [prefixWord, tailWord_5748081, baseEnd_5748081] using wordTrace_append hprefix tailTrace_5748081
  have hstable : (prefixWord ++ tailWord_5748081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748081).length < 2 ^ (prefixWord ++ tailWord_5748081).sum := by decide
  have hdescent : baseEnd_5748081 < baseStart_5748081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748098 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5748098 : Nat := 118140960795 + 5748098 * 2 ^ 59
def prefixEnd_5748098 : Nat := 4983230072969 + 3 ^ 40 * 5748098 * 2
def baseEnd_5748098 : Nat := 2951537123147756773839985

theorem tailTrace_5748098 : CollatzResearch.WordTrace tailWord_5748098 prefixEnd_5748098 2951537123147756773839985 := by
  unfold tailWord_5748098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52412589382407529456655237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139766905019753411884413965 52412589382407529456655237)
  ·
    refine ⟨9827360509201411773122857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52412589382407529456655237 9827360509201411773122857)
    ·
      refine ⟨7370520381901058829842143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9827360509201411773122857 7370520381901058829842143)
      ·
        refine ⟨11055780572851588244763215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370520381901058829842143 11055780572851588244763215)
        ·
          refine ⟨16583670859277382367144823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055780572851588244763215 16583670859277382367144823)
          ·
            refine ⟨24875506288916073550717235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16583670859277382367144823 24875506288916073550717235)
            ·
              refine ⟨37313259433374110326075853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24875506288916073550717235 37313259433374110326075853)
              ·
                refine ⟨13992472287515291372278445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37313259433374110326075853 13992472287515291372278445)
                ·
                  refine ⟨5247177107818234264604417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13992472287515291372278445 5247177107818234264604417)
                  ·
                    refine ⟨3935382830863675698453313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247177107818234264604417 3935382830863675698453313)
                    ·
                      refine ⟨2951537123147756773839985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935382830863675698453313 2951537123147756773839985)
                      ·
                        rfl

theorem cell23_5748098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5748098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748098 prefixEnd_5748098 := by exact prefixLift 5748098
  have htrace : WordTrace (prefixWord ++ tailWord_5748098) baseStart_5748098 baseEnd_5748098 := by
    simpa [prefixWord, tailWord_5748098, baseEnd_5748098] using wordTrace_append hprefix tailTrace_5748098
  have hstable : (prefixWord ++ tailWord_5748098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748098).length < 2 ^ (prefixWord ++ tailWord_5748098).sum := by decide
  have hdescent : baseEnd_5748098 < baseStart_5748098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748140 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_5748140 : Nat := 118140960795 + 5748140 * 2 ^ 59
def prefixEnd_5748140 : Nat := 4983230072969 + 3 ^ 40 * 5748140 * 2
def baseEnd_5748140 : Nat := 2951558689335245609514791

theorem tailTrace_5748140 : CollatzResearch.WordTrace tailWord_5748140 prefixEnd_5748140 2951558689335245609514791 := by
  unfold tailWord_5748140
  simp only [CollatzResearch.WordTrace]
  refine ⟨104825944697738979499824937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139767926263651972666433249 104825944697738979499824937)
  ·
    refine ⟨78619458523304234624868703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104825944697738979499824937 78619458523304234624868703)
    ·
      refine ⟨117929187784956351937303055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78619458523304234624868703 117929187784956351937303055)
      ·
        refine ⟨176893781677434527905954583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117929187784956351937303055 176893781677434527905954583)
        ·
          refine ⟨265340672516151791858931875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176893781677434527905954583 265340672516151791858931875)
          ·
            refine ⟨398011008774227687788397813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265340672516151791858931875 398011008774227687788397813)
            ·
              refine ⟨37313532072583845730162295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398011008774227687788397813 37313532072583845730162295)
              ·
                refine ⟨55970298108875768595243443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37313532072583845730162295 55970298108875768595243443)
                ·
                  refine ⟨83955447163313652892865165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55970298108875768595243443 83955447163313652892865165)
                  ·
                    refine ⟨31483292686242619834824437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83955447163313652892865165 31483292686242619834824437)
                    ·
                      refine ⟨2951558689335245609514791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31483292686242619834824437 2951558689335245609514791)
                      ·
                        rfl

theorem cell23_5748140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_5748140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748140 prefixEnd_5748140 := by exact prefixLift 5748140
  have htrace : WordTrace (prefixWord ++ tailWord_5748140) baseStart_5748140 baseEnd_5748140 := by
    simpa [prefixWord, tailWord_5748140, baseEnd_5748140] using wordTrace_append hprefix tailTrace_5748140
  have hstable : (prefixWord ++ tailWord_5748140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748140).length < 2 ^ (prefixWord ++ tailWord_5748140).sum := by decide
  have hdescent : baseEnd_5748140 < baseStart_5748140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748157 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5748157 : Nat := 118140960795 + 5748157 * 2 ^ 59
def prefixEnd_5748157 : Nat := 4983230072969 + 3 ^ 40 * 5748157 * 2
def baseEnd_5748157 : Nat := 2951567418506372043002213

theorem tailTrace_5748157 : CollatzResearch.WordTrace tailWord_5748157 prefixEnd_5748157 2951567418506372043002213 := by
  unfold tailWord_5748157
  simp only [CollatzResearch.WordTrace]
  refine ⟨209652509436416370903018725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139768339624277580602012483 209652509436416370903018725)
  ·
    refine ⟨39309845519328069544316011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209652509436416370903018725 39309845519328069544316011)
    ·
      refine ⟨58964768278992104316474017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39309845519328069544316011 58964768278992104316474017)
      ·
        refine ⟨44223576209244078237355513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58964768278992104316474017 44223576209244078237355513)
        ·
          refine ⟨33167682156933058678016635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44223576209244078237355513 33167682156933058678016635)
          ·
            refine ⟨49751523235399588017024953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33167682156933058678016635 49751523235399588017024953)
            ·
              refine ⟨37313642426549691012768715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49751523235399588017024953 37313642426549691012768715)
              ·
                refine ⟨55970463639824536519153073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37313642426549691012768715 55970463639824536519153073)
                ·
                  refine ⟨41977847729868402389364805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55970463639824536519153073 41977847729868402389364805)
                  ·
                    refine ⟨7870846449350325448005901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41977847729868402389364805 7870846449350325448005901)
                    ·
                      refine ⟨2951567418506372043002213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7870846449350325448005901 2951567418506372043002213)
                      ·
                        rfl

theorem cell23_5748157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5748157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748157 prefixEnd_5748157 := by exact prefixLift 5748157
  have htrace : WordTrace (prefixWord ++ tailWord_5748157) baseStart_5748157 baseEnd_5748157 := by
    simpa [prefixWord, tailWord_5748157, baseEnd_5748157] using wordTrace_append hprefix tailTrace_5748157
  have hstable : (prefixWord ++ tailWord_5748157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748157).length < 2 ^ (prefixWord ++ tailWord_5748157).sum := by decide
  have hdescent : baseEnd_5748157 < baseStart_5748157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748205 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5748205 : Nat := 118140960795 + 5748205 * 2 ^ 59
def prefixEnd_5748205 : Nat := 4983230072969 + 3 ^ 40 * 5748205 * 2
def baseEnd_5748205 : Nat := 2951592065577787855201993

theorem tailTrace_5748205 : CollatzResearch.WordTrace tailWord_5748205 prefixEnd_5748205 2951592065577787855201993 := by
  unfold tailWord_5748205
  simp only [CollatzResearch.WordTrace]
  refine ⟨209654260140242475100766069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139769506760161650067177379 209654260140242475100766069)
  ·
    refine ⟨19655086888147732040696819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209654260140242475100766069 19655086888147732040696819)
    ·
      refine ⟨29482630332221598061045229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655086888147732040696819 29482630332221598061045229)
      ·
        refine ⟨11055986374583099272891961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29482630332221598061045229 11055986374583099272891961)
        ·
          refine ⟨8291989780937324454668971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11055986374583099272891961 8291989780937324454668971)
          ·
            refine ⟨12437984671405986682003457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8291989780937324454668971 12437984671405986682003457)
            ·
              refine ⟨9328488503554490011502593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12437984671405986682003457 9328488503554490011502593)
              ·
                refine ⟨6996366377665867508626945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9328488503554490011502593 6996366377665867508626945)
                ·
                  refine ⟨5247274783249400631470209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6996366377665867508626945 5247274783249400631470209)
                  ·
                    refine ⟨3935456087437050473602657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247274783249400631470209 3935456087437050473602657)
                    ·
                      refine ⟨2951592065577787855201993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935456087437050473602657 2951592065577787855201993)
                      ·
                        rfl

theorem cell23_5748205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5748205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748205 prefixEnd_5748205 := by exact prefixLift 5748205
  have htrace : WordTrace (prefixWord ++ tailWord_5748205) baseStart_5748205 baseEnd_5748205 := by
    simpa [prefixWord, tailWord_5748205, baseEnd_5748205] using wordTrace_append hprefix tailTrace_5748205
  have hstable : (prefixWord ++ tailWord_5748205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748205).length < 2 ^ (prefixWord ++ tailWord_5748205).sum := by decide
  have hdescent : baseEnd_5748205 < baseStart_5748205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748207 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 2, 5]
def baseStart_5748207 : Nat := 118140960795 + 5748207 * 2 ^ 59
def prefixEnd_5748207 : Nat := 4983230072969 + 3 ^ 40 * 5748207 * 2
def baseEnd_5748207 : Nat := 983864364179698949125661

theorem tailTrace_5748207 : CollatzResearch.WordTrace tailWord_5748207 prefixEnd_5748207 983864364179698949125661 := by
  unfold tailWord_5748207
  simp only [CollatzResearch.WordTrace]
  refine ⟨209654333086235229442338875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139769555390823486294892583 209654333086235229442338875)
  ·
    refine ⟨314481499629352844163508313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209654333086235229442338875 314481499629352844163508313)
    ·
      refine ⟨235861124722014633122631235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314481499629352844163508313 235861124722014633122631235)
      ·
        refine ⟨353791687083021949683946853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235861124722014633122631235 353791687083021949683946853)
        ·
          refine ⟨66335941328066615565740035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353791687083021949683946853 66335941328066615565740035)
          ·
            refine ⟨99503911992099923348610053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66335941328066615565740035 99503911992099923348610053)
            ·
              refine ⟨18656983498518735627864385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99503911992099923348610053 18656983498518735627864385)
              ·
                refine ⟨13992737623889051720898289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18656983498518735627864385 13992737623889051720898289)
                ·
                  refine ⟨10494553217916788790673717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13992737623889051720898289 10494553217916788790673717)
                  ·
                    refine ⟨983864364179698949125661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10494553217916788790673717 983864364179698949125661)
                    ·
                      rfl

theorem cell23_5748207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_5748207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748207 prefixEnd_5748207 := by exact prefixLift 5748207
  have htrace : WordTrace (prefixWord ++ tailWord_5748207) baseStart_5748207 baseEnd_5748207 := by
    simpa [prefixWord, tailWord_5748207, baseEnd_5748207] using wordTrace_append hprefix tailTrace_5748207
  have hstable : (prefixWord ++ tailWord_5748207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748207).length < 2 ^ (prefixWord ++ tailWord_5748207).sum := by decide
  have hdescent : baseEnd_5748207 < baseStart_5748207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748257 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5748257 : Nat := 118140960795 + 5748257 * 2 ^ 59
def prefixEnd_5748257 : Nat := 4983230072969 + 3 ^ 40 * 5748257 * 2
def baseEnd_5748257 : Nat := 2951618766571821651751753

theorem tailTrace_5748257 : CollatzResearch.WordTrace tailWord_5748257 prefixEnd_5748257 2951618766571821651751753 := by
  unfold tailWord_5748257
  simp only [CollatzResearch.WordTrace]
  refine ⟨209656156736054087981659025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139770771157369391987772683 209656156736054087981659025)
  ·
    refine ⟨157242117552040565986244269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209656156736054087981659025 157242117552040565986244269)
    ·
      refine ⟨58965794082015212244841601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157242117552040565986244269 58965794082015212244841601)
      ·
        refine ⟨44224345561511409183631201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58965794082015212244841601 44224345561511409183631201)
        ·
          refine ⟨33168259171133556887723401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44224345561511409183631201 33168259171133556887723401)
          ·
            refine ⟨24876194378350167665792551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33168259171133556887723401 24876194378350167665792551)
            ·
              refine ⟨37314291567525251498688827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24876194378350167665792551 37314291567525251498688827)
              ·
                refine ⟨55971437351287877248033241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37314291567525251498688827 55971437351287877248033241)
                ·
                  refine ⟨41978578013465907936024931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55971437351287877248033241 41978578013465907936024931)
                  ·
                    refine ⟨62967867020198861904037397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41978578013465907936024931 62967867020198861904037397)
                    ·
                      refine ⟨2951618766571821651751753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62967867020198861904037397 2951618766571821651751753)
                      ·
                        rfl

theorem cell23_5748257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5748257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748257 prefixEnd_5748257 := by exact prefixLift 5748257
  have htrace : WordTrace (prefixWord ++ tailWord_5748257) baseStart_5748257 baseEnd_5748257 := by
    simpa [prefixWord, tailWord_5748257, baseEnd_5748257] using wordTrace_append hprefix tailTrace_5748257
  have hstable : (prefixWord ++ tailWord_5748257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748257).length < 2 ^ (prefixWord ++ tailWord_5748257).sum := by decide
  have hdescent : baseEnd_5748257 < baseStart_5748257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748297 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_5748297 : Nat := 118140960795 + 5748297 * 2 ^ 59
def prefixEnd_5748297 : Nat := 4983230072969 + 3 ^ 40 * 5748297 * 2
def baseEnd_5748297 : Nat := 983879768599333831750523

theorem tailTrace_5748297 : CollatzResearch.WordTrace tailWord_5748297 prefixEnd_5748297 983879768599333831750523 := by
  unfold tailWord_5748297
  simp only [CollatzResearch.WordTrace]
  refine ⟨209657615655909174813115145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139771743770606116542076763 209657615655909174813115145)
  ·
    refine ⟨157243211741931881109836359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209657615655909174813115145 157243211741931881109836359)
    ·
      refine ⟨235864817612897821664754539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157243211741931881109836359 235864817612897821664754539)
      ·
        refine ⟨353797226419346732497131809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235864817612897821664754539 353797226419346732497131809)
        ·
          refine ⟨265347919814510049372848857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353797226419346732497131809 265347919814510049372848857)
          ·
            refine ⟨199010939860882537029636643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265347919814510049372848857 199010939860882537029636643)
            ·
              refine ⟨298516409791323805544454965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199010939860882537029636643 298516409791323805544454965)
              ·
                refine ⟨27985913417936606769792653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298516409791323805544454965 27985913417936606769792653)
                ·
                  refine ⟨10494717531726227538672245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27985913417936606769792653 10494717531726227538672245)
                  ·
                    refine ⟨983879768599333831750523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10494717531726227538672245 983879768599333831750523)
                    ·
                      rfl

theorem cell23_5748297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_5748297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748297 prefixEnd_5748297 := by exact prefixLift 5748297
  have htrace : WordTrace (prefixWord ++ tailWord_5748297) baseStart_5748297 baseEnd_5748297 := by
    simpa [prefixWord, tailWord_5748297, baseEnd_5748297] using wordTrace_append hprefix tailTrace_5748297
  have hstable : (prefixWord ++ tailWord_5748297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748297).length < 2 ^ (prefixWord ++ tailWord_5748297).sum := by decide
  have hdescent : baseEnd_5748297 < baseStart_5748297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748304 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2]
def baseStart_5748304 : Nat := 118140960795 + 5748304 * 2 ^ 59
def prefixEnd_5748304 : Nat := 4983230072969 + 3 ^ 40 * 5748304 * 2
def baseEnd_5748304 : Nat := 2951642900162582967864037

theorem tailTrace_5748304 : CollatzResearch.WordTrace tailWord_5748304 prefixEnd_5748304 2951642900162582967864037 := by
  unfold tailWord_5748304
  simp only [CollatzResearch.WordTrace]
  refine ⟨104828935483441907504309983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139771913977922543339079977 104828935483441907504309983)
  ·
    refine ⟨157243403225162861256464975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104828935483441907504309983 157243403225162861256464975)
    ·
      refine ⟨235865104837744291884697463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157243403225162861256464975 235865104837744291884697463)
      ·
        refine ⟨353797657256616437827046195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235865104837744291884697463 353797657256616437827046195)
        ·
          refine ⟨530696485884924656740569293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353797657256616437827046195 530696485884924656740569293)
          ·
            refine ⟨199011182206846746277713485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530696485884924656740569293 199011182206846746277713485)
            ·
              refine ⟨74629193327567529854142557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199011182206846746277713485 74629193327567529854142557)
              ·
                refine ⟨27985947497837823695303459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74629193327567529854142557 27985947497837823695303459)
                ·
                  refine ⟨41978921246756735542955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27985947497837823695303459 41978921246756735542955189)
                  ·
                    refine ⟨3935523866883443957152049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41978921246756735542955189 3935523866883443957152049)
                    ·
                      refine ⟨2951642900162582967864037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935523866883443957152049 2951642900162582967864037)
                      ·
                        rfl

theorem cell23_5748304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2].length) (baseStart_5748304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748304 prefixEnd_5748304 := by exact prefixLift 5748304
  have htrace : WordTrace (prefixWord ++ tailWord_5748304) baseStart_5748304 baseEnd_5748304 := by
    simpa [prefixWord, tailWord_5748304, baseEnd_5748304] using wordTrace_append hprefix tailTrace_5748304
  have hstable : (prefixWord ++ tailWord_5748304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748304).length < 2 ^ (prefixWord ++ tailWord_5748304).sum := by decide
  have hdescent : baseEnd_5748304 < baseStart_5748304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748321 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_5748321 : Nat := 118140960795 + 5748321 * 2 ^ 59
def prefixEnd_5748321 : Nat := 4983230072969 + 3 ^ 40 * 5748321 * 2
def baseEnd_5748321 : Nat := 2951651629333709401351459

theorem tailTrace_5748321 : CollatzResearch.WordTrace tailWord_5748321 prefixEnd_5748321 2951651629333709401351459 := by
  unfold tailWord_5748321
  simp only [CollatzResearch.WordTrace]
  refine ⟨209658491007822226911988817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139772327338548151274659211 209658491007822226911988817)
  ·
    refine ⟨157243868255866670183991613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209658491007822226911988817 157243868255866670183991613)
    ·
      refine ⟨58966450595950001318996855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157243868255866670183991613 58966450595950001318996855)
      ·
        refine ⟨88449675893925001978495283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58966450595950001318996855 88449675893925001978495283)
        ·
          refine ⟨132674513840887502967742925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88449675893925001978495283 132674513840887502967742925)
          ·
            refine ⟨49752942690332813612903597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132674513840887502967742925 49752942690332813612903597)
            ·
              refine ⟨18657353508874805104838849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49752942690332813612903597 18657353508874805104838849)
              ·
                refine ⟨13993015131656103828629137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18657353508874805104838849 13993015131656103828629137)
                ·
                  refine ⟨10494761348742077871471853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13993015131656103828629137 10494761348742077871471853)
                  ·
                    refine ⟨3935535505778279201801945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10494761348742077871471853 3935535505778279201801945)
                    ·
                      refine ⟨2951651629333709401351459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935535505778279201801945 2951651629333709401351459)
                      ·
                        rfl

theorem cell23_5748321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_5748321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748321 prefixEnd_5748321 := by exact prefixLift 5748321
  have htrace : WordTrace (prefixWord ++ tailWord_5748321) baseStart_5748321 baseEnd_5748321 := by
    simpa [prefixWord, tailWord_5748321, baseEnd_5748321] using wordTrace_append hprefix tailTrace_5748321
  have hstable : (prefixWord ++ tailWord_5748321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748321).length < 2 ^ (prefixWord ++ tailWord_5748321).sum := by decide
  have hdescent : baseEnd_5748321 < baseStart_5748321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748328 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5748328 : Nat := 118140960795 + 5748328 * 2 ^ 59
def prefixEnd_5748328 : Nat := 4983230072969 + 3 ^ 40 * 5748328 * 2
def baseEnd_5748328 : Nat := 2951655223698290873963927

theorem tailTrace_5748328 : CollatzResearch.WordTrace tailWord_5748328 prefixEnd_5748328 2951655223698290873963927 := by
  unfold tailWord_5748328
  simp only [CollatzResearch.WordTrace]
  refine ⟨104829373159398433553746819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139772497545864578071662425 104829373159398433553746819)
  ·
    refine ⟨157244059739097650330620229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104829373159398433553746819 157244059739097650330620229)
    ·
      refine ⟨29483261201080809436991293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157244059739097650330620229 29483261201080809436991293)
      ·
        refine ⟨11056222950405303538871735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29483261201080809436991293 11056222950405303538871735)
        ·
          refine ⟨16584334425607955308307603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056222950405303538871735 16584334425607955308307603)
          ·
            refine ⟨24876501638411932962461405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16584334425607955308307603 24876501638411932962461405)
            ·
              refine ⟨9328688114404474860923027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24876501638411932962461405 9328688114404474860923027)
              ·
                refine ⟨13993032171606712291384541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328688114404474860923027 13993032171606712291384541)
                ·
                  refine ⟨5247387064352517109269203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13993032171606712291384541 5247387064352517109269203)
                  ·
                    refine ⟨7871080596528775663903805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247387064352517109269203 7871080596528775663903805)
                    ·
                      refine ⟨2951655223698290873963927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7871080596528775663903805 2951655223698290873963927)
                      ·
                        rfl

theorem cell23_5748328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5748328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748328 prefixEnd_5748328 := by exact prefixLift 5748328
  have htrace : WordTrace (prefixWord ++ tailWord_5748328) baseStart_5748328 baseEnd_5748328 := by
    simpa [prefixWord, tailWord_5748328, baseEnd_5748328] using wordTrace_append hprefix tailTrace_5748328
  have hstable : (prefixWord ++ tailWord_5748328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748328).length < 2 ^ (prefixWord ++ tailWord_5748328).sum := by decide
  have hdescent : baseEnd_5748328 < baseStart_5748328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748347 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_5748347 : Nat := 118140960795 + 5748347 * 2 ^ 59
def prefixEnd_5748347 : Nat := 4983230072969 + 3 ^ 40 * 5748347 * 2
def baseEnd_5748347 : Nat := 2951664979830726299626339

theorem tailTrace_5748347 : CollatzResearch.WordTrace tailWord_5748347 prefixEnd_5748347 2951664979830726299626339 := by
  unfold tailWord_5748347
  simp only [CollatzResearch.WordTrace]
  refine ⟨209659439305728033352435295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139772959537152022234956863 209659439305728033352435295)
  ·
    refine ⟨314489158958592050028652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209659439305728033352435295 314489158958592050028652943)
    ·
      refine ⟨471733738437888075042979415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314489158958592050028652943 471733738437888075042979415)
      ·
        refine ⟨707600607656832112564469123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471733738437888075042979415 707600607656832112564469123)
        ·
          refine ⟨1061400911485248168846703685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707600607656832112564469123 1061400911485248168846703685)
          ·
            refine ⟨199012670903484031658756941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1061400911485248168846703685 199012670903484031658756941)
            ·
              refine ⟨74629751588806511872033853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199012670903484031658756941 74629751588806511872033853)
              ·
                refine ⟨27986156845802441952012695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74629751588806511872033853 27986156845802441952012695)
                ·
                  refine ⟨41979235268703662928019043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27986156845802441952012695 41979235268703662928019043)
                  ·
                    refine ⟨62968852903055494392028565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41979235268703662928019043 62968852903055494392028565)
                    ·
                      refine ⟨2951664979830726299626339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62968852903055494392028565 2951664979830726299626339)
                      ·
                        rfl

theorem cell23_5748347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_5748347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748347 prefixEnd_5748347 := by exact prefixLift 5748347
  have htrace : WordTrace (prefixWord ++ tailWord_5748347) baseStart_5748347 baseEnd_5748347 := by
    simpa [prefixWord, tailWord_5748347, baseEnd_5748347] using wordTrace_append hprefix tailTrace_5748347
  have hstable : (prefixWord ++ tailWord_5748347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748347).length < 2 ^ (prefixWord ++ tailWord_5748347).sum := by decide
  have hdescent : baseEnd_5748347 < baseStart_5748347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748357 : List Nat := [1, 3, 1, 1, 4, 1, 1, 11]
def baseStart_5748357 : Nat := 118140960795 + 5748357 * 2 ^ 59
def prefixEnd_5748357 : Nat := 4983230072969 + 3 ^ 40 * 5748357 * 2
def baseEnd_5748357 : Nat := 109321115356935972611159

theorem tailTrace_5748357 : CollatzResearch.WordTrace tailWord_5748357 prefixEnd_5748357 109321115356935972611159 := by
  unfold tailWord_5748357
  simp only [CollatzResearch.WordTrace]
  refine ⟨209659804035691805060299325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139773202690461203373532883 209659804035691805060299325)
  ·
    refine ⟨78622426513384426897612247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209659804035691805060299325 78622426513384426897612247)
    ·
      refine ⟨117933639770076640346418371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78622426513384426897612247 117933639770076640346418371)
      ·
        refine ⟨176900459655114960519627557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117933639770076640346418371 176900459655114960519627557)
        ·
          refine ⟨33168836185334055097430167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176900459655114960519627557 33168836185334055097430167)
          ·
            refine ⟨49753254278001082646145251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33168836185334055097430167 49753254278001082646145251)
            ·
              refine ⟨74629881417001623969217877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49753254278001082646145251 74629881417001623969217877)
              ·
                refine ⟨109321115356935972611159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74629881417001623969217877 109321115356935972611159)
                ·
                  rfl

theorem cell23_5748357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 11].length) (baseStart_5748357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748357 prefixEnd_5748357 := by exact prefixLift 5748357
  have htrace : WordTrace (prefixWord ++ tailWord_5748357) baseStart_5748357 baseEnd_5748357 := by
    simpa [prefixWord, tailWord_5748357, baseEnd_5748357] using wordTrace_append hprefix tailTrace_5748357
  have hstable : (prefixWord ++ tailWord_5748357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748357).length < 2 ^ (prefixWord ++ tailWord_5748357).sum := by decide
  have hdescent : baseEnd_5748357 < baseStart_5748357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748364 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5748364 : Nat := 118140960795 + 5748364 * 2 ^ 59
def prefixEnd_5748364 : Nat := 4983230072969 + 3 ^ 40 * 5748364 * 2
def baseEnd_5748364 : Nat := 2951673709001852733113761

theorem tailTrace_5748364 : CollatzResearch.WordTrace tailWord_5748364 prefixEnd_5748364 2951673709001852733113761 := by
  unfold tailWord_5748364
  simp only [CollatzResearch.WordTrace]
  refine ⟨104830029673333222627902073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139773372897777630170536097 104830029673333222627902073)
  ·
    refine ⟨78622522254999916970926555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104830029673333222627902073 78622522254999916970926555)
    ·
      refine ⟨117933783382499875456389833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78622522254999916970926555 117933783382499875456389833)
      ·
        refine ⟨88450337536874906592292375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117933783382499875456389833 88450337536874906592292375)
        ·
          refine ⟨132675506305312359888438563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88450337536874906592292375 132675506305312359888438563)
          ·
            refine ⟨199013259457968539832657845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132675506305312359888438563 199013259457968539832657845)
            ·
              refine ⟨18657493074184550609311673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199013259457968539832657845 18657493074184550609311673)
              ·
                refine ⟨13993119805638412956983755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18657493074184550609311673 13993119805638412956983755)
                ·
                  refine ⟨20989679708457619435475633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13993119805638412956983755 20989679708457619435475633)
                  ·
                    refine ⟨15742259781343214576606725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20989679708457619435475633 15742259781343214576606725)
                    ·
                      refine ⟨2951673709001852733113761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15742259781343214576606725 2951673709001852733113761)
                      ·
                        rfl

theorem cell23_5748364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5748364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748364 prefixEnd_5748364 := by exact prefixLift 5748364
  have htrace : WordTrace (prefixWord ++ tailWord_5748364) baseStart_5748364 baseEnd_5748364 := by
    simpa [prefixWord, tailWord_5748364, baseEnd_5748364] using wordTrace_append hprefix tailTrace_5748364
  have hstable : (prefixWord ++ tailWord_5748364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748364).length < 2 ^ (prefixWord ++ tailWord_5748364).sum := by decide
  have hdescent : baseEnd_5748364 < baseStart_5748364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748374 : List Nat := [5, 3, 15]
def baseStart_5748374 : Nat := 118140960795 + 5748374 * 2 ^ 59
def prefixEnd_5748374 : Nat := 4983230072969 + 3 ^ 40 * 5748374 * 2
def baseEnd_5748374 : Nat := 449882463619630802315

theorem tailTrace_5748374 : CollatzResearch.WordTrace tailWord_5748374 prefixEnd_5748374 449882463619630802315 := by
  unfold tailWord_5748374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103776504789388560229261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139773616051086811309112117 13103776504789388560229261)
  ·
    refine ⟨4913916189296020710085973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13103776504789388560229261 4913916189296020710085973)
    ·
      refine ⟨449882463619630802315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4913916189296020710085973 449882463619630802315)
      ·
        rfl

theorem cell23_5748374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 15].length) (baseStart_5748374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748374 prefixEnd_5748374 := by exact prefixLift 5748374
  have htrace : WordTrace (prefixWord ++ tailWord_5748374) baseStart_5748374 baseEnd_5748374 := by
    simpa [prefixWord, tailWord_5748374, baseEnd_5748374] using wordTrace_append hprefix tailTrace_5748374
  have hstable : (prefixWord ++ tailWord_5748374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748374).length < 2 ^ (prefixWord ++ tailWord_5748374).sum := by decide
  have hdescent : baseEnd_5748374 < baseStart_5748374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748377 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_5748377 : Nat := 118140960795 + 5748377 * 2 ^ 59
def prefixEnd_5748377 : Nat := 4983230072969 + 3 ^ 40 * 5748377 * 2
def baseEnd_5748377 : Nat := 2951680384250361182251201

theorem tailTrace_5748377 : CollatzResearch.WordTrace tailWord_5748377 prefixEnd_5748377 2951680384250361182251201 := by
  unfold tailWord_5748377
  simp only [CollatzResearch.WordTrace]
  refine ⟨209660533495619348476027385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139773688997079565650684923 209660533495619348476027385)
  ·
    refine ⟨157245400121714511357020539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209660533495619348476027385 157245400121714511357020539)
    ·
      refine ⟨235868100182571767035530809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157245400121714511357020539 235868100182571767035530809)
      ·
        refine ⟨176901075136928825276648107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235868100182571767035530809 176901075136928825276648107)
        ·
          refine ⟨265351612705393237914972161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176901075136928825276648107 265351612705393237914972161)
          ·
            refine ⟨199013709529044928436229121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265351612705393237914972161 199013709529044928436229121)
            ·
              refine ⟨149260282146783696327171841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199013709529044928436229121 149260282146783696327171841)
              ·
                refine ⟨111945211610087772245378881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149260282146783696327171841 111945211610087772245378881)
                ·
                  refine ⟨83958908707565829184034161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111945211610087772245378881 83958908707565829184034161)
                  ·
                    refine ⟨62969181530674371888025621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83958908707565829184034161 62969181530674371888025621)
                    ·
                      refine ⟨2951680384250361182251201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62969181530674371888025621 2951680384250361182251201)
                      ·
                        rfl

theorem cell23_5748377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_5748377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748377 prefixEnd_5748377 := by exact prefixLift 5748377
  have htrace : WordTrace (prefixWord ++ tailWord_5748377) baseStart_5748377 baseEnd_5748377 := by
    simpa [prefixWord, tailWord_5748377, baseEnd_5748377] using wordTrace_append hprefix tailTrace_5748377
  have hstable : (prefixWord ++ tailWord_5748377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748377).length < 2 ^ (prefixWord ++ tailWord_5748377).sum := by decide
  have hdescent : baseEnd_5748377 < baseStart_5748377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748387 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 1, 9]
def baseStart_5748387 : Nat := 118140960795 + 5748387 * 2 ^ 59
def prefixEnd_5748387 : Nat := 4983230072969 + 3 ^ 40 * 5748387 * 2
def baseEnd_5748387 : Nat := 983895173018968714375385

theorem tailTrace_5748387 : CollatzResearch.WordTrace tailWord_5748387 prefixEnd_5748387 983895173018968714375385 := by
  unfold tailWord_5748387
  simp only [CollatzResearch.WordTrace]
  refine ⟨209660898225583120183891415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139773932150388746789260943 209660898225583120183891415)
  ·
    refine ⟨314491347338374680275837123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209660898225583120183891415 314491347338374680275837123)
    ·
      refine ⟨471737021007562020413755685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314491347338374680275837123 471737021007562020413755685)
      ·
        refine ⟨88450691438917878827579191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471737021007562020413755685 88450691438917878827579191)
        ·
          refine ⟨132676037158376818241368787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88450691438917878827579191 132676037158376818241368787)
          ·
            refine ⟨199014055737565227362053181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132676037158376818241368787 199014055737565227362053181)
            ·
              refine ⟨74630270901586960260769943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199014055737565227362053181 74630270901586960260769943)
              ·
                refine ⟨111945406352380440391154915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74630270901586960260769943 111945406352380440391154915)
                ·
                  refine ⟨167918109528570660586732373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111945406352380440391154915 167918109528570660586732373)
                  ·
                    refine ⟨983895173018968714375385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167918109528570660586732373 983895173018968714375385)
                    ·
                      rfl

theorem cell23_5748387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_5748387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748387 prefixEnd_5748387 := by exact prefixLift 5748387
  have htrace : WordTrace (prefixWord ++ tailWord_5748387) baseStart_5748387 baseEnd_5748387 := by
    simpa [prefixWord, tailWord_5748387, baseEnd_5748387] using wordTrace_append hprefix tailTrace_5748387
  have hstable : (prefixWord ++ tailWord_5748387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748387).length < 2 ^ (prefixWord ++ tailWord_5748387).sum := by decide
  have hdescent : baseEnd_5748387 < baseStart_5748387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748422 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5748422 : Nat := 118140960795 + 5748422 * 2 ^ 59
def prefixEnd_5748422 : Nat := 4983230072969 + 3 ^ 40 * 5748422 * 2
def baseEnd_5748422 : Nat := 2951703490879813506188495

theorem tailTrace_5748422 : CollatzResearch.WordTrace tailWord_5748422 prefixEnd_5748422 2951703490879813506188495 := by
  unfold tailWord_5748422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551942961889260036294235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139774783186970880774277013 6551942961889260036294235)
  ·
    refine ⟨9827914442833890054441353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551942961889260036294235 9827914442833890054441353)
    ·
      refine ⟨7370935832125417540831015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9827914442833890054441353 7370935832125417540831015)
      ·
        refine ⟨11056403748188126311246523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370935832125417540831015 11056403748188126311246523)
        ·
          refine ⟨16584605622282189466869785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056403748188126311246523 16584605622282189466869785)
          ·
            refine ⟨12438454216711642100152339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16584605622282189466869785 12438454216711642100152339)
            ·
              refine ⟨18657681325067463150228509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12438454216711642100152339 18657681325067463150228509)
              ·
                refine ⟨6996630496900298681335691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18657681325067463150228509 6996630496900298681335691)
                ·
                  refine ⟨10494945745350448022003537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6996630496900298681335691 10494945745350448022003537)
                  ·
                    refine ⟨7871209309012836016502653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10494945745350448022003537 7871209309012836016502653)
                    ·
                      refine ⟨2951703490879813506188495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7871209309012836016502653 2951703490879813506188495)
                      ·
                        rfl

theorem cell23_5748422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5748422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748422 prefixEnd_5748422 := by exact prefixLift 5748422
  have htrace : WordTrace (prefixWord ++ tailWord_5748422) baseStart_5748422 baseEnd_5748422 := by
    simpa [prefixWord, tailWord_5748422, baseEnd_5748422] using wordTrace_append hprefix tailTrace_5748422
  have hstable : (prefixWord ++ tailWord_5748422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748422).length < 2 ^ (prefixWord ++ tailWord_5748422).sum := by decide
  have hdescent : baseEnd_5748422 < baseStart_5748422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748458 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_5748458 : Nat := 118140960795 + 5748458 * 2 ^ 59
def prefixEnd_5748458 : Nat := 4983230072969 + 3 ^ 40 * 5748458 * 2
def baseEnd_5748458 : Nat := 2951721976183375365338329

theorem tailTrace_5748458 : CollatzResearch.WordTrace tailWord_5748458 prefixEnd_5748458 2951721976183375365338329 := by
  unfold tailWord_5748458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52415871952081474827431507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139775658538883932873150685 52415871952081474827431507)
  ·
    refine ⟨78623807928122212241147261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52415871952081474827431507 78623807928122212241147261)
    ·
      refine ⟨29483927973045829590430223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78623807928122212241147261 29483927973045829590430223)
      ·
        refine ⟨44225891959568744385645335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29483927973045829590430223 44225891959568744385645335)
        ·
          refine ⟨66338837939353116578468003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44225891959568744385645335 66338837939353116578468003)
          ·
            refine ⟨99508256909029674867702005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66338837939353116578468003 99508256909029674867702005)
            ·
              refine ⟨9328899085221532018847063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99508256909029674867702005 9328899085221532018847063)
              ·
                refine ⟨13993348627832298028270595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328899085221532018847063 13993348627832298028270595)
                ·
                  refine ⟨20990022941748447042405893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13993348627832298028270595 20990022941748447042405893)
                  ·
                    refine ⟨3935629301577833820451105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20990022941748447042405893 3935629301577833820451105)
                    ·
                      refine ⟨2951721976183375365338329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935629301577833820451105 2951721976183375365338329)
                      ·
                        rfl

theorem cell23_5748458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_5748458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748458 prefixEnd_5748458 := by exact prefixLift 5748458
  have htrace : WordTrace (prefixWord ++ tailWord_5748458) baseStart_5748458 baseEnd_5748458 := by
    simpa [prefixWord, tailWord_5748458, baseEnd_5748458] using wordTrace_append hprefix tailTrace_5748458
  have hstable : (prefixWord ++ tailWord_5748458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748458).length < 2 ^ (prefixWord ++ tailWord_5748458).sum := by decide
  have hdescent : baseEnd_5748458 < baseStart_5748458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748478 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5748478 : Nat := 118140960795 + 5748478 * 2 ^ 59
def prefixEnd_5748478 : Nat := 4983230072969 + 3 ^ 40 * 5748478 * 2
def baseEnd_5748478 : Nat := 2951732245796465287088237

theorem tailTrace_5748478 : CollatzResearch.WordTrace tailWord_5748478 prefixEnd_5748478 2951732245796465287088237 := by
  unfold tailWord_5748478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208027158531680340681761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139776144845502295150302725 26208027158531680340681761)
  ·
    refine ⟨19656020368898760255511321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26208027158531680340681761 19656020368898760255511321)
    ·
      refine ⟨14742015276674070191633491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19656020368898760255511321 14742015276674070191633491)
      ·
        refine ⟨22113022915011105287450237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14742015276674070191633491 22113022915011105287450237)
        ·
          refine ⟨8292383593129164482793839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22113022915011105287450237 8292383593129164482793839)
          ·
            refine ⟨12438575389693746724190759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292383593129164482793839 12438575389693746724190759)
            ·
              refine ⟨18657863084540620086286139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12438575389693746724190759 18657863084540620086286139)
              ·
                refine ⟨27986794626810930129429209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18657863084540620086286139 27986794626810930129429209)
                ·
                  refine ⟨20990095970108197597071907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27986794626810930129429209 20990095970108197597071907)
                  ·
                    refine ⟨31485143955162296395607861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20990095970108197597071907 31485143955162296395607861)
                    ·
                      refine ⟨2951732245796465287088237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31485143955162296395607861 2951732245796465287088237)
                      ·
                        rfl

theorem cell23_5748478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5748478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748478 prefixEnd_5748478 := by exact prefixLift 5748478
  have htrace : WordTrace (prefixWord ++ tailWord_5748478) baseStart_5748478 baseEnd_5748478 := by
    simpa [prefixWord, tailWord_5748478, baseEnd_5748478] using wordTrace_append hprefix tailTrace_5748478
  have hstable : (prefixWord ++ tailWord_5748478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748478).length < 2 ^ (prefixWord ++ tailWord_5748478).sum := by decide
  have hdescent : baseEnd_5748478 < baseStart_5748478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748498 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_5748498 : Nat := 118140960795 + 5748498 * 2 ^ 59
def prefixEnd_5748498 : Nat := 4983230072969 + 3 ^ 40 * 5748498 * 2
def baseEnd_5748498 : Nat := 327971390601061689870905

theorem tailTrace_5748498 : CollatzResearch.WordTrace tailWord_5748498 prefixEnd_5748498 327971390601061689870905 := by
  unfold tailWord_5748498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52416236682045246535295537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139776631152120657427454765 52416236682045246535295537)
  ·
    refine ⟨39312177511533934901471653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52416236682045246535295537 39312177511533934901471653)
    ·
      refine ⟨7371033283412612794025935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39312177511533934901471653 7371033283412612794025935)
      ·
        refine ⟨11056549925118919191038903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371033283412612794025935 11056549925118919191038903)
        ·
          refine ⟨16584824887678378786558355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056549925118919191038903 16584824887678378786558355)
          ·
            refine ⟨24877237331517568179837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16584824887678378786558355 24877237331517568179837533)
            ·
              refine ⟨9328963999319088067439075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24877237331517568179837533 9328963999319088067439075)
              ·
                refine ⟨13993445998978632101158613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9328963999319088067439075 13993445998978632101158613)
                ·
                  refine ⟨327971390601061689870905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13993445998978632101158613 327971390601061689870905)
                  ·
                    rfl

theorem cell23_5748498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_5748498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748498 prefixEnd_5748498 := by exact prefixLift 5748498
  have htrace : WordTrace (prefixWord ++ tailWord_5748498) baseStart_5748498 baseEnd_5748498 := by
    simpa [prefixWord, tailWord_5748498, baseEnd_5748498] using wordTrace_append hprefix tailTrace_5748498
  have hstable : (prefixWord ++ tailWord_5748498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748498).length < 2 ^ (prefixWord ++ tailWord_5748498).sum := by decide
  have hdescent : baseEnd_5748498 < baseStart_5748498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748504 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5748504 : Nat := 118140960795 + 5748504 * 2 ^ 59
def prefixEnd_5748504 : Nat := 4983230072969 + 3 ^ 40 * 5748504 * 2
def baseEnd_5748504 : Nat := 2951745596293482185363117

theorem tailTrace_5748504 : CollatzResearch.WordTrace tailWord_5748504 prefixEnd_5748504 2951745596293482185363117 := by
  unfold tailWord_5748504
  simp only [CollatzResearch.WordTrace]
  refine ⟨104832582783079624582950283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139776777044106166110600377 104832582783079624582950283)
  ·
    refine ⟨157248874174619436874425425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104832582783079624582950283 157248874174619436874425425)
    ·
      refine ⟨117936655630964577655819069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157248874174619436874425425 117936655630964577655819069)
      ·
        refine ⟨44226245861611716620932151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117936655630964577655819069 44226245861611716620932151)
        ·
          refine ⟨66339368792417574931398227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44226245861611716620932151 66339368792417574931398227)
          ·
            refine ⟨99509053188626362397097341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66339368792417574931398227 99509053188626362397097341)
            ·
              refine ⟨37315894945734885898911503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99509053188626362397097341 37315894945734885898911503)
              ·
                refine ⟨55973842418602328848367255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37315894945734885898911503 55973842418602328848367255)
                ·
                  refine ⟨83960763627903493272550883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55973842418602328848367255 83960763627903493272550883)
                  ·
                    refine ⟨125941145441855239908826325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83960763627903493272550883 125941145441855239908826325)
                    ·
                      refine ⟨2951745596293482185363117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125941145441855239908826325 2951745596293482185363117)
                      ·
                        rfl

theorem cell23_5748504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5748504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748504 prefixEnd_5748504 := by exact prefixLift 5748504
  have htrace : WordTrace (prefixWord ++ tailWord_5748504) baseStart_5748504 baseEnd_5748504 := by
    simpa [prefixWord, tailWord_5748504, baseEnd_5748504] using wordTrace_append hprefix tailTrace_5748504
  have hstable : (prefixWord ++ tailWord_5748504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748504).length < 2 ^ (prefixWord ++ tailWord_5748504).sum := by decide
  have hdescent : baseEnd_5748504 < baseStart_5748504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748608 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2]
def baseStart_5748608 : Nat := 118140960795 + 5748608 * 2 ^ 59
def prefixEnd_5748608 : Nat := 4983230072969 + 3 ^ 40 * 5748608 * 2
def baseEnd_5748608 : Nat := 2951798998281549778462639

theorem tailTrace_5748608 : CollatzResearch.WordTrace tailWord_5748608 prefixEnd_5748608 2951798998281549778462639 := by
  unfold tailWord_5748608
  simp only [CollatzResearch.WordTrace]
  refine ⟨104834479378891237463843239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139779305838521649951790985 104834479378891237463843239)
  ·
    refine ⟨157251719068336856195764859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104834479378891237463843239 157251719068336856195764859)
    ·
      refine ⟨235877578602505284293647289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157251719068336856195764859 235877578602505284293647289)
      ·
        refine ⟨176908183951878963220235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235877578602505284293647289 176908183951878963220235467)
        ·
          refine ⟨265362275927818444830353201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176908183951878963220235467 265362275927818444830353201)
          ·
            refine ⟨199021706945863833622764901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265362275927818444830353201 199021706945863833622764901)
            ·
              refine ⟨37316570052349468804268419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199021706945863833622764901 37316570052349468804268419)
              ·
                refine ⟨55974855078524203206402629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37316570052349468804268419 55974855078524203206402629)
                ·
                  refine ⟨10495285327223288101200493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55974855078524203206402629 10495285327223288101200493)
                  ·
                    refine ⟨3935731997708733037950185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10495285327223288101200493 3935731997708733037950185)
                    ·
                      refine ⟨2951798998281549778462639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935731997708733037950185 2951798998281549778462639)
                      ·
                        rfl

theorem cell23_5748608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_5748608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748608 prefixEnd_5748608 := by exact prefixLift 5748608
  have htrace : WordTrace (prefixWord ++ tailWord_5748608) baseStart_5748608 baseEnd_5748608 := by
    simpa [prefixWord, tailWord_5748608, baseEnd_5748608] using wordTrace_append hprefix tailTrace_5748608
  have hstable : (prefixWord ++ tailWord_5748608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748608).length < 2 ^ (prefixWord ++ tailWord_5748608).sum := by decide
  have hdescent : baseEnd_5748608 < baseStart_5748608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748622 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_5748622 : Nat := 118140960795 + 5748622 * 2 ^ 59
def prefixEnd_5748622 : Nat := 4983230072969 + 3 ^ 40 * 5748622 * 2
def baseEnd_5748622 : Nat := 327978465223412524854175

theorem tailTrace_5748622 : CollatzResearch.WordTrace tailWord_5748622 prefixEnd_5748622 327978465223412524854175 := by
  unfold tailWord_5748622
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208683672466469414837015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139779646253154503545797413 26208683672466469414837015)
  ·
    refine ⟨39313025508699704122255523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208683672466469414837015 39313025508699704122255523)
    ·
      refine ⟨58969538263049556183383285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39313025508699704122255523 58969538263049556183383285)
      ·
        refine ⟨5528394212160895892192183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58969538263049556183383285 5528394212160895892192183)
        ·
          refine ⟨8292591318241343838288275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528394212160895892192183 8292591318241343838288275)
          ·
            refine ⟨12438886977362015757432413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292591318241343838288275 12438886977362015757432413)
            ·
              refine ⟨4664582616510755909037155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12438886977362015757432413 4664582616510755909037155)
              ·
                refine ⟨6996873924766133863555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4664582616510755909037155 6996873924766133863555733)
                ·
                  refine ⟨327978465223412524854175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6996873924766133863555733 327978465223412524854175)
                  ·
                    rfl

theorem cell23_5748622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_5748622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748622 prefixEnd_5748622 := by exact prefixLift 5748622
  have htrace : WordTrace (prefixWord ++ tailWord_5748622) baseStart_5748622 baseEnd_5748622 := by
    simpa [prefixWord, tailWord_5748622, baseEnd_5748622] using wordTrace_append hprefix tailTrace_5748622
  have hstable : (prefixWord ++ tailWord_5748622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748622).length < 2 ^ (prefixWord ++ tailWord_5748622).sum := by decide
  have hdescent : baseEnd_5748622 < baseStart_5748622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748661 : List Nat := [1, 3, 3, 2, 1, 2, 11]
def baseStart_5748661 : Nat := 118140960795 + 5748661 * 2 ^ 59
def prefixEnd_5748661 : Nat := 4983230072969 + 3 ^ 40 * 5748661 * 2
def baseEnd_5748661 : Nat := 36442298922916519396295

theorem tailTrace_5748661 : CollatzResearch.WordTrace tailWord_5748661 prefixEnd_5748661 36442298922916519396295 := by
  unfold tailWord_5748661
  simp only [CollatzResearch.WordTrace]
  refine ⟨209670891826590464979365837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139780594551060309986243891 209670891826590464979365837)
  ·
    refine ⟨78626584434971424367262189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209670891826590464979365837 78626584434971424367262189)
    ·
      refine ⟨29484969163114284137723321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78626584434971424367262189 29484969163114284137723321)
      ·
        refine ⟨22113726872335713103292491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29484969163114284137723321 22113726872335713103292491)
        ·
          refine ⟨33170590308503569654938737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22113726872335713103292491 33170590308503569654938737)
          ·
            refine ⟨24877942731377677241204053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33170590308503569654938737 24877942731377677241204053)
            ·
              refine ⟨36442298922916519396295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24877942731377677241204053 36442298922916519396295)
              ·
                rfl

theorem cell23_5748661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 11].length) (baseStart_5748661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748661 prefixEnd_5748661 := by exact prefixLift 5748661
  have htrace : WordTrace (prefixWord ++ tailWord_5748661) baseStart_5748661 baseEnd_5748661 := by
    simpa [prefixWord, tailWord_5748661, baseEnd_5748661] using wordTrace_append hprefix tailTrace_5748661
  have hstable : (prefixWord ++ tailWord_5748661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748661).length < 2 ^ (prefixWord ++ tailWord_5748661).sum := by decide
  have hdescent : baseEnd_5748661 < baseStart_5748661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748715 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 1, 3, 2]
def baseStart_5748715 : Nat := 118140960795 + 5748715 * 2 ^ 59
def prefixEnd_5748715 : Nat := 4983230072969 + 3 ^ 40 * 5748715 * 2
def baseEnd_5748715 : Nat := 2951853940711580859824647

theorem tailTrace_5748715 : CollatzResearch.WordTrace tailWord_5748715 prefixEnd_5748715 2951853940711580859824647 := by
  unfold tailWord_5748715
  simp only [CollatzResearch.WordTrace]
  refine ⟨209672861368394832201831599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139781907578929888134554399 209672861368394832201831599)
  ·
    refine ⟨314509292052592248302747399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209672861368394832201831599 314509292052592248302747399)
    ·
      refine ⟨471763938078888372454121099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314509292052592248302747399 471763938078888372454121099)
      ·
        refine ⟨707645907118332558681181649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471763938078888372454121099 707645907118332558681181649)
        ·
          refine ⟨530734430338749419010886237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707645907118332558681181649 530734430338749419010886237)
          ·
            refine ⟨199025411377031032129082339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530734430338749419010886237 199025411377031032129082339)
            ·
              refine ⟨298538117065546548193623509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199025411377031032129082339 298538117065546548193623509)
              ·
                refine ⟨6996987118723747223288051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 298538117065546548193623509 6996987118723747223288051)
                ·
                  refine ⟨10495480678085620834932077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6996987118723747223288051 10495480678085620834932077)
                  ·
                    refine ⟨3935805254282107813099529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10495480678085620834932077 3935805254282107813099529)
                    ·
                      refine ⟨2951853940711580859824647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935805254282107813099529 2951853940711580859824647)
                      ·
                        rfl

theorem cell23_5748715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3, 2].length) (baseStart_5748715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748715 prefixEnd_5748715 := by exact prefixLift 5748715
  have htrace : WordTrace (prefixWord ++ tailWord_5748715) baseStart_5748715 baseEnd_5748715 := by
    simpa [prefixWord, tailWord_5748715, baseEnd_5748715] using wordTrace_append hprefix tailTrace_5748715
  have hstable : (prefixWord ++ tailWord_5748715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748715).length < 2 ^ (prefixWord ++ tailWord_5748715).sum := by decide
  have hdescent : baseEnd_5748715 < baseStart_5748715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748731 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_5748731 : Nat := 118140960795 + 5748731 * 2 ^ 59
def prefixEnd_5748731 : Nat := 4983230072969 + 3 ^ 40 * 5748731 * 2
def baseEnd_5748731 : Nat := 2951862156402052797224573

theorem tailTrace_5748731 : CollatzResearch.WordTrace tailWord_5748731 prefixEnd_5748731 2951862156402052797224573 := by
  unfold tailWord_5748731
  simp only [CollatzResearch.WordTrace]
  refine ⟨209673444936336866934414047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139782296624224577956276031 209673444936336866934414047)
  ·
    refine ⟨314510167404505300401621071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209673444936336866934414047 314510167404505300401621071)
    ·
      refine ⟨471765251106757950602431607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314510167404505300401621071 471765251106757950602431607)
      ·
        refine ⟨707647876660136925903647411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471765251106757950602431607 707647876660136925903647411)
        ·
          refine ⟨1061471814990205388855471117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707647876660136925903647411 1061471814990205388855471117)
          ·
            refine ⟨398051930621327020820801669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1061471814990205388855471117 398051930621327020820801669)
            ·
              refine ⟨74634736991498816403900313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398051930621327020820801669 74634736991498816403900313)
              ·
                refine ⟨55976052743624112302925235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74634736991498816403900313 55976052743624112302925235)
                ·
                  refine ⟨83964079115436168454387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55976052743624112302925235 83964079115436168454387853)
                  ·
                    refine ⟨31486529668288563170395445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83964079115436168454387853 31486529668288563170395445)
                    ·
                      refine ⟨2951862156402052797224573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31486529668288563170395445 2951862156402052797224573)
                      ·
                        rfl

theorem cell23_5748731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_5748731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748731 prefixEnd_5748731 := by exact prefixLift 5748731
  have htrace : WordTrace (prefixWord ++ tailWord_5748731) baseStart_5748731 baseEnd_5748731 := by
    simpa [prefixWord, tailWord_5748731, baseEnd_5748731] using wordTrace_append hprefix tailTrace_5748731
  have hstable : (prefixWord ++ tailWord_5748731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748731).length < 2 ^ (prefixWord ++ tailWord_5748731).sum := by decide
  have hdescent : baseEnd_5748731 < baseStart_5748731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748745 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 8, 2, 2]
def baseStart_5748745 : Nat := 118140960795 + 5748745 * 2 ^ 59
def prefixEnd_5748745 : Nat := 4983230072969 + 3 ^ 40 * 5748745 * 2
def baseEnd_5748745 : Nat := 2951869345131215742449509

theorem tailTrace_5748745 : CollatzResearch.WordTrace tailWord_5748745 prefixEnd_5748745 2951869345131215742449509 := by
  unfold tailWord_5748745
  simp only [CollatzResearch.WordTrace]
  refine ⟨209673955558286147325423689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139782637038857431550282459 209673955558286147325423689)
  ·
    refine ⟨157255466668714610494067767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209673955558286147325423689 157255466668714610494067767)
    ·
      refine ⟨235883200003071915741101651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157255466668714610494067767 235883200003071915741101651)
      ·
        refine ⟨353824800004607873611652477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235883200003071915741101651 353824800004607873611652477)
        ·
          refine ⟨132684300001727952604369679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353824800004607873611652477 132684300001727952604369679)
          ·
            refine ⟨199026450002591928906554519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132684300001727952604369679 199026450002591928906554519)
            ·
              refine ⟨298539675003887893359831779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199026450002591928906554519 298539675003887893359831779)
              ·
                refine ⟨447809512505831840039747669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298539675003887893359831779 447809512505831840039747669)
                ·
                  refine ⟨5247767724677716875465793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 447809512505831840039747669 5247767724677716875465793)
                  ·
                    refine ⟨3935825793508287656599345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5247767724677716875465793 3935825793508287656599345)
                    ·
                      refine ⟨2951869345131215742449509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935825793508287656599345 2951869345131215742449509)
                      ·
                        rfl

theorem cell23_5748745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2, 2].length) (baseStart_5748745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748745 prefixEnd_5748745 := by exact prefixLift 5748745
  have htrace : WordTrace (prefixWord ++ tailWord_5748745) baseStart_5748745 baseEnd_5748745 := by
    simpa [prefixWord, tailWord_5748745, baseEnd_5748745] using wordTrace_append hprefix tailTrace_5748745
  have hstable : (prefixWord ++ tailWord_5748745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748745).length < 2 ^ (prefixWord ++ tailWord_5748745).sum := by decide
  have hdescent : baseEnd_5748745 < baseStart_5748745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748748 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_5748748 : Nat := 118140960795 + 5748748 * 2 ^ 59
def prefixEnd_5748748 : Nat := 4983230072969 + 3 ^ 40 * 5748748 * 2
def baseEnd_5748748 : Nat := 2951870885573179230711995

theorem tailTrace_5748748 : CollatzResearch.WordTrace tailWord_5748748 prefixEnd_5748748 2951870885573179230711995 := by
  unfold tailWord_5748748
  simp only [CollatzResearch.WordTrace]
  refine ⟨104837032488637639418891449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139782709984850185891855265 104837032488637639418891449)
  ·
    refine ⟨78627774366478229564168587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104837032488637639418891449 78627774366478229564168587)
    ·
      refine ⟨117941661549717344346252881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78627774366478229564168587 117941661549717344346252881)
      ·
        refine ⟨88456246162288008259689661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117941661549717344346252881 88456246162288008259689661)
        ·
          refine ⟨33171092310858003097383623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88456246162288008259689661 33171092310858003097383623)
          ·
            refine ⟨49756638466287004646075435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33171092310858003097383623 49756638466287004646075435)
            ·
              refine ⟨74634957699430506969113153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49756638466287004646075435 74634957699430506969113153)
              ·
                refine ⟨55976218274572880226834865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74634957699430506969113153 55976218274572880226834865)
                ·
                  refine ⟨41982163705929660170126149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55976218274572880226834865 41982163705929660170126149)
                  ·
                    refine ⟨7871655694861811281898653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41982163705929660170126149 7871655694861811281898653)
                    ·
                      refine ⟨2951870885573179230711995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7871655694861811281898653 2951870885573179230711995)
                      ·
                        rfl

theorem cell23_5748748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_5748748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748748 prefixEnd_5748748 := by exact prefixLift 5748748
  have htrace : WordTrace (prefixWord ++ tailWord_5748748) baseStart_5748748 baseEnd_5748748 := by
    simpa [prefixWord, tailWord_5748748, baseEnd_5748748] using wordTrace_append hprefix tailTrace_5748748
  have hstable : (prefixWord ++ tailWord_5748748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748748).length < 2 ^ (prefixWord ++ tailWord_5748748).sum := by decide
  have hdescent : baseEnd_5748748 < baseStart_5748748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748761 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_5748761 : Nat := 118140960795 + 5748761 * 2 ^ 59
def prefixEnd_5748761 : Nat := 4983230072969 + 3 ^ 40 * 5748761 * 2
def baseEnd_5748761 : Nat := 2951877560821687679849435

theorem tailTrace_5748761 : CollatzResearch.WordTrace tailWord_5748761 prefixEnd_5748761 2951877560821687679849435 := by
  unfold tailWord_5748761
  simp only [CollatzResearch.WordTrace]
  refine ⟨209674539126228182058006137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139783026084152121372004091 209674539126228182058006137)
  ·
    refine ⟨157255904344671136543504603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209674539126228182058006137 157255904344671136543504603)
    ·
      refine ⟨235883856517006704815256905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157255904344671136543504603 235883856517006704815256905)
      ·
        refine ⟨176912892387755028611442679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235883856517006704815256905 176912892387755028611442679)
        ·
          refine ⟨265369338581632542917164019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176912892387755028611442679 265369338581632542917164019)
          ·
            refine ⟨398054007872448814375746029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265369338581632542917164019 398054007872448814375746029)
            ·
              refine ⟨149270252952168305390904761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398054007872448814375746029 149270252952168305390904761)
              ·
                refine ⟨111952689714126229043178571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149270252952168305390904761 111952689714126229043178571)
                ·
                  refine ⟨167929034571189343564767857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111952689714126229043178571 167929034571189343564767857)
                  ·
                    refine ⟨125946775928392007673575893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167929034571189343564767857 125946775928392007673575893)
                    ·
                      refine ⟨2951877560821687679849435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125946775928392007673575893 2951877560821687679849435)
                      ·
                        rfl

theorem cell23_5748761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_5748761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748761 prefixEnd_5748761 := by exact prefixLift 5748761
  have htrace : WordTrace (prefixWord ++ tailWord_5748761) baseStart_5748761 baseEnd_5748761 := by
    simpa [prefixWord, tailWord_5748761, baseEnd_5748761] using wordTrace_append hprefix tailTrace_5748761
  have hstable : (prefixWord ++ tailWord_5748761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748761).length < 2 ^ (prefixWord ++ tailWord_5748761).sum := by decide
  have hdescent : baseEnd_5748761 < baseStart_5748761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748785 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 5]
def baseStart_5748785 : Nat := 118140960795 + 5748785 * 2 ^ 59
def prefixEnd_5748785 : Nat := 4983230072969 + 3 ^ 40 * 5748785 * 2
def baseEnd_5748785 : Nat := 327987764928599509549925

theorem tailTrace_5748785 : CollatzResearch.WordTrace tailWord_5748785 prefixEnd_5748785 327987764928599509549925 := by
  unfold tailWord_5748785
  simp only [CollatzResearch.WordTrace]
  refine ⟨209675414478141234156879809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139783609652094156104586539 209675414478141234156879809)
  ·
    refine ⟨157256560858605925617659857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209675414478141234156879809 157256560858605925617659857)
    ·
      refine ⟨117942420643954444213244893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157256560858605925617659857 117942420643954444213244893)
      ·
        refine ⟨44228407741482916579966835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117942420643954444213244893 44228407741482916579966835)
        ·
          refine ⟨66342611612224374869950253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44228407741482916579966835 66342611612224374869950253)
          ·
            refine ⟨24878479354584140576231345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66342611612224374869950253 24878479354584140576231345)
            ·
              refine ⟨18658859515938105432173509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24878479354584140576231345 18658859515938105432173509)
              ·
                refine ⟨3498536159238394768532533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18658859515938105432173509 3498536159238394768532533)
                ·
                  refine ⟨327987764928599509549925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3498536159238394768532533 327987764928599509549925)
                  ·
                    rfl

theorem cell23_5748785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 5].length) (baseStart_5748785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748785 prefixEnd_5748785 := by exact prefixLift 5748785
  have htrace : WordTrace (prefixWord ++ tailWord_5748785) baseStart_5748785 baseEnd_5748785 := by
    simpa [prefixWord, tailWord_5748785, baseEnd_5748785] using wordTrace_append hprefix tailTrace_5748785
  have hstable : (prefixWord ++ tailWord_5748785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748785).length < 2 ^ (prefixWord ++ tailWord_5748785).sum := by decide
  have hdescent : baseEnd_5748785 < baseStart_5748785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748835 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5748835 : Nat := 118140960795 + 5748835 * 2 ^ 59
def prefixEnd_5748835 : Nat := 4983230072969 + 3 ^ 40 * 5748835 * 2
def baseEnd_5748835 : Nat := 2951915558390120390324095

theorem tailTrace_5748835 : CollatzResearch.WordTrace tailWord_5748835 prefixEnd_5748835 2951915558390120390324095 := by
  unfold tailWord_5748835
  simp only [CollatzResearch.WordTrace]
  refine ⟨209677238127960092696199959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139784825418640061797466639 209677238127960092696199959)
  ·
    refine ⟨314515857191940139044299939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209677238127960092696199959 314515857191940139044299939)
    ·
      refine ⟨471773785787910208566449909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314515857191940139044299939 471773785787910208566449909)
      ·
        refine ⟨44228792417616582053104679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 471773785787910208566449909 44228792417616582053104679)
        ·
          refine ⟨66343188626424873079657019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44228792417616582053104679 66343188626424873079657019)
          ·
            refine ⟨99514782939637309619485529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66343188626424873079657019 99514782939637309619485529)
            ·
              refine ⟨74636087204727982214614147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99514782939637309619485529 74636087204727982214614147)
              ·
                refine ⟨111954130807091973321921221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74636087204727982214614147 111954130807091973321921221)
                ·
                  refine ⟨20991399526329744997860229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111954130807091973321921221 20991399526329744997860229)
                  ·
                    refine ⟨3935887411186827187098793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20991399526329744997860229 3935887411186827187098793)
                    ·
                      refine ⟨2951915558390120390324095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3935887411186827187098793 2951915558390120390324095)
                      ·
                        rfl

theorem cell23_5748835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5748835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748835 prefixEnd_5748835 := by exact prefixLift 5748835
  have htrace : WordTrace (prefixWord ++ tailWord_5748835) baseStart_5748835 baseEnd_5748835 := by
    simpa [prefixWord, tailWord_5748835, baseEnd_5748835] using wordTrace_append hprefix tailTrace_5748835
  have hstable : (prefixWord ++ tailWord_5748835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748835).length < 2 ^ (prefixWord ++ tailWord_5748835).sum := by decide
  have hdescent : baseEnd_5748835 < baseStart_5748835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748872 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5748872 : Nat := 118140960795 + 5748872 * 2 ^ 59
def prefixEnd_5748872 : Nat := 4983230072969 + 3 ^ 40 * 5748872 * 2
def baseEnd_5748872 : Nat := 2951934557174336745561425

theorem tailTrace_5748872 : CollatzResearch.WordTrace tailWord_5748872 prefixEnd_5748872 2951934557174336745561425 := by
  unfold tailWord_5748872
  simp only [CollatzResearch.WordTrace]
  refine ⟨104839293814413024007648435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139785725085884032010197913 104839293814413024007648435)
  ·
    refine ⟨157258940721619536011472653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104839293814413024007648435 157258940721619536011472653)
    ·
      refine ⟨58972102770607326004302245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157258940721619536011472653 58972102770607326004302245)
      ·
        refine ⟨11057269269488873625806671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58972102770607326004302245 11057269269488873625806671)
        ·
          refine ⟨16585903904233310438710007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057269269488873625806671 16585903904233310438710007)
          ·
            refine ⟨24878855856349965658065011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16585903904233310438710007 24878855856349965658065011)
            ·
              refine ⟨37318283784524948487097517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24878855856349965658065011 37318283784524948487097517)
              ·
                refine ⟨13994356419196855682661569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37318283784524948487097517 13994356419196855682661569)
                ·
                  refine ⟨10495767314397641761996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13994356419196855682661569 10495767314397641761996177)
                  ·
                    refine ⟨7871825485798231321497133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10495767314397641761996177 7871825485798231321497133)
                    ·
                      refine ⟨2951934557174336745561425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7871825485798231321497133 2951934557174336745561425)
                      ·
                        rfl

theorem cell23_5748872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5748872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748872 prefixEnd_5748872 := by exact prefixLift 5748872
  have htrace : WordTrace (prefixWord ++ tailWord_5748872) baseStart_5748872 baseEnd_5748872 := by
    simpa [prefixWord, tailWord_5748872, baseEnd_5748872] using wordTrace_append hprefix tailTrace_5748872
  have hstable : (prefixWord ++ tailWord_5748872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748872).length < 2 ^ (prefixWord ++ tailWord_5748872).sum := by decide
  have hdescent : baseEnd_5748872 < baseStart_5748872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748896 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 1, 4]
def baseStart_5748896 : Nat := 118140960795 + 5748896 * 2 ^ 59
def prefixEnd_5748896 : Nat := 4983230072969 + 3 ^ 40 * 5748896 * 2
def baseEnd_5748896 : Nat := 983982293570014883887105

theorem tailTrace_5748896 : CollatzResearch.WordTrace tailWord_5748896 prefixEnd_5748896 983982293570014883887105 := by
  unfold tailWord_5748896
  simp only [CollatzResearch.WordTrace]
  refine ⟨104839731490369550057085271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139786308653826066742780361 104839731490369550057085271)
  ·
    refine ⟨157259597235554325085627907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104839731490369550057085271 157259597235554325085627907)
    ·
      refine ⟨235889395853331487628441861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157259597235554325085627907 235889395853331487628441861)
      ·
        refine ⟨44229261722499653930332849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235889395853331487628441861 44229261722499653930332849)
        ·
          refine ⟨33171946291874740447749637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44229261722499653930332849 33171946291874740447749637)
          ·
            refine ⟨6219739929726513833953057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33171946291874740447749637 6219739929726513833953057)
            ·
              refine ⟨4664804947294885375464793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219739929726513833953057 4664804947294885375464793)
              ·
                refine ⟨3498603710471164031598595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664804947294885375464793 3498603710471164031598595)
                ·
                  refine ⟨5247905565706746047397893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498603710471164031598595 5247905565706746047397893)
                  ·
                    refine ⟨983982293570014883887105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247905565706746047397893 983982293570014883887105)
                    ·
                      rfl

theorem cell23_5748896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_5748896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748896 prefixEnd_5748896 := by exact prefixLift 5748896
  have htrace : WordTrace (prefixWord ++ tailWord_5748896) baseStart_5748896 baseEnd_5748896 := by
    simpa [prefixWord, tailWord_5748896, baseEnd_5748896] using wordTrace_append hprefix tailTrace_5748896
  have hstable : (prefixWord ++ tailWord_5748896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748896).length < 2 ^ (prefixWord ++ tailWord_5748896).sum := by decide
  have hdescent : baseEnd_5748896 < baseStart_5748896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748952 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_5748952 : Nat := 118140960795 + 5748952 * 2 ^ 59
def prefixEnd_5748952 : Nat := 4983230072969 + 3 ^ 40 * 5748952 * 2
def baseEnd_5748952 : Nat := 983991878542232144187019

theorem tailTrace_5748952 : CollatzResearch.WordTrace tailWord_5748952 prefixEnd_5748952 983991878542232144187019 := by
  unfold tailWord_5748952
  simp only [CollatzResearch.WordTrace]
  refine ⟨104840752734268110839104555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139787670312357481118806073 104840752734268110839104555)
  ·
    refine ⟨157261129101402166258656833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104840752734268110839104555 157261129101402166258656833)
    ·
      refine ⟨117945846826051624693992625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157261129101402166258656833 117945846826051624693992625)
      ·
        refine ⟨88459385119538718520494469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117945846826051624693992625 88459385119538718520494469)
        ·
          refine ⟨16586134709913509722592713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88459385119538718520494469 16586134709913509722592713)
          ·
            refine ⟨12439601032435132291944535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16586134709913509722592713 12439601032435132291944535)
            ·
              refine ⟨18659401548652698437916803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439601032435132291944535 18659401548652698437916803)
              ·
                refine ⟨27989102322979047656875205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18659401548652698437916803 27989102322979047656875205)
                ·
                  refine ⟨5247956685558571435664101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27989102322979047656875205 5247956685558571435664101)
                  ·
                    refine ⟨983991878542232144187019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247956685558571435664101 983991878542232144187019)
                    ·
                      rfl

theorem cell23_5748952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_5748952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748952 prefixEnd_5748952 := by exact prefixLift 5748952
  have htrace : WordTrace (prefixWord ++ tailWord_5748952) baseStart_5748952 baseEnd_5748952 := by
    simpa [prefixWord, tailWord_5748952, baseEnd_5748952] using wordTrace_append hprefix tailTrace_5748952
  have hstable : (prefixWord ++ tailWord_5748952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748952).length < 2 ^ (prefixWord ++ tailWord_5748952).sum := by decide
  have hdescent : baseEnd_5748952 < baseStart_5748952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748982 : List Nat := [5, 1, 1, 1, 1, 1, 6, 7]
def baseStart_5748982 : Nat := 118140960795 + 5748982 * 2 ^ 59
def prefixEnd_5748982 : Nat := 4983230072969 + 3 ^ 40 * 5748982 * 2
def baseEnd_5748982 : Nat := 109333001483197456117997

theorem tailTrace_5748982 : CollatzResearch.WordTrace tailWord_5748982 prefixEnd_5748982 109333001483197456117997 := by
  unfold tailWord_5748982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105162478651721050112575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139788399772285024534534133 13105162478651721050112575)
  ·
    refine ⟨19657743717977581575168863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13105162478651721050112575 19657743717977581575168863)
    ·
      refine ⟨29486615576966372362753295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19657743717977581575168863 29486615576966372362753295)
      ·
        refine ⟨44229923365449558544129943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29486615576966372362753295 44229923365449558544129943)
        ·
          refine ⟨66344885048174337816194915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44229923365449558544129943 66344885048174337816194915)
          ·
            refine ⟨99517327572261506724292373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66344885048174337816194915 99517327572261506724292373)
            ·
              refine ⟨4664874729949758127701205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99517327572261506724292373 4664874729949758127701205)
              ·
                refine ⟨109333001483197456117997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4664874729949758127701205 109333001483197456117997)
                ·
                  rfl

theorem cell23_5748982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_5748982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748982 prefixEnd_5748982 := by exact prefixLift 5748982
  have htrace : WordTrace (prefixWord ++ tailWord_5748982) baseStart_5748982 baseEnd_5748982 := by
    simpa [prefixWord, tailWord_5748982, baseEnd_5748982] using wordTrace_append hprefix tailTrace_5748982
  have hstable : (prefixWord ++ tailWord_5748982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748982).length < 2 ^ (prefixWord ++ tailWord_5748982).sum := by decide
  have hdescent : baseEnd_5748982 < baseStart_5748982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748992 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_5748992 : Nat := 118140960795 + 5748992 * 2 ^ 59
def prefixEnd_5748992 : Nat := 4983230072969 + 3 ^ 40 * 5748992 * 2
def baseEnd_5748992 : Nat := 2951996174852876276060873

theorem tailTrace_5748992 : CollatzResearch.WordTrace tailWord_5748992 prefixEnd_5748992 2951996174852876276060873 := by
  unfold tailWord_5748992
  simp only [CollatzResearch.WordTrace]
  refine ⟨104841482194195654254832615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139788642925594205673110153 104841482194195654254832615)
  ·
    refine ⟨157262223291293481382248923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104841482194195654254832615 157262223291293481382248923)
    ·
      refine ⟨235893334936940222073373385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157262223291293481382248923 235893334936940222073373385)
      ·
        refine ⟨176920001202705166555030039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235893334936940222073373385 176920001202705166555030039)
        ·
          refine ⟨265380001804057749832545059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176920001202705166555030039 265380001804057749832545059)
          ·
            refine ⟨398070002706086624748817589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265380001804057749832545059 398070002706086624748817589)
            ·
              refine ⟨37319062753695621070201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398070002706086624748817589 37319062753695621070201649)
              ·
                refine ⟨27989297065271715802651237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37319062753695621070201649 27989297065271715802651237)
                ·
                  refine ⟨5247993199738446712997107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27989297065271715802651237 5247993199738446712997107)
                  ·
                    refine ⟨7871989799607670069495661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5247993199738446712997107 7871989799607670069495661)
                    ·
                      refine ⟨2951996174852876276060873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7871989799607670069495661 2951996174852876276060873)
                      ·
                        rfl

theorem cell23_5748992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_5748992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748992 prefixEnd_5748992 := by exact prefixLift 5748992
  have htrace : WordTrace (prefixWord ++ tailWord_5748992) baseStart_5748992 baseEnd_5748992 := by
    simpa [prefixWord, tailWord_5748992, baseEnd_5748992] using wordTrace_append hprefix tailTrace_5748992
  have hstable : (prefixWord ++ tailWord_5748992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748992).length < 2 ^ (prefixWord ++ tailWord_5748992).sum := by decide
  have hdescent : baseEnd_5748992 < baseStart_5748992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5748999 : List Nat := [1, 1, 4, 5, 2, 1, 9]
def baseStart_5748999 : Nat := 118140960795 + 5748999 * 2 ^ 59
def prefixEnd_5748999 : Nat := 4983230072969 + 3 ^ 40 * 5748999 * 2
def baseEnd_5748999 : Nat := 36444441595277256156461

theorem tailTrace_5748999 : CollatzResearch.WordTrace tailWord_5748999 prefixEnd_5748999 36444441595277256156461 := by
  unfold tailWord_5748999
  simp only [CollatzResearch.WordTrace]
  refine ⟨209683219699365948705170051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139788813132910632470113367 209683219699365948705170051)
  ·
    refine ⟨314524829549048923057755077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209683219699365948705170051 314524829549048923057755077)
    ·
      refine ⟨58973405540446673073329077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314524829549048923057755077 58973405540446673073329077)
      ·
        refine ⟨5528756769416875600624601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58973405540446673073329077 5528756769416875600624601)
        ·
          refine ⟨4146567577062656700468451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5528756769416875600624601 4146567577062656700468451)
          ·
            refine ⟨6219851365593985050702677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146567577062656700468451 6219851365593985050702677)
            ·
              refine ⟨36444441595277256156461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6219851365593985050702677 36444441595277256156461)
              ·
                rfl

theorem cell23_5748999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 9].length) (baseStart_5748999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5748999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5748999 prefixEnd_5748999 := by exact prefixLift 5748999
  have htrace : WordTrace (prefixWord ++ tailWord_5748999) baseStart_5748999 baseEnd_5748999 := by
    simpa [prefixWord, tailWord_5748999, baseEnd_5748999] using wordTrace_append hprefix tailTrace_5748999
  have hstable : (prefixWord ++ tailWord_5748999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5748999).length < 2 ^ (prefixWord ++ tailWord_5748999).sum := by decide
  have hdescent : baseEnd_5748999 < baseStart_5748999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5748999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749025 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5749025 : Nat := 118140960795 + 5749025 * 2 ^ 59
def prefixEnd_5749025 : Nat := 4983230072969 + 3 ^ 40 * 5749025 * 2
def baseEnd_5749025 : Nat := 984004373238158215649407

theorem tailTrace_5749025 : CollatzResearch.WordTrace tailWord_5749025 prefixEnd_5749025 984004373238158215649407 := by
  unfold tailWord_5749025
  simp only [CollatzResearch.WordTrace]
  refine ⟨209684167997271755145616529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139789445331514503430411019 209684167997271755145616529)
  ·
    refine ⟨157263125997953816359212397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209684167997271755145616529 157263125997953816359212397)
    ·
      refine ⟨58973672249232681134704649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157263125997953816359212397 58973672249232681134704649)
      ·
        refine ⟨44230254186924510851028487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58973672249232681134704649 44230254186924510851028487)
        ·
          refine ⟨66345381280386766276542731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44230254186924510851028487 66345381280386766276542731)
          ·
            refine ⟨99518071920580149414814097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66345381280386766276542731 99518071920580149414814097)
            ·
              refine ⟨74638553940435112061110573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99518071920580149414814097 74638553940435112061110573)
              ·
                refine ⟨27989457727663167022916465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74638553940435112061110573 27989457727663167022916465)
                ·
                  refine ⟨20992093295747375267187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27989457727663167022916465 20992093295747375267187349)
                  ·
                    refine ⟨984004373238158215649407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20992093295747375267187349 984004373238158215649407)
                    ·
                      rfl

theorem cell23_5749025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5749025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749025 prefixEnd_5749025 := by exact prefixLift 5749025
  have htrace : WordTrace (prefixWord ++ tailWord_5749025) baseStart_5749025 baseEnd_5749025 := by
    simpa [prefixWord, tailWord_5749025, baseEnd_5749025] using wordTrace_append hprefix tailTrace_5749025
  have hstable : (prefixWord ++ tailWord_5749025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749025).length < 2 ^ (prefixWord ++ tailWord_5749025).sum := by decide
  have hdescent : baseEnd_5749025 < baseStart_5749025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749026 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_5749026 : Nat := 118140960795 + 5749026 * 2 ^ 59
def prefixEnd_5749026 : Nat := 4983230072969 + 3 ^ 40 * 5749026 * 2
def baseEnd_5749026 : Nat := 2952013633195129143035717

theorem tailTrace_5749026 : CollatzResearch.WordTrace tailWord_5749026 prefixEnd_5749026 2952013633195129143035717 := by
  unfold tailWord_5749026
  simp only [CollatzResearch.WordTrace]
  refine ⟨52421051117567033079100733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139789469646845421544268621 52421051117567033079100733)
  ·
    refine ⟨19657894169087637404662775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52421051117567033079100733 19657894169087637404662775)
    ·
      refine ⟨29486841253631456106994163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19657894169087637404662775 29486841253631456106994163)
      ·
        refine ⟨44230261880447184160491245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29486841253631456106994163 44230261880447184160491245)
        ·
          refine ⟨16586348205167694060184217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44230261880447184160491245 16586348205167694060184217)
          ·
            refine ⟨12439761153875770545138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16586348205167694060184217 12439761153875770545138163)
            ·
              refine ⟨18659641730813655817707245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12439761153875770545138163 18659641730813655817707245)
              ·
                refine ⟨6997365649055120931640217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18659641730813655817707245 6997365649055120931640217)
                ·
                  refine ⟨5248024236791340698730163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6997365649055120931640217 5248024236791340698730163)
                  ·
                    refine ⟨7872036355187011048095245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248024236791340698730163 7872036355187011048095245)
                    ·
                      refine ⟨2952013633195129143035717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872036355187011048095245 2952013633195129143035717)
                      ·
                        rfl

theorem cell23_5749026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_5749026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749026 prefixEnd_5749026 := by exact prefixLift 5749026
  have htrace : WordTrace (prefixWord ++ tailWord_5749026) baseStart_5749026 baseEnd_5749026 := by
    simpa [prefixWord, tailWord_5749026, baseEnd_5749026] using wordTrace_append hprefix tailTrace_5749026
  have hstable : (prefixWord ++ tailWord_5749026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749026).length < 2 ^ (prefixWord ++ tailWord_5749026).sum := by decide
  have hdescent : baseEnd_5749026 < baseStart_5749026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749049 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5749049 : Nat := 118140960795 + 5749049 * 2 ^ 59
def prefixEnd_5749049 : Nat := 4983230072969 + 3 ^ 40 * 5749049 * 2
def baseEnd_5749049 : Nat := 2952025443250182553048111

theorem tailTrace_5749049 : CollatzResearch.WordTrace tailWord_5749049 prefixEnd_5749049 2952025443250182553048111 := by
  unfold tailWord_5749049
  simp only [CollatzResearch.WordTrace]
  refine ⟨209685043349184807244490201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139790028899456538162993467 209685043349184807244490201)
  ·
    refine ⟨157263782511888605433367651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209685043349184807244490201 157263782511888605433367651)
    ·
      refine ⟨235895673767832908150051477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157263782511888605433367651 235895673767832908150051477)
      ·
        refine ⟨11057609707867167569533663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235895673767832908150051477 11057609707867167569533663)
        ·
          refine ⟨16586414561800751354300495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057609707867167569533663 16586414561800751354300495)
          ·
            refine ⟨24879621842701127031450743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16586414561800751354300495 24879621842701127031450743)
            ·
              refine ⟨37319432764051690547176115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24879621842701127031450743 37319432764051690547176115)
              ·
                refine ⟨55979149146077535820764173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37319432764051690547176115 55979149146077535820764173)
                ·
                  refine ⟨20992180929779075932786565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55979149146077535820764173 20992180929779075932786565)
                  ·
                    refine ⟨3936033924333576737397481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20992180929779075932786565 3936033924333576737397481)
                    ·
                      refine ⟨2952025443250182553048111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936033924333576737397481 2952025443250182553048111)
                      ·
                        rfl

theorem cell23_5749049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5749049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749049 prefixEnd_5749049 := by exact prefixLift 5749049
  have htrace : WordTrace (prefixWord ++ tailWord_5749049) baseStart_5749049 baseEnd_5749049 := by
    simpa [prefixWord, tailWord_5749049, baseEnd_5749049] using wordTrace_append hprefix tailTrace_5749049
  have hstable : (prefixWord ++ tailWord_5749049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749049).length < 2 ^ (prefixWord ++ tailWord_5749049).sum := by decide
  have hdescent : baseEnd_5749049 < baseStart_5749049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749159 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5749159 : Nat := 118140960795 + 5749159 * 2 ^ 59
def prefixEnd_5749159 : Nat := 4983230072969 + 3 ^ 40 * 5749159 * 2
def baseEnd_5749159 : Nat := 2952081926122177122672605

theorem tailTrace_5749159 : CollatzResearch.WordTrace tailWord_5749159 prefixEnd_5749159 2952081926122177122672605 := by
  unfold tailWord_5749159
  simp only [CollatzResearch.WordTrace]
  refine ⟨209689055378786296030994531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139792703585857530687329687 209689055378786296030994531)
  ·
    refine ⟨314533583068179444046491797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209689055378786296030994531 314533583068179444046491797)
    ·
      refine ⟨14743761706320911439679303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314533583068179444046491797 14743761706320911439679303)
      ·
        refine ⟨22115642559481367159518955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14743761706320911439679303 22115642559481367159518955)
        ·
          refine ⟨33173463839222050739278433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22115642559481367159518955 33173463839222050739278433)
          ·
            refine ⟨24880097879416538054458825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33173463839222050739278433 24880097879416538054458825)
            ·
              refine ⟨18660073409562403540844119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24880097879416538054458825 18660073409562403540844119)
              ·
                refine ⟨27990110114343605311266179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18660073409562403540844119 27990110114343605311266179)
                ·
                  refine ⟨41985165171515407966899269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27990110114343605311266179 41985165171515407966899269)
                  ·
                    refine ⟨7872218469659138993793613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41985165171515407966899269 7872218469659138993793613)
                    ·
                      refine ⟨2952081926122177122672605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872218469659138993793613 2952081926122177122672605)
                      ·
                        rfl

theorem cell23_5749159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5749159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749159 prefixEnd_5749159 := by exact prefixLift 5749159
  have htrace : WordTrace (prefixWord ++ tailWord_5749159) baseStart_5749159 baseEnd_5749159 := by
    simpa [prefixWord, tailWord_5749159, baseEnd_5749159] using wordTrace_append hprefix tailTrace_5749159
  have hstable : (prefixWord ++ tailWord_5749159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749159).length < 2 ^ (prefixWord ++ tailWord_5749159).sum := by decide
  have hdescent : baseEnd_5749159 < baseStart_5749159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749182 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5749182 : Nat := 118140960795 + 5749182 * 2 ^ 59
def prefixEnd_5749182 : Nat := 4983230072969 + 3 ^ 40 * 5749182 * 2
def baseEnd_5749182 : Nat := 2952093736177230532684999

theorem tailTrace_5749182 : CollatzResearch.WordTrace tailWord_5749182 prefixEnd_5749182 2952093736177230532684999 := by
  unfold tailWord_5749182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211236782212871369885225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139793262838468647306054533 26211236782212871369885225)
  ·
    refine ⟨19658427586659653527413919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26211236782212871369885225 19658427586659653527413919)
    ·
      refine ⟨29487641379989480291120879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658427586659653527413919 29487641379989480291120879)
      ·
        refine ⟨44231462069984220436681319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29487641379989480291120879 44231462069984220436681319)
        ·
          refine ⟨66347193104976330655021979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44231462069984220436681319 66347193104976330655021979)
          ·
            refine ⟨99520789657464495982532969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66347193104976330655021979 99520789657464495982532969)
            ·
              refine ⟨74640592243098371986899727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99520789657464495982532969 74640592243098371986899727)
              ·
                refine ⟨111960888364647557980349591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74640592243098371986899727 111960888364647557980349591)
                ·
                  refine ⟨167941332546971336970524387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111960888364647557980349591 167941332546971336970524387)
                  ·
                    refine ⟨251911998820457005455786581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167941332546971336970524387 251911998820457005455786581)
                    ·
                      refine ⟨2952093736177230532684999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 251911998820457005455786581 2952093736177230532684999)
                      ·
                        rfl

theorem cell23_5749182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5749182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749182 prefixEnd_5749182 := by exact prefixLift 5749182
  have htrace : WordTrace (prefixWord ++ tailWord_5749182) baseStart_5749182 baseEnd_5749182 := by
    simpa [prefixWord, tailWord_5749182, baseEnd_5749182] using wordTrace_append hprefix tailTrace_5749182
  have hstable : (prefixWord ++ tailWord_5749182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749182).length < 2 ^ (prefixWord ++ tailWord_5749182).sum := by decide
  have hdescent : baseEnd_5749182 < baseStart_5749182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749199 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 6, 3, 2]
def baseStart_5749199 : Nat := 118140960795 + 5749199 * 2 ^ 59
def prefixEnd_5749199 : Nat := 4983230072969 + 3 ^ 40 * 5749199 * 2
def baseEnd_5749199 : Nat := 2952102465348356966172421

theorem tailTrace_5749199 : CollatzResearch.WordTrace tailWord_5749199 prefixEnd_5749199 2952102465348356966172421 := by
  unfold tailWord_5749199
  simp only [CollatzResearch.WordTrace]
  refine ⟨209690514298641382862450651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139793676199094255241633767 209690514298641382862450651)
  ·
    refine ⟨314535771447962074293675977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209690514298641382862450651 314535771447962074293675977)
    ·
      refine ⟨235901828585971555720256983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314535771447962074293675977 235901828585971555720256983)
      ·
        refine ⟨353852742878957333580385475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235901828585971555720256983 353852742878957333580385475)
        ·
          refine ⟨530779114318436000370578213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353852742878957333580385475 530779114318436000370578213)
          ·
            refine ⟨99521083934706750069483415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530779114318436000370578213 99521083934706750069483415)
            ·
              refine ⟨149281625902060125104225123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99521083934706750069483415 149281625902060125104225123)
              ·
                refine ⟨223922438853090187656337685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149281625902060125104225123 223922438853090187656337685)
                ·
                  refine ⟨10496364321238602546390829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223922438853090187656337685 10496364321238602546390829)
                  ·
                    refine ⟨3936136620464475954896561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10496364321238602546390829 3936136620464475954896561)
                    ·
                      refine ⟨2952102465348356966172421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936136620464475954896561 2952102465348356966172421)
                      ·
                        rfl

theorem cell23_5749199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3, 2].length) (baseStart_5749199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749199 prefixEnd_5749199 := by exact prefixLift 5749199
  have htrace : WordTrace (prefixWord ++ tailWord_5749199) baseStart_5749199 baseEnd_5749199 := by
    simpa [prefixWord, tailWord_5749199, baseEnd_5749199] using wordTrace_append hprefix tailTrace_5749199
  have hstable : (prefixWord ++ tailWord_5749199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749199).length < 2 ^ (prefixWord ++ tailWord_5749199).sum := by decide
  have hdescent : baseEnd_5749199 < baseStart_5749199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749216 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2]
def baseStart_5749216 : Nat := 118140960795 + 5749216 * 2 ^ 59
def prefixEnd_5749216 : Nat := 4983230072969 + 3 ^ 40 * 5749216 * 2
def baseEnd_5749216 : Nat := 2952111194519483399659843

theorem tailTrace_5749216 : CollatzResearch.WordTrace tailWord_5749216 prefixEnd_5749216 2952111194519483399659843 := by
  unfold tailWord_5749216
  simp only [CollatzResearch.WordTrace]
  refine ⟨104845567169789897382909751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139794089559719863177213001 104845567169789897382909751)
  ·
    refine ⟨157268350754684846074364627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104845567169789897382909751 157268350754684846074364627)
    ·
      refine ⟨235902526132027269111546941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157268350754684846074364627 235902526132027269111546941)
      ·
        refine ⟨88463447299510225916830103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235902526132027269111546941 88463447299510225916830103)
        ·
          refine ⟨132695170949265338875245155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88463447299510225916830103 132695170949265338875245155)
          ·
            refine ⟨199042756423898008312867733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132695170949265338875245155 199042756423898008312867733)
            ·
              refine ⟨9330129207370219139665675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199042756423898008312867733 9330129207370219139665675)
              ·
                refine ⟨13995193811055328709498513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330129207370219139665675 13995193811055328709498513)
                ·
                  refine ⟨10496395358291496532123885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13995193811055328709498513 10496395358291496532123885)
                  ·
                    refine ⟨3936148259359311199546457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10496395358291496532123885 3936148259359311199546457)
                    ·
                      refine ⟨2952111194519483399659843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936148259359311199546457 2952111194519483399659843)
                      ·
                        rfl

theorem cell23_5749216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_5749216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749216 prefixEnd_5749216 := by exact prefixLift 5749216
  have htrace : WordTrace (prefixWord ++ tailWord_5749216) baseStart_5749216 baseEnd_5749216 := by
    simpa [prefixWord, tailWord_5749216, baseEnd_5749216] using wordTrace_append hprefix tailTrace_5749216
  have hstable : (prefixWord ++ tailWord_5749216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749216).length < 2 ^ (prefixWord ++ tailWord_5749216).sum := by decide
  have hdescent : baseEnd_5749216 < baseStart_5749216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749223 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5749223 : Nat := 118140960795 + 5749223 * 2 ^ 59
def prefixEnd_5749223 : Nat := 4983230072969 + 3 ^ 40 * 5749223 * 2
def baseEnd_5749223 : Nat := 2952114788884064872272311

theorem tailTrace_5749223 : CollatzResearch.WordTrace tailWord_5749223 prefixEnd_5749223 2952114788884064872272311 := by
  unfold tailWord_5749223
  simp only [CollatzResearch.WordTrace]
  refine ⟨209691389650554434961324323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139794259767036289974216215 209691389650554434961324323)
  ·
    refine ⟨314537084475831652441986485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209691389650554434961324323 314537084475831652441986485)
    ·
      refine ⟨29487851669609217416436233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314537084475831652441986485 29487851669609217416436233)
      ·
        refine ⟨22115888752206913062327175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29487851669609217416436233 22115888752206913062327175)
        ·
          refine ⟨33173833128310369593490763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22115888752206913062327175 33173833128310369593490763)
          ·
            refine ⟨49760749692465554390236145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33173833128310369593490763 49760749692465554390236145)
            ·
              refine ⟨37320562269349165792677109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49760749692465554390236145 37320562269349165792677109)
              ·
                refine ⟨3498802712751484293063479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37320562269349165792677109 3498802712751484293063479)
                ·
                  refine ⟨5248204069127226439595219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498802712751484293063479 5248204069127226439595219)
                  ·
                    refine ⟨7872306103690839659392829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248204069127226439595219 7872306103690839659392829)
                    ·
                      refine ⟨2952114788884064872272311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872306103690839659392829 2952114788884064872272311)
                      ·
                        rfl

theorem cell23_5749223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5749223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749223 prefixEnd_5749223 := by exact prefixLift 5749223
  have htrace : WordTrace (prefixWord ++ tailWord_5749223) baseStart_5749223 baseEnd_5749223 := by
    simpa [prefixWord, tailWord_5749223, baseEnd_5749223] using wordTrace_append hprefix tailTrace_5749223
  have hstable : (prefixWord ++ tailWord_5749223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749223).length < 2 ^ (prefixWord ++ tailWord_5749223).sum := by decide
  have hdescent : baseEnd_5749223 < baseStart_5749223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749242 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_5749242 : Nat := 118140960795 + 5749242 * 2 ^ 59
def prefixEnd_5749242 : Nat := 4983230072969 + 3 ^ 40 * 5749242 * 2
def baseEnd_5749242 : Nat := 2952124545016500297934723

theorem tailTrace_5749242 : CollatzResearch.WordTrace tailWord_5749242 prefixEnd_5749242 2952124545016500297934723 := by
  unfold tailWord_5749242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52423020659371400301566495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139794721758323734137510653 52423020659371400301566495)
  ·
    refine ⟨78634530989057100452349743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52423020659371400301566495 78634530989057100452349743)
    ·
      refine ⟨117951796483585650678524615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78634530989057100452349743 117951796483585650678524615)
      ·
        refine ⟨176927694725378476017786923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117951796483585650678524615 176927694725378476017786923)
        ·
          refine ⟨265391542088067714026680385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176927694725378476017786923 265391542088067714026680385)
          ·
            refine ⟨199043656566050785520010289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265391542088067714026680385 199043656566050785520010289)
            ·
              refine ⟨149282742424538089140007717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199043656566050785520010289 149282742424538089140007717)
              ·
                refine ⟨27990514204600891713751447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149282742424538089140007717 27990514204600891713751447)
                ·
                  refine ⟨41985771306901337570627171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27990514204600891713751447 41985771306901337570627171)
                  ·
                    refine ⟨62978656960352006355940757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41985771306901337570627171 62978656960352006355940757)
                    ·
                      refine ⟨2952124545016500297934723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62978656960352006355940757 2952124545016500297934723)
                      ·
                        rfl

theorem cell23_5749242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_5749242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749242 prefixEnd_5749242 := by exact prefixLift 5749242
  have htrace : WordTrace (prefixWord ++ tailWord_5749242) baseStart_5749242 baseEnd_5749242 := by
    simpa [prefixWord, tailWord_5749242, baseEnd_5749242] using wordTrace_append hprefix tailTrace_5749242
  have hstable : (prefixWord ++ tailWord_5749242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749242).length < 2 ^ (prefixWord ++ tailWord_5749242).sum := by decide
  have hdescent : baseEnd_5749242 < baseStart_5749242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749259 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_5749259 : Nat := 118140960795 + 5749259 * 2 ^ 59
def prefixEnd_5749259 : Nat := 4983230072969 + 3 ^ 40 * 5749259 * 2
def baseEnd_5749259 : Nat := 2952133274187626731422145

theorem tailTrace_5749259 : CollatzResearch.WordTrace tailWord_5749259 prefixEnd_5749259 2952133274187626731422145 := by
  unfold tailWord_5749259
  simp only [CollatzResearch.WordTrace]
  refine ⟨209692702678424013109634831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139795135118949342073089887 209692702678424013109634831)
  ·
    refine ⟨314539054017636019664452247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209692702678424013109634831 314539054017636019664452247)
    ·
      refine ⟨471808581026454029496678371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314539054017636019664452247 471808581026454029496678371)
      ·
        refine ⟨707712871539681044245017557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471808581026454029496678371 707712871539681044245017557)
        ·
          refine ⟨16587020426711274474492599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 707712871539681044245017557 16587020426711274474492599)
          ·
            refine ⟨24880530640066911711738899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16587020426711274474492599 24880530640066911711738899)
            ·
              refine ⟨37320795960100367567608349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24880530640066911711738899 37320795960100367567608349)
              ·
                refine ⟨13995298485037637837853131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37320795960100367567608349 13995298485037637837853131)
                ·
                  refine ⟨20992947727556456756779697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13995298485037637837853131 20992947727556456756779697)
                  ·
                    refine ⟨15744710795667342567584773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20992947727556456756779697 15744710795667342567584773)
                    ·
                      refine ⟨2952133274187626731422145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15744710795667342567584773 2952133274187626731422145)
                      ·
                        rfl

theorem cell23_5749259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_5749259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749259 prefixEnd_5749259 := by exact prefixLift 5749259
  have htrace : WordTrace (prefixWord ++ tailWord_5749259) baseStart_5749259 baseEnd_5749259 := by
    simpa [prefixWord, tailWord_5749259, baseEnd_5749259] using wordTrace_append hprefix tailTrace_5749259
  have hstable : (prefixWord ++ tailWord_5749259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749259).length < 2 ^ (prefixWord ++ tailWord_5749259).sum := by decide
  have hdescent : baseEnd_5749259 < baseStart_5749259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749269 : List Nat := [1, 3, 2, 1, 3, 1, 5, 7]
def baseStart_5749269 : Nat := 118140960795 + 5749269 * 2 ^ 59
def prefixEnd_5749269 : Nat := 4983230072969 + 3 ^ 40 * 5749269 * 2
def baseEnd_5749269 : Nat := 109338459592376729344337

theorem tailTrace_5749269 : CollatzResearch.WordTrace tailWord_5749269 prefixEnd_5749269 109338459592376729344337 := by
  unfold tailWord_5749269
  simp only [CollatzResearch.WordTrace]
  refine ⟨209693067408387784817498861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139795378272258523211665907 209693067408387784817498861)
  ·
    refine ⟨78634900278145419306562073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209693067408387784817498861 78634900278145419306562073)
    ·
      refine ⟨58976175208609064479921555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78634900278145419306562073 58976175208609064479921555)
      ·
        refine ⟨88464262812913596719882333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58976175208609064479921555 88464262812913596719882333)
        ·
          refine ⟨33174098554842598769955875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88464262812913596719882333 33174098554842598769955875)
          ·
            refine ⟨49761147832263898154933813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33174098554842598769955875 49761147832263898154933813)
            ·
              refine ⟨4665107609274740452025045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49761147832263898154933813 4665107609274740452025045)
              ·
                refine ⟨109338459592376729344337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4665107609274740452025045 109338459592376729344337)
                ·
                  rfl

theorem cell23_5749269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 7].length) (baseStart_5749269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749269 prefixEnd_5749269 := by exact prefixLift 5749269
  have htrace : WordTrace (prefixWord ++ tailWord_5749269) baseStart_5749269 baseEnd_5749269 := by
    simpa [prefixWord, tailWord_5749269, baseEnd_5749269] using wordTrace_append hprefix tailTrace_5749269
  have hstable : (prefixWord ++ tailWord_5749269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749269).length < 2 ^ (prefixWord ++ tailWord_5749269).sum := by decide
  have hdescent : baseEnd_5749269 < baseStart_5749269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749280 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5749280 : Nat := 118140960795 + 5749280 * 2 ^ 59
def prefixEnd_5749280 : Nat := 4983230072969 + 3 ^ 40 * 5749280 * 2
def baseEnd_5749280 : Nat := 2952144057281371149259549

theorem tailTrace_5749280 : CollatzResearch.WordTrace tailWord_5749280 prefixEnd_5749280 2952144057281371149259549 := by
  unfold tailWord_5749280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104846734305673966848074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139795645740898622464099529 104846734305673966848074647)
  ·
    refine ⟨157270101458510950272111971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104846734305673966848074647 157270101458510950272111971)
    ·
      refine ⟨235905152187766425408167957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157270101458510950272111971 235905152187766425408167957)
      ·
        refine ⟨11058054008801551191007873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235905152187766425408167957 11058054008801551191007873)
        ·
          refine ⟨8293540506601163393255905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11058054008801551191007873 8293540506601163393255905)
          ·
            refine ⟨6220155379950872544941929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293540506601163393255905 6220155379950872544941929)
            ·
              refine ⟨4665116534963154408706447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220155379950872544941929 4665116534963154408706447)
              ·
                refine ⟨6997674802444731613059671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665116534963154408706447 6997674802444731613059671)
                ·
                  refine ⟨10496512203667097419589507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6997674802444731613059671 10496512203667097419589507)
                  ·
                    refine ⟨15744768305500646129384261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10496512203667097419589507 15744768305500646129384261)
                    ·
                      refine ⟨2952144057281371149259549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15744768305500646129384261 2952144057281371149259549)
                      ·
                        rfl

theorem cell23_5749280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5749280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749280 prefixEnd_5749280 := by exact prefixLift 5749280
  have htrace : WordTrace (prefixWord ++ tailWord_5749280) baseStart_5749280 baseEnd_5749280 := by
    simpa [prefixWord, tailWord_5749280, baseEnd_5749280] using wordTrace_append hprefix tailTrace_5749280
  have hstable : (prefixWord ++ tailWord_5749280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749280).length < 2 ^ (prefixWord ++ tailWord_5749280).sum := by decide
  have hdescent : baseEnd_5749280 < baseStart_5749280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749283 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 1, 2, 3]
def baseStart_5749283 : Nat := 118140960795 + 5749283 * 2 ^ 59
def prefixEnd_5749283 : Nat := 4983230072969 + 3 ^ 40 * 5749283 * 2
def baseEnd_5749283 : Nat := 2952145597723334637522035

theorem tailTrace_5749283 : CollatzResearch.WordTrace tailWord_5749283 prefixEnd_5749283 2952145597723334637522035 := by
  unfold tailWord_5749283
  simp only [CollatzResearch.WordTrace]
  refine ⟨209693578030337065208508503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139795718686891376805672335 209693578030337065208508503)
  ·
    refine ⟨314540367045505597812762755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209693578030337065208508503 314540367045505597812762755)
    ·
      refine ⟨471810550568258396719144133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314540367045505597812762755 471810550568258396719144133)
      ·
        refine ⟨88464478231548449384839525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471810550568258396719144133 88464478231548449384839525)
        ·
          refine ⟨16587089668415334259657411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88464478231548449384839525 16587089668415334259657411)
          ·
            refine ⟨24880634502623001389486117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16587089668415334259657411 24880634502623001389486117)
            ·
              refine ⟨4665118969241812760528647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24880634502623001389486117 4665118969241812760528647)
              ·
                refine ⟨6997678453862719140792971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665118969241812760528647 6997678453862719140792971)
                ·
                  refine ⟨10496517680794078711189457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6997678453862719140792971 10496517680794078711189457)
                  ·
                    refine ⟨7872388260595559033392093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10496517680794078711189457 7872388260595559033392093)
                    ·
                      refine ⟨2952145597723334637522035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872388260595559033392093 2952145597723334637522035)
                      ·
                        rfl

theorem cell23_5749283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_5749283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749283 prefixEnd_5749283 := by exact prefixLift 5749283
  have htrace : WordTrace (prefixWord ++ tailWord_5749283) baseStart_5749283 baseEnd_5749283 := by
    simpa [prefixWord, tailWord_5749283, baseEnd_5749283] using wordTrace_append hprefix tailTrace_5749283
  have hstable : (prefixWord ++ tailWord_5749283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749283).length < 2 ^ (prefixWord ++ tailWord_5749283).sum := by decide
  have hdescent : baseEnd_5749283 < baseStart_5749283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749310 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5749310 : Nat := 118140960795 + 5749310 * 2 ^ 59
def prefixEnd_5749310 : Nat := 4983230072969 + 3 ^ 40 * 5749310 * 2
def baseEnd_5749310 : Nat := 2952159461701006031884411

theorem tailTrace_5749310 : CollatzResearch.WordTrace tailWord_5749310 prefixEnd_5749310 2952159461701006031884411 := by
  unfold tailWord_5749310
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211820350154906102467673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139796375200826165879827589 26211820350154906102467673)
  ·
    refine ⟨19658865262616179576850755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26211820350154906102467673 19658865262616179576850755)
    ·
      refine ⟨29488297893924269365276133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658865262616179576850755 29488297893924269365276133)
      ·
        refine ⟨5529055855110800505989275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29488297893924269365276133 5529055855110800505989275)
        ·
          refine ⟨8293583782666200758983913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529055855110800505989275 8293583782666200758983913)
          ·
            refine ⟨6220187836999650569237935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293583782666200758983913 6220187836999650569237935)
            ·
              refine ⟨9330281755499475853856903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220187836999650569237935 9330281755499475853856903)
              ·
                refine ⟨13995422633249213780785355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330281755499475853856903 13995422633249213780785355)
                ·
                  refine ⟨20993133949873820671178033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13995422633249213780785355 20993133949873820671178033)
                  ·
                    refine ⟨15744850462405365503383525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20993133949873820671178033 15744850462405365503383525)
                    ·
                      refine ⟨2952159461701006031884411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15744850462405365503383525 2952159461701006031884411)
                      ·
                        rfl

theorem cell23_5749310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5749310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749310 prefixEnd_5749310 := by exact prefixLift 5749310
  have htrace : WordTrace (prefixWord ++ tailWord_5749310) baseStart_5749310 baseEnd_5749310 := by
    simpa [prefixWord, tailWord_5749310, baseEnd_5749310] using wordTrace_append hprefix tailTrace_5749310
  have hstable : (prefixWord ++ tailWord_5749310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749310).length < 2 ^ (prefixWord ++ tailWord_5749310).sum := by decide
  have hdescent : baseEnd_5749310 < baseStart_5749310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749313 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5749313 : Nat := 118140960795 + 5749313 * 2 ^ 59
def prefixEnd_5749313 : Nat := 4983230072969 + 3 ^ 40 * 5749313 * 2
def baseEnd_5749313 : Nat := 2952161002142969520146897

theorem tailTrace_5749313 : CollatzResearch.WordTrace tailWord_5749313 prefixEnd_5749313 2952161002142969520146897 := by
  unfold tailWord_5749313
  simp only [CollatzResearch.WordTrace]
  refine ⟨209694672220228380332100593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139796448146818920221400395 209694672220228380332100593)
  ·
    refine ⟨157271004165171285249075445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209694672220228380332100593 157271004165171285249075445)
    ·
      refine ⟨14744156640484807992100823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157271004165171285249075445 14744156640484807992100823)
      ·
        refine ⟨22116234960727211988151235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14744156640484807992100823 22116234960727211988151235)
        ·
          refine ⟨33174352441090817982226853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22116234960727211988151235 33174352441090817982226853)
          ·
            refine ⟨6220191082704528371667535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33174352441090817982226853 6220191082704528371667535)
            ·
              refine ⟨9330286624056792557501303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220191082704528371667535 9330286624056792557501303)
              ·
                refine ⟨13995429936085188836251955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330286624056792557501303 13995429936085188836251955)
                ·
                  refine ⟨20993144904127783254377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13995429936085188836251955 20993144904127783254377933)
                  ·
                    refine ⟨7872429339047918720391725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20993144904127783254377933 7872429339047918720391725)
                    ·
                      refine ⟨2952161002142969520146897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872429339047918720391725 2952161002142969520146897)
                      ·
                        rfl

theorem cell23_5749313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5749313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749313 prefixEnd_5749313 := by exact prefixLift 5749313
  have htrace : WordTrace (prefixWord ++ tailWord_5749313) baseStart_5749313 baseEnd_5749313 := by
    simpa [prefixWord, tailWord_5749313, baseEnd_5749313] using wordTrace_append hprefix tailTrace_5749313
  have hstable : (prefixWord ++ tailWord_5749313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749313).length < 2 ^ (prefixWord ++ tailWord_5749313).sum := by decide
  have hdescent : baseEnd_5749313 < baseStart_5749313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749336 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_5749336 : Nat := 118140960795 + 5749336 * 2 ^ 59
def prefixEnd_5749336 : Nat := 4983230072969 + 3 ^ 40 * 5749336 * 2
def baseEnd_5749336 : Nat := 2952172812198022930159291

theorem tailTrace_5749336 : CollatzResearch.WordTrace tailWord_5749336 prefixEnd_5749336 2952172812198022930159291 := by
  unfold tailWord_5749336
  simp only [CollatzResearch.WordTrace]
  refine ⟨104847755549572527630093931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139797007399430036840125241 104847755549572527630093931)
  ·
    refine ⟨157271633324358791445140897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104847755549572527630093931 157271633324358791445140897)
    ·
      refine ⟨117953724993269093583855673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157271633324358791445140897 117953724993269093583855673)
      ·
        refine ⟨88465293744951820187891755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117953724993269093583855673 88465293744951820187891755)
        ·
          refine ⟨132697940617427730281837633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88465293744951820187891755 132697940617427730281837633)
          ·
            refine ⟨99523455463070797711378225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132697940617427730281837633 99523455463070797711378225)
            ·
              refine ⟨74642591597303098283533669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99523455463070797711378225 74642591597303098283533669)
              ·
                refine ⟨13995485924494330928162563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74642591597303098283533669 13995485924494330928162563)
                ·
                  refine ⟨20993228886741496392243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13995485924494330928162563 20993228886741496392243845)
                  ·
                    refine ⟨3936230416264030573545721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20993228886741496392243845 3936230416264030573545721)
                    ·
                      refine ⟨2952172812198022930159291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936230416264030573545721 2952172812198022930159291)
                      ·
                        rfl

theorem cell23_5749336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_5749336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749336 prefixEnd_5749336 := by exact prefixLift 5749336
  have htrace : WordTrace (prefixWord ++ tailWord_5749336) baseStart_5749336 baseEnd_5749336 := by
    simpa [prefixWord, tailWord_5749336, baseEnd_5749336] using wordTrace_append hprefix tailTrace_5749336
  have hstable : (prefixWord ++ tailWord_5749336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749336).length < 2 ^ (prefixWord ++ tailWord_5749336).sum := by decide
  have hdescent : baseEnd_5749336 < baseStart_5749336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749353 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 2, 2, 2]
def baseStart_5749353 : Nat := 118140960795 + 5749353 * 2 ^ 59
def prefixEnd_5749353 : Nat := 4983230072969 + 3 ^ 40 * 5749353 * 2
def baseEnd_5749353 : Nat := 2952181541369149363646713

theorem tailTrace_5749353 : CollatzResearch.WordTrace tailWord_5749353 prefixEnd_5749353 2952181541369149363646713 := by
  unfold tailWord_5749353
  simp only [CollatzResearch.WordTrace]
  refine ⟨209696131140083467163556713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139797420760055644775704475 209696131140083467163556713)
  ·
    refine ⟨157272098355062600372667535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209696131140083467163556713 157272098355062600372667535)
    ·
      refine ⟨235908147532593900559001303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157272098355062600372667535 235908147532593900559001303)
      ·
        refine ⟨353862221298890850838501955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235908147532593900559001303 353862221298890850838501955)
        ·
          refine ⟨530793331948336276257752933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353862221298890850838501955 530793331948336276257752933)
          ·
            refine ⟨99523749740313051798328675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530793331948336276257752933 99523749740313051798328675)
            ·
              refine ⟨149285624610469577697493013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99523749740313051798328675 149285624610469577697493013)
              ·
                refine ⟨6997763653615761454569985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149285624610469577697493013 6997763653615761454569985)
                ·
                  refine ⟨5248322740211821090927489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6997763653615761454569985 5248322740211821090927489)
                  ·
                    refine ⟨3936242055158865818195617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5248322740211821090927489 3936242055158865818195617)
                    ·
                      refine ⟨2952181541369149363646713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936242055158865818195617 2952181541369149363646713)
                      ·
                        rfl

theorem cell23_5749353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2, 2].length) (baseStart_5749353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749353 prefixEnd_5749353 := by exact prefixLift 5749353
  have htrace : WordTrace (prefixWord ++ tailWord_5749353) baseStart_5749353 baseEnd_5749353 := by
    simpa [prefixWord, tailWord_5749353, baseEnd_5749353] using wordTrace_append hprefix tailTrace_5749353
  have hstable : (prefixWord ++ tailWord_5749353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749353).length < 2 ^ (prefixWord ++ tailWord_5749353).sum := by decide
  have hdescent : baseEnd_5749353 < baseStart_5749353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749359 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 7]
def baseStart_5749359 : Nat := 118140960795 + 5749359 * 2 ^ 59
def prefixEnd_5749359 : Nat := 4983230072969 + 3 ^ 40 * 5749359 * 2
def baseEnd_5749359 : Nat := 328020513583675148907965

theorem tailTrace_5749359 : CollatzResearch.WordTrace tailWord_5749359 prefixEnd_5749359 328020513583675148907965 := by
  unfold tailWord_5749359
  simp only [CollatzResearch.WordTrace]
  refine ⟨209696349978061730188275131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139797566652041153458850087 209696349978061730188275131)
  ·
    refine ⟨314544524967092595282412697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209696349978061730188275131 314544524967092595282412697)
    ·
      refine ⟨235908393725319446461809523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314544524967092595282412697 235908393725319446461809523)
      ·
        refine ⟨353862590587979169692714285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235908393725319446461809523 353862590587979169692714285)
        ·
          refine ⟨132698471470492188634767857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353862590587979169692714285 132698471470492188634767857)
          ·
            refine ⟨99523853602869141476075893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132698471470492188634767857 99523853602869141476075893)
            ·
              refine ⟨9330361275268982013382115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99523853602869141476075893 9330361275268982013382115)
              ·
                refine ⟨13995541912903473020073173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330361275268982013382115 13995541912903473020073173)
                ·
                  refine ⟨328020513583675148907965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13995541912903473020073173 328020513583675148907965)
                  ·
                    rfl

theorem cell23_5749359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 7].length) (baseStart_5749359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749359 prefixEnd_5749359 := by exact prefixLift 5749359
  have htrace : WordTrace (prefixWord ++ tailWord_5749359) baseStart_5749359 baseEnd_5749359 := by
    simpa [prefixWord, tailWord_5749359, baseEnd_5749359] using wordTrace_append hprefix tailTrace_5749359
  have hstable : (prefixWord ++ tailWord_5749359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749359).length < 2 ^ (prefixWord ++ tailWord_5749359).sum := by decide
  have hdescent : baseEnd_5749359 < baseStart_5749359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749399 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5749399 : Nat := 118140960795 + 5749399 * 2 ^ 59
def prefixEnd_5749399 : Nat := 4983230072969 + 3 ^ 40 * 5749399 * 2
def baseEnd_5749399 : Nat := 2952205161479256183671501

theorem tailTrace_5749399 : CollatzResearch.WordTrace tailWord_5749399 prefixEnd_5749399 2952205161479256183671501 := by
  unfold tailWord_5749399
  simp only [CollatzResearch.WordTrace]
  refine ⟨209697808897916817019731251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139798539265277878013154167 209697808897916817019731251)
  ·
    refine ⟨314546713346875225529596877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209697808897916817019731251 314546713346875225529596877)
    ·
      refine ⟨117955017505078209573598829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314546713346875225529596877 117955017505078209573598829)
      ·
        refine ⟨44233131564404328590099561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117955017505078209573598829 44233131564404328590099561)
        ·
          refine ⟨33174848673303246442574671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44233131564404328590099561 33174848673303246442574671)
          ·
            refine ⟨49762273009954869663862007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33174848673303246442574671 49762273009954869663862007)
            ·
              refine ⟨74643409514932304495793011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49762273009954869663862007 74643409514932304495793011)
              ·
                refine ⟨111965114272398456743689517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74643409514932304495793011 111965114272398456743689517)
                ·
                  refine ⟨41986917852149421278883569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111965114272398456743689517 41986917852149421278883569)
                  ·
                    refine ⟨31490188389112065959162677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41986917852149421278883569 31490188389112065959162677)
                    ·
                      refine ⟨2952205161479256183671501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31490188389112065959162677 2952205161479256183671501)
                      ·
                        rfl

theorem cell23_5749399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5749399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749399 prefixEnd_5749399 := by exact prefixLift 5749399
  have htrace : WordTrace (prefixWord ++ tailWord_5749399) baseStart_5749399 baseEnd_5749399 := by
    simpa [prefixWord, tailWord_5749399, baseEnd_5749399] using wordTrace_append hprefix tailTrace_5749399
  have hstable : (prefixWord ++ tailWord_5749399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749399).length < 2 ^ (prefixWord ++ tailWord_5749399).sum := by decide
  have hdescent : baseEnd_5749399 < baseStart_5749399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749503 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 2, 3, 2]
def baseStart_5749503 : Nat := 118140960795 + 5749503 * 2 ^ 59
def prefixEnd_5749503 : Nat := 4983230072969 + 3 ^ 40 * 5749503 * 2
def baseEnd_5749503 : Nat := 2952258563467323776771023

theorem tailTrace_5749503 : CollatzResearch.WordTrace tailWord_5749503 prefixEnd_5749503 2952258563467323776771023 := by
  unfold tailWord_5749503
  simp only [CollatzResearch.WordTrace]
  refine ⟨209701602089540042781517163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139801068059693361854344775 209701602089540042781517163)
  ·
    refine ⟨314552403134310064172275745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209701602089540042781517163 314552403134310064172275745)
    ·
      refine ⟨235914302350732548129206809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314552403134310064172275745 235914302350732548129206809)
      ·
        refine ⟨176935726763049411096905107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235914302350732548129206809 176935726763049411096905107)
        ·
          refine ⟨265403590144574116645357661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176935726763049411096905107 265403590144574116645357661)
          ·
            refine ⟨99526346304215293742009123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265403590144574116645357661 99526346304215293742009123)
            ·
              refine ⟨149289519456322940613013685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99526346304215293742009123 149289519456322940613013685)
              ·
                refine ⟨13995892449030275682470033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149289519456322940613013685 13995892449030275682470033)
                ·
                  refine ⟨10496919336772706761852525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13995892449030275682470033 10496919336772706761852525)
                  ·
                    refine ⟨3936344751289765035694697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10496919336772706761852525 3936344751289765035694697)
                    ·
                      refine ⟨2952258563467323776771023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936344751289765035694697 2952258563467323776771023)
                      ·
                        rfl

theorem cell23_5749503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_5749503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749503 prefixEnd_5749503 := by exact prefixLift 5749503
  have htrace : WordTrace (prefixWord ++ tailWord_5749503) baseStart_5749503 baseEnd_5749503 := by
    simpa [prefixWord, tailWord_5749503, baseEnd_5749503] using wordTrace_append hprefix tailTrace_5749503
  have hstable : (prefixWord ++ tailWord_5749503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749503).length < 2 ^ (prefixWord ++ tailWord_5749503).sum := by decide
  have hdescent : baseEnd_5749503 < baseStart_5749503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749516 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5749516 : Nat := 118140960795 + 5749516 * 2 ^ 59
def prefixEnd_5749516 : Nat := 4983230072969 + 3 ^ 40 * 5749516 * 2
def baseEnd_5749516 : Nat := 2952265238715832225908463

theorem tailTrace_5749516 : CollatzResearch.WordTrace tailWord_5749516 prefixEnd_5749516 2952265238715832225908463 := by
  unfold tailWord_5749516
  simp only [CollatzResearch.WordTrace]
  refine ⟨104851038119246473000870201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139801384158995297334493601 104851038119246473000870201)
  ·
    refine ⟨78638278589434854750652651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104851038119246473000870201 78638278589434854750652651)
    ·
      refine ⟨117957417884152282125978977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78638278589434854750652651 117957417884152282125978977)
      ·
        refine ⟨88468063413114211594484233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117957417884152282125978977 88468063413114211594484233)
        ·
          refine ⟨66351047559835658695863175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88468063413114211594484233 66351047559835658695863175)
          ·
            refine ⟨99526571339753488043794763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66351047559835658695863175 99526571339753488043794763)
            ·
              refine ⟨149289857009630232065692145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99526571339753488043794763 149289857009630232065692145)
              ·
                refine ⟨111967392757222674049269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149289857009630232065692145 111967392757222674049269109)
                ·
                  refine ⟨10496943070989625692118979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111967392757222674049269109 10496943070989625692118979)
                  ·
                    refine ⟨15745414606484438538178469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10496943070989625692118979 15745414606484438538178469)
                    ·
                      refine ⟨2952265238715832225908463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15745414606484438538178469 2952265238715832225908463)
                      ·
                        rfl

theorem cell23_5749516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5749516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749516 prefixEnd_5749516 := by exact prefixLift 5749516
  have htrace : WordTrace (prefixWord ++ tailWord_5749516) baseStart_5749516 baseEnd_5749516 := by
    simpa [prefixWord, tailWord_5749516, baseEnd_5749516] using wordTrace_append hprefix tailTrace_5749516
  have hstable : (prefixWord ++ tailWord_5749516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749516).length < 2 ^ (prefixWord ++ tailWord_5749516).sum := by decide
  have hdescent : baseEnd_5749516 < baseStart_5749516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749527 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5749527 : Nat := 118140960795 + 5749527 * 2 ^ 59
def prefixEnd_5749527 : Nat := 4983230072969 + 3 ^ 40 * 5749527 * 2
def baseEnd_5749527 : Nat := 2952270887003031682870913

theorem tailTrace_5749527 : CollatzResearch.WordTrace tailWord_5749527 prefixEnd_5749527 2952270887003031682870913 := by
  unfold tailWord_5749527
  simp only [CollatzResearch.WordTrace]
  refine ⟨209702477441453094880390835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139801651627635396586927223 209702477441453094880390835)
  ·
    refine ⟨314553716162179642320586253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209702477441453094880390835 314553716162179642320586253)
    ·
      refine ⟨117957643560817365870219845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314553716162179642320586253 117957643560817365870219845)
      ·
        refine ⟨22117058167653256100666221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117957643560817365870219845 22117058167653256100666221)
        ·
          refine ⟨8293896812869971037749833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22117058167653256100666221 8293896812869971037749833)
          ·
            refine ⟨6220422609652478278312375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293896812869971037749833 6220422609652478278312375)
            ·
              refine ⟨9330633914478717417468563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220422609652478278312375 9330633914478717417468563)
              ·
                refine ⟨13995950871718076126202845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330633914478717417468563 13995950871718076126202845)
                ·
                  refine ⟨5248481576894278547326067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13995950871718076126202845 5248481576894278547326067)
                  ·
                    refine ⟨7872722365341417820989101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248481576894278547326067 7872722365341417820989101)
                    ·
                      refine ⟨2952270887003031682870913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872722365341417820989101 2952270887003031682870913)
                      ·
                        rfl

theorem cell23_5749527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5749527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749527 prefixEnd_5749527 := by exact prefixLift 5749527
  have htrace : WordTrace (prefixWord ++ tailWord_5749527) baseStart_5749527 baseEnd_5749527 := by
    simpa [prefixWord, tailWord_5749527, baseEnd_5749527] using wordTrace_append hprefix tailTrace_5749527
  have hstable : (prefixWord ++ tailWord_5749527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749527).length < 2 ^ (prefixWord ++ tailWord_5749527).sum := by decide
  have hdescent : baseEnd_5749527 < baseStart_5749527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749550 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5749550 : Nat := 118140960795 + 5749550 * 2 ^ 59
def prefixEnd_5749550 : Nat := 4983230072969 + 3 ^ 40 * 5749550 * 2
def baseEnd_5749550 : Nat := 2952282697058085092883307

theorem tailTrace_5749550 : CollatzResearch.WordTrace tailWord_5749550 prefixEnd_5749550 2952282697058085092883307 := by
  unfold tailWord_5749550
  simp only [CollatzResearch.WordTrace]
  refine ⟨26212914540046221226059763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139802210880246513205652069 26212914540046221226059763)
  ·
    refine ⟨39319371810069331839089645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26212914540046221226059763 39319371810069331839089645)
    ·
      refine ⟨14744764428775999439658617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39319371810069331839089645 14744764428775999439658617)
      ·
        refine ⟨11058573321581999579743963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14744764428775999439658617 11058573321581999579743963)
        ·
          refine ⟨16587859982372999369615945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058573321581999579743963 16587859982372999369615945)
          ·
            refine ⟨12440894986779749527211959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16587859982372999369615945 12440894986779749527211959)
            ·
              refine ⟨18661342480169624290817939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12440894986779749527211959 18661342480169624290817939)
              ·
                refine ⟨27992013720254436436226909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661342480169624290817939 27992013720254436436226909)
                ·
                  refine ⟨10497005145095413663585091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27992013720254436436226909 10497005145095413663585091)
                  ·
                    refine ⟨15745507717643120495377637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10497005145095413663585091 15745507717643120495377637)
                    ·
                      refine ⟨2952282697058085092883307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15745507717643120495377637 2952282697058085092883307)
                      ·
                        rfl

theorem cell23_5749550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5749550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749550 prefixEnd_5749550 := by exact prefixLift 5749550
  have htrace : WordTrace (prefixWord ++ tailWord_5749550) baseStart_5749550 baseEnd_5749550 := by
    simpa [prefixWord, tailWord_5749550, baseEnd_5749550] using wordTrace_append hprefix tailTrace_5749550
  have hstable : (prefixWord ++ tailWord_5749550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749550).length < 2 ^ (prefixWord ++ tailWord_5749550).sum := by decide
  have hdescent : baseEnd_5749550 < baseStart_5749550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749553 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_5749553 : Nat := 118140960795 + 5749553 * 2 ^ 59
def prefixEnd_5749553 : Nat := 4983230072969 + 3 ^ 40 * 5749553 * 2
def baseEnd_5749553 : Nat := 2952284237500048581145793

theorem tailTrace_5749553 : CollatzResearch.WordTrace tailWord_5749553 prefixEnd_5749553 2952284237500048581145793 := by
  unfold tailWord_5749553
  simp only [CollatzResearch.WordTrace]
  refine ⟨209703425739358901320837313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139802283826239267547224875 209703425739358901320837313)
  ·
    refine ⟨157277569304519175990627985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209703425739358901320837313 157277569304519175990627985)
    ·
      refine ⟨117958176978389381992970989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157277569304519175990627985 117958176978389381992970989)
      ·
        refine ⟨44234316366896018247364121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117958176978389381992970989 44234316366896018247364121)
        ·
          refine ⟨33175737275172013685523091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44234316366896018247364121 33175737275172013685523091)
          ·
            refine ⟨49763605912758020528284637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33175737275172013685523091 49763605912758020528284637)
            ·
              refine ⟨18661352217284257698106739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49763605912758020528284637 18661352217284257698106739)
              ·
                refine ⟨27992028325926386547160109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661352217284257698106739 27992028325926386547160109)
                ·
                  refine ⟨10497010622222394955185041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27992028325926386547160109 10497010622222394955185041)
                  ·
                    refine ⟨7872757966666796216388781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10497010622222394955185041 7872757966666796216388781)
                    ·
                      refine ⟨2952284237500048581145793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872757966666796216388781 2952284237500048581145793)
                      ·
                        rfl

theorem cell23_5749553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_5749553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749553 prefixEnd_5749553 := by exact prefixLift 5749553
  have htrace : WordTrace (prefixWord ++ tailWord_5749553) baseStart_5749553 baseEnd_5749553 := by
    simpa [prefixWord, tailWord_5749553, baseEnd_5749553] using wordTrace_append hprefix tailTrace_5749553
  have hstable : (prefixWord ++ tailWord_5749553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749553).length < 2 ^ (prefixWord ++ tailWord_5749553).sum := by decide
  have hdescent : baseEnd_5749553 < baseStart_5749553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749584 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 1, 2, 2]
def baseStart_5749584 : Nat := 118140960795 + 5749584 * 2 ^ 59
def prefixEnd_5749584 : Nat := 4983230072969 + 3 ^ 40 * 5749584 * 2
def baseEnd_5749584 : Nat := 2952300155400337959858151

theorem tailTrace_5749584 : CollatzResearch.WordTrace tailWord_5749584 prefixEnd_5749584 2952300155400337959858151 := by
  unfold tailWord_5749584
  simp only [CollatzResearch.WordTrace]
  refine ⟨104852278201123296807607903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139803037601497729076810537 104852278201123296807607903)
  ·
    refine ⟨157278417301684945211411855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104852278201123296807607903 157278417301684945211411855)
    ·
      refine ⟨235917625952527417817117783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157278417301684945211411855 235917625952527417817117783)
      ·
        refine ⟨353876438928791126725676675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235917625952527417817117783 353876438928791126725676675)
        ·
          refine ⟨530814658393186690088515013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353876438928791126725676675 530814658393186690088515013)
          ·
            refine ⟨99527748448722504391596565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530814658393186690088515013 99527748448722504391596565)
            ·
              refine ⟨4665363208533867393356089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99527748448722504391596565 4665363208533867393356089)
              ·
                refine ⟨3499022406400400545017067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4665363208533867393356089 3499022406400400545017067)
                ·
                  refine ⟨5248533609600600817525601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499022406400400545017067 5248533609600600817525601)
                  ·
                    refine ⟨3936400207200450613144201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5248533609600600817525601 3936400207200450613144201)
                    ·
                      refine ⟨2952300155400337959858151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936400207200450613144201 2952300155400337959858151)
                      ·
                        rfl

theorem cell23_5749584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 2, 2].length) (baseStart_5749584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749584 prefixEnd_5749584 := by exact prefixLift 5749584
  have htrace : WordTrace (prefixWord ++ tailWord_5749584) baseStart_5749584 baseEnd_5749584 := by
    simpa [prefixWord, tailWord_5749584, baseEnd_5749584] using wordTrace_append hprefix tailTrace_5749584
  have hstable : (prefixWord ++ tailWord_5749584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749584).length < 2 ^ (prefixWord ++ tailWord_5749584).sum := by decide
  have hdescent : baseEnd_5749584 < baseStart_5749584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749586 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_5749586 : Nat := 118140960795 + 5749586 * 2 ^ 59
def prefixEnd_5749586 : Nat := 4983230072969 + 3 ^ 40 * 5749586 * 2
def baseEnd_5749586 : Nat := 984100394120548984011047

theorem tailTrace_5749586 : CollatzResearch.WordTrace tailWord_5749586 prefixEnd_5749586 984100394120548984011047 := by
  unfold tailWord_5749586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52426157337059836989197153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139803086232159565304525741 52426157337059836989197153)
  ·
    refine ⟨39319618002794877741897865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52426157337059836989197153 39319618002794877741897865)
    ·
      refine ⟨29489713502096158306423399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39319618002794877741897865 29489713502096158306423399)
      ·
        refine ⟨44234570253144237459635099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29489713502096158306423399 44234570253144237459635099)
        ·
          refine ⟨66351855379716356189452649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44234570253144237459635099 66351855379716356189452649)
          ·
            refine ⟨49763891534787267142089487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66351855379716356189452649 49763891534787267142089487)
            ·
              refine ⟨74645837302180900713134231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49763891534787267142089487 74645837302180900713134231)
              ·
                refine ⟨111968755953271351069701347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74645837302180900713134231 111968755953271351069701347)
                ·
                  refine ⟨167953133929907026604552021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111968755953271351069701347 167953133929907026604552021)
                  ·
                    refine ⟨984100394120548984011047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167953133929907026604552021 984100394120548984011047)
                    ·
                      rfl

theorem cell23_5749586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_5749586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749586 prefixEnd_5749586 := by exact prefixLift 5749586
  have htrace : WordTrace (prefixWord ++ tailWord_5749586) baseStart_5749586 baseEnd_5749586 := by
    simpa [prefixWord, tailWord_5749586, baseEnd_5749586] using wordTrace_append hprefix tailTrace_5749586
  have hstable : (prefixWord ++ tailWord_5749586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749586).length < 2 ^ (prefixWord ++ tailWord_5749586).sum := by decide
  have hdescent : baseEnd_5749586 < baseStart_5749586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749600 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_5749600 : Nat := 118140960795 + 5749600 * 2 ^ 59
def prefixEnd_5749600 : Nat := 4983230072969 + 3 ^ 40 * 5749600 * 2
def baseEnd_5749600 : Nat := 2952308371090809897258077

theorem tailTrace_5749600 : CollatzResearch.WordTrace tailWord_5749600 prefixEnd_5749600 2952308371090809897258077 := by
  unfold tailWord_5749600
  simp only [CollatzResearch.WordTrace]
  refine ⟨104852569985094314173899127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139803426646792418898532169 104852569985094314173899127)
  ·
    refine ⟨157278854977641471260848691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104852569985094314173899127 157278854977641471260848691)
    ·
      refine ⟨235918282466462206891273037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157278854977641471260848691 235918282466462206891273037)
      ·
        refine ⟨88469355924923327584227389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235918282466462206891273037 88469355924923327584227389)
        ·
          refine ⟨33176008471846247844085271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88469355924923327584227389 33176008471846247844085271)
          ·
            refine ⟨49764012707769371766127907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33176008471846247844085271 49764012707769371766127907)
            ·
              refine ⟨74646019061654057649191861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49764012707769371766127907 74646019061654057649191861)
              ·
                refine ⟨6998064287030067904611737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74646019061654057649191861 6998064287030067904611737)
                ·
                  refine ⟨5248548215272550928458803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998064287030067904611737 5248548215272550928458803)
                  ·
                    refine ⟨7872822322908826392688205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248548215272550928458803 7872822322908826392688205)
                    ·
                      refine ⟨2952308371090809897258077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872822322908826392688205 2952308371090809897258077)
                      ·
                        rfl

theorem cell23_5749600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_5749600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749600 prefixEnd_5749600 := by exact prefixLift 5749600
  have htrace : WordTrace (prefixWord ++ tailWord_5749600) baseStart_5749600 baseEnd_5749600 := by
    simpa [prefixWord, tailWord_5749600, baseEnd_5749600] using wordTrace_append hprefix tailTrace_5749600
  have hstable : (prefixWord ++ tailWord_5749600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749600).length < 2 ^ (prefixWord ++ tailWord_5749600).sum := by decide
  have hdescent : baseEnd_5749600 < baseStart_5749600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749626 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5749626 : Nat := 118140960795 + 5749626 * 2 ^ 59
def prefixEnd_5749626 : Nat := 4983230072969 + 3 ^ 40 * 5749626 * 2
def baseEnd_5749626 : Nat := 2952321721587826795532957

theorem tailTrace_5749626 : CollatzResearch.WordTrace tailWord_5749626 prefixEnd_5749626 2952321721587826795532957 := by
  unfold tailWord_5749626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52426522067023608697061183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139804058845396289858829821 52426522067023608697061183)
  ·
    refine ⟨78639783100535413045591775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52426522067023608697061183 78639783100535413045591775)
    ·
      refine ⟨117959674650803119568387663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78639783100535413045591775 117959674650803119568387663)
      ·
        refine ⟨176939511976204679352581495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117959674650803119568387663 176939511976204679352581495)
        ·
          refine ⟨265409267964307019028872243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176939511976204679352581495 265409267964307019028872243)
          ·
            refine ⟨398113901946460528543308365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265409267964307019028872243 398113901946460528543308365)
            ·
              refine ⟨149292713229922698203740637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398113901946460528543308365 149292713229922698203740637)
              ·
                refine ⟨55984767461221011826402739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149292713229922698203740637 55984767461221011826402739)
                ·
                  refine ⟨83977151191831517739604109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55984767461221011826402739 83977151191831517739604109)
                  ·
                    refine ⟨31491431696936819152351541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83977151191831517739604109 31491431696936819152351541)
                    ·
                      refine ⟨2952321721587826795532957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31491431696936819152351541 2952321721587826795532957)
                      ·
                        rfl

theorem cell23_5749626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5749626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749626 prefixEnd_5749626 := by exact prefixLift 5749626
  have htrace : WordTrace (prefixWord ++ tailWord_5749626) baseStart_5749626 baseEnd_5749626 := by
    simpa [prefixWord, tailWord_5749626, baseEnd_5749626] using wordTrace_append hprefix tailTrace_5749626
  have hstable : (prefixWord ++ tailWord_5749626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749626).length < 2 ^ (prefixWord ++ tailWord_5749626).sum := by decide
  have hdescent : baseEnd_5749626 < baseStart_5749626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749627 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 1, 3, 2]
def baseStart_5749627 : Nat := 118140960795 + 5749627 * 2 ^ 59
def prefixEnd_5749627 : Nat := 4983230072969 + 3 ^ 40 * 5749627 * 2
def baseEnd_5749627 : Nat := 2952322235068481291620453

theorem tailTrace_5749627 : CollatzResearch.WordTrace tailWord_5749627 prefixEnd_5749627 2952322235068481291620453 := by
  unfold tailWord_5749627
  simp only [CollatzResearch.WordTrace]
  refine ⟨209706124741090811959031135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139804083160727207972687423 209706124741090811959031135)
  ·
    refine ⟨314559187111636217938546703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209706124741090811959031135 314559187111636217938546703)
    ·
      refine ⟨471838780667454326907820055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314559187111636217938546703 471838780667454326907820055)
      ·
        refine ⟨707758171001181490361730083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471838780667454326907820055 707758171001181490361730083)
        ·
          refine ⟨1061637256501772235542595125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707758171001181490361730083 1061637256501772235542595125)
          ·
            refine ⟨99528492797041147082118293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1061637256501772235542595125 99528492797041147082118293)
            ·
              refine ⟨4665398099861303769474295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99528492797041147082118293 4665398099861303769474295)
              ·
                refine ⟨6998097149791955654211443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665398099861303769474295 6998097149791955654211443)
                ·
                  refine ⟨10497145724687933481317165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998097149791955654211443 10497145724687933481317165)
                  ·
                    refine ⟨3936429646757975055493937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10497145724687933481317165 3936429646757975055493937)
                    ·
                      refine ⟨2952322235068481291620453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936429646757975055493937 2952322235068481291620453)
                      ·
                        rfl

theorem cell23_5749627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 3, 2].length) (baseStart_5749627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749627 prefixEnd_5749627 := by exact prefixLift 5749627
  have htrace : WordTrace (prefixWord ++ tailWord_5749627) baseStart_5749627 baseEnd_5749627 := by
    simpa [prefixWord, tailWord_5749627, baseEnd_5749627] using wordTrace_append hprefix tailTrace_5749627
  have hstable : (prefixWord ++ tailWord_5749627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749627).length < 2 ^ (prefixWord ++ tailWord_5749627).sum := by decide
  have hdescent : baseEnd_5749627 < baseStart_5749627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749653 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_5749653 : Nat := 118140960795 + 5749653 * 2 ^ 59
def prefixEnd_5749653 : Nat := 4983230072969 + 3 ^ 40 * 5749653 * 2
def baseEnd_5749653 : Nat := 2952335585565498189895333

theorem tailTrace_5749653 : CollatzResearch.WordTrace tailWord_5749653 prefixEnd_5749653 2952335585565498189895333 := by
  unfold tailWord_5749653
  simp only [CollatzResearch.WordTrace]
  refine ⟨209707073038996618399477613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139804715359331078932985075 209707073038996618399477613)
  ·
    refine ⟨78640152389623731899804105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209707073038996618399477613 78640152389623731899804105)
    ·
      refine ⟨58980114292217798924853079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78640152389623731899804105 58980114292217798924853079)
      ·
        refine ⟨88470171438326698387279619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58980114292217798924853079 88470171438326698387279619)
        ·
          refine ⟨132705257157490047580919429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88470171438326698387279619 132705257157490047580919429)
          ·
            refine ⟨24882235717029383921422393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132705257157490047580919429 24882235717029383921422393)
            ·
              refine ⟨18661676787772037941066795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24882235717029383921422393 18661676787772037941066795)
              ·
                refine ⟨27992515181658056911600193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661676787772037941066795 27992515181658056911600193)
                ·
                  refine ⟨20994386386243542683700145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27992515181658056911600193 20994386386243542683700145)
                  ·
                    refine ⟨15745789789682657012775109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20994386386243542683700145 15745789789682657012775109)
                    ·
                      refine ⟨2952335585565498189895333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15745789789682657012775109 2952335585565498189895333)
                      ·
                        rfl

theorem cell23_5749653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_5749653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749653 prefixEnd_5749653 := by exact prefixLift 5749653
  have htrace : WordTrace (prefixWord ++ tailWord_5749653) baseStart_5749653 baseEnd_5749653 := by
    simpa [prefixWord, tailWord_5749653, baseEnd_5749653] using wordTrace_append hprefix tailTrace_5749653
  have hstable : (prefixWord ++ tailWord_5749653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749653).length < 2 ^ (prefixWord ++ tailWord_5749653).sum := by decide
  have hdescent : baseEnd_5749653 < baseStart_5749653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749663 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 7]
def baseStart_5749663 : Nat := 118140960795 + 5749663 * 2 ^ 59
def prefixEnd_5749663 : Nat := 4983230072969 + 3 ^ 40 * 5749663 * 2
def baseEnd_5749663 : Nat := 328037857819115905641143

theorem tailTrace_5749663 : CollatzResearch.WordTrace tailWord_5749663 prefixEnd_5749663 328037857819115905641143 := by
  unfold tailWord_5749663
  simp only [CollatzResearch.WordTrace]
  refine ⟨209707437768960390107341643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139804958512640260071561095 209707437768960390107341643)
  ·
    refine ⟨314561156653440585161012465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209707437768960390107341643 314561156653440585161012465)
    ·
      refine ⟨235920867490080438870759349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314561156653440585161012465 235920867490080438870759349)
      ·
        refine ⟨22117581327195041144133689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235920867490080438870759349 22117581327195041144133689)
        ·
          refine ⟨16588185995396280858100267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22117581327195041144133689 16588185995396280858100267)
          ·
            refine ⟨24882278993094421287150401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588185995396280858100267 24882278993094421287150401)
            ·
              refine ⟨18661709244820815965362801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24882278993094421287150401 18661709244820815965362801)
              ·
                refine ⟨13996281933615611974022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18661709244820815965362801 13996281933615611974022101)
                ·
                  refine ⟨328037857819115905641143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13996281933615611974022101 328037857819115905641143)
                  ·
                    rfl

theorem cell23_5749663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 7].length) (baseStart_5749663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749663 prefixEnd_5749663 := by exact prefixLift 5749663
  have htrace : WordTrace (prefixWord ++ tailWord_5749663) baseStart_5749663 baseEnd_5749663 := by
    simpa [prefixWord, tailWord_5749663, baseEnd_5749663] using wordTrace_append hprefix tailTrace_5749663
  have hstable : (prefixWord ++ tailWord_5749663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749663).length < 2 ^ (prefixWord ++ tailWord_5749663).sum := by decide
  have hdescent : baseEnd_5749663 < baseStart_5749663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749677 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5749677 : Nat := 118140960795 + 5749677 * 2 ^ 59
def prefixEnd_5749677 : Nat := 4983230072969 + 3 ^ 40 * 5749677 * 2
def baseEnd_5749677 : Nat := 2952347909101206095995223

theorem tailTrace_5749677 : CollatzResearch.WordTrace tailWord_5749677 prefixEnd_5749677 2952347909101206095995223 := by
  unfold tailWord_5749677
  simp only [CollatzResearch.WordTrace]
  refine ⟨209707948390909670498351285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139805298927273113665567523 209707948390909670498351285)
  ·
    refine ⟨19660120161647781609220433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209707948390909670498351285 19660120161647781609220433)
    ·
      refine ⟨14745090121235836206915325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19660120161647781609220433 14745090121235836206915325)
      ·
        refine ⟨5529408795463438577593247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14745090121235836206915325 5529408795463438577593247)
        ·
          refine ⟨8294113193195157866389871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529408795463438577593247 8294113193195157866389871)
          ·
            refine ⟨12441169789792736799584807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294113193195157866389871 12441169789792736799584807)
            ·
              refine ⟨18661754684689105199377211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441169789792736799584807 18661754684689105199377211)
              ·
                refine ⟨27992632027033657799065817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18661754684689105199377211 27992632027033657799065817)
                ·
                  refine ⟨20994474020275243349299363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27992632027033657799065817 20994474020275243349299363)
                  ·
                    refine ⟨31491711030412865023949045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20994474020275243349299363 31491711030412865023949045)
                    ·
                      refine ⟨2952347909101206095995223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31491711030412865023949045 2952347909101206095995223)
                      ·
                        rfl

theorem cell23_5749677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5749677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749677 prefixEnd_5749677 := by exact prefixLift 5749677
  have htrace : WordTrace (prefixWord ++ tailWord_5749677) baseStart_5749677 baseEnd_5749677 := by
    simpa [prefixWord, tailWord_5749677, baseEnd_5749677] using wordTrace_append hprefix tailTrace_5749677
  have hstable : (prefixWord ++ tailWord_5749677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749677).length < 2 ^ (prefixWord ++ tailWord_5749677).sum := by decide
  have hdescent : baseEnd_5749677 < baseStart_5749677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749702 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5749702 : Nat := 118140960795 + 5749702 * 2 ^ 59
def prefixEnd_5749702 : Nat := 4983230072969 + 3 ^ 40 * 5749702 * 2
def baseEnd_5749702 : Nat := 2952360746117568498182609

theorem tailTrace_5749702 : CollatzResearch.WordTrace tailWord_5749702 prefixEnd_5749702 2952360746117568498182609 := by
  unfold tailWord_5749702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553401881744346867750355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139805906810546066512007573 6553401881744346867750355)
  ·
    refine ⟨9830102822616520301625533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553401881744346867750355 9830102822616520301625533)
    ·
      refine ⟨3686288558481195113109575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9830102822616520301625533 3686288558481195113109575)
      ·
        refine ⟨5529432837721792669664363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686288558481195113109575 5529432837721792669664363)
        ·
          refine ⟨8294149256582689004496545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529432837721792669664363 8294149256582689004496545)
          ·
            refine ⟨6220611942437016753372409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294149256582689004496545 6220611942437016753372409)
            ·
              refine ⟨4665458956827762565029307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220611942437016753372409 4665458956827762565029307)
              ·
                refine ⟨6998188435241643847543961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665458956827762565029307 6998188435241643847543961)
                ·
                  refine ⟨5248641326431232885657971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998188435241643847543961 5248641326431232885657971)
                  ·
                    refine ⟨7872961989646849328486957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248641326431232885657971 7872961989646849328486957)
                    ·
                      refine ⟨2952360746117568498182609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7872961989646849328486957 2952360746117568498182609)
                      ·
                        rfl

theorem cell23_5749702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5749702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749702 prefixEnd_5749702 := by exact prefixLift 5749702
  have htrace : WordTrace (prefixWord ++ tailWord_5749702) baseStart_5749702 baseEnd_5749702 := by
    simpa [prefixWord, tailWord_5749702, baseEnd_5749702] using wordTrace_append hprefix tailTrace_5749702
  have hstable : (prefixWord ++ tailWord_5749702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749702).length < 2 ^ (prefixWord ++ tailWord_5749702).sum := by decide
  have hdescent : baseEnd_5749702 < baseStart_5749702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749713 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_5749713 : Nat := 118140960795 + 5749713 * 2 ^ 59
def prefixEnd_5749713 : Nat := 4983230072969 + 3 ^ 40 * 5749713 * 2
def baseEnd_5749713 : Nat := 2952366394404767955145057

theorem tailTrace_5749713 : CollatzResearch.WordTrace tailWord_5749713 prefixEnd_5749713 2952366394404767955145057 := by
  unfold tailWord_5749713
  simp only [CollatzResearch.WordTrace]
  refine ⟨209709261418779248646661793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139806174279186165764441195 209709261418779248646661793)
  ·
    refine ⟨157281946064084436484996345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209709261418779248646661793 157281946064084436484996345)
    ·
      refine ⟨117961459548063327363747259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157281946064084436484996345 117961459548063327363747259)
      ·
        refine ⟨176942189322094991045620889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117961459548063327363747259 176942189322094991045620889)
        ·
          refine ⟨132706641991571243284215667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176942189322094991045620889 132706641991571243284215667)
          ·
            refine ⟨199059962987356864926323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132706641991571243284215667 199059962987356864926323501)
            ·
              refine ⟨74647486120258824347371313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199059962987356864926323501 74647486120258824347371313)
              ·
                refine ⟨55985614590194118260528485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74647486120258824347371313 55985614590194118260528485)
                ·
                  refine ⟨10497302735661397173849091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55985614590194118260528485 10497302735661397173849091)
                  ·
                    refine ⟨15745954103492095760773637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10497302735661397173849091 15745954103492095760773637)
                    ·
                      refine ⟨2952366394404767955145057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15745954103492095760773637 2952366394404767955145057)
                      ·
                        rfl

theorem cell23_5749713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_5749713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749713 prefixEnd_5749713 := by exact prefixLift 5749713
  have htrace : WordTrace (prefixWord ++ tailWord_5749713) baseStart_5749713 baseEnd_5749713 := by
    simpa [prefixWord, tailWord_5749713, baseEnd_5749713] using wordTrace_append hprefix tailTrace_5749713
  have hstable : (prefixWord ++ tailWord_5749713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749713).length < 2 ^ (prefixWord ++ tailWord_5749713).sum := by decide
  have hdescent : baseEnd_5749713 < baseStart_5749713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749748 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5749748 : Nat := 118140960795 + 5749748 * 2 ^ 59
def prefixEnd_5749748 : Nat := 4983230072969 + 3 ^ 40 * 5749748 * 2
def baseEnd_5749748 : Nat := 328042707358630590911933

theorem tailTrace_5749748 : CollatzResearch.WordTrace tailWord_5749748 prefixEnd_5749748 328042707358630590911933 := by
  unfold tailWord_5749748
  simp only [CollatzResearch.WordTrace]
  refine ⟨104855268986826224812092949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139807025315768299749457265 104855268986826224812092949)
  ·
    refine ⟨4915090733757479288066857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104855268986826224812092949 4915090733757479288066857)
    ·
      refine ⟨3686318050318109466050143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915090733757479288066857 3686318050318109466050143)
      ·
        refine ⟨5529477075477164199075215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686318050318109466050143 5529477075477164199075215)
        ·
          refine ⟨8294215613215746298612823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529477075477164199075215 8294215613215746298612823)
          ·
            refine ⟨12441323419823619447919235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294215613215746298612823 12441323419823619447919235)
            ·
              refine ⟨18661985129735429171878853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441323419823619447919235 18661985129735429171878853)
              ·
                refine ⟨3499122211825392969727285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18661985129735429171878853 3499122211825392969727285)
                ·
                  refine ⟨328042707358630590911933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3499122211825392969727285 328042707358630590911933)
                  ·
                    rfl

theorem cell23_5749748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5749748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749748 prefixEnd_5749748 := by exact prefixLift 5749748
  have htrace : WordTrace (prefixWord ++ tailWord_5749748) baseStart_5749748 baseEnd_5749748 := by
    simpa [prefixWord, tailWord_5749748, baseEnd_5749748] using wordTrace_append hprefix tailTrace_5749748
  have hstable : (prefixWord ++ tailWord_5749748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749748).length < 2 ^ (prefixWord ++ tailWord_5749748).sum := by decide
  have hdescent : baseEnd_5749748 < baseStart_5749748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749763 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3]
def baseStart_5749763 : Nat := 118140960795 + 5749763 * 2 ^ 59
def prefixEnd_5749763 : Nat := 4983230072969 + 3 ^ 40 * 5749763 * 2
def baseEnd_5749763 : Nat := 2952392068437492759519827

theorem tailTrace_5749763 : CollatzResearch.WordTrace tailWord_5749763 prefixEnd_5749763 2952392068437492759519827 := by
  unfold tailWord_5749763
  simp only [CollatzResearch.WordTrace]
  refine ⟨209711085068598107185981943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139807390045732071457321295 209711085068598107185981943)
  ·
    refine ⟨314566627602897160778972915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209711085068598107185981943 314566627602897160778972915)
    ·
      refine ⟨471849941404345741168459373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314566627602897160778972915 471849941404345741168459373)
      ·
        refine ⟨176943728026629652938172265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471849941404345741168459373 176943728026629652938172265)
        ·
          refine ⟨132707796019972239703629199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176943728026629652938172265 132707796019972239703629199)
          ·
            refine ⟨199061694029958359555443799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132707796019972239703629199 199061694029958359555443799)
            ·
              refine ⟨298592541044937539333165699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199061694029958359555443799 298592541044937539333165699)
              ·
                refine ⟨447888811567406308999748549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298592541044937539333165699 447888811567406308999748549)
                ·
                  refine ⟨83979152168888682937452853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447888811567406308999748549 83979152168888682937452853)
                  ·
                    refine ⟨7873045515833314025386205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83979152168888682937452853 7873045515833314025386205)
                    ·
                      refine ⟨2952392068437492759519827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7873045515833314025386205 2952392068437492759519827)
                      ·
                        rfl

theorem cell23_5749763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_5749763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749763 prefixEnd_5749763 := by exact prefixLift 5749763
  have htrace : WordTrace (prefixWord ++ tailWord_5749763) baseStart_5749763 baseEnd_5749763 := by
    simpa [prefixWord, tailWord_5749763, baseEnd_5749763] using wordTrace_append hprefix tailTrace_5749763
  have hstable : (prefixWord ++ tailWord_5749763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749763).length < 2 ^ (prefixWord ++ tailWord_5749763).sum := by decide
  have hdescent : baseEnd_5749763 < baseStart_5749763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749770 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_5749770 : Nat := 118140960795 + 5749770 * 2 ^ 59
def prefixEnd_5749770 : Nat := 4983230072969 + 3 ^ 40 * 5749770 * 2
def baseEnd_5749770 : Nat := 328043962533563803570255

theorem tailTrace_5749770 : CollatzResearch.WordTrace tailWord_5749770 prefixEnd_5749770 328043962533563803570255 := by
  unfold tailWord_5749770
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427835094893186845371691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139807560253048498254324509 52427835094893186845371691)
  ·
    refine ⟨78641752642339780268057537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52427835094893186845371691 78641752642339780268057537)
    ·
      refine ⟨58981314481754835201043153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78641752642339780268057537 58981314481754835201043153)
      ·
        refine ⟨44235985861316126400782365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58981314481754835201043153 44235985861316126400782365)
        ·
          refine ⟨16588494697993547400293387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44235985861316126400782365 16588494697993547400293387)
          ·
            refine ⟨24882742046990321100440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588494697993547400293387 24882742046990321100440081)
            ·
              refine ⟨18662056535242740825330061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24882742046990321100440081 18662056535242740825330061)
              ·
                refine ⟨6998271200716027809498773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18662056535242740825330061 6998271200716027809498773)
                ·
                  refine ⟨328043962533563803570255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6998271200716027809498773 328043962533563803570255)
                  ·
                    rfl

theorem cell23_5749770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_5749770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749770 prefixEnd_5749770 := by exact prefixLift 5749770
  have htrace : WordTrace (prefixWord ++ tailWord_5749770) baseStart_5749770 baseEnd_5749770 := by
    simpa [prefixWord, tailWord_5749770, baseEnd_5749770] using wordTrace_append hprefix tailTrace_5749770
  have hstable : (prefixWord ++ tailWord_5749770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749770).length < 2 ^ (prefixWord ++ tailWord_5749770).sum := by decide
  have hdescent : baseEnd_5749770 < baseStart_5749770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749778 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5749778 : Nat := 118140960795 + 5749778 * 2 ^ 59
def prefixEnd_5749778 : Nat := 4983230072969 + 3 ^ 40 * 5749778 * 2
def baseEnd_5749778 : Nat := 984133256882436733610753

theorem tailTrace_5749778 : CollatzResearch.WordTrace tailWord_5749778 prefixEnd_5749778 984133256882436733610753 := by
  unfold tailWord_5749778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427908040885941186944497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139807754775695843165185325 52427908040885941186944497)
  ·
    refine ⟨39320931030664455890208373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52427908040885941186944497 39320931030664455890208373)
    ·
      refine ⟨3686337284124792739707035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39320931030664455890208373 3686337284124792739707035)
      ·
        refine ⟨5529505926187189109560553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686337284124792739707035 5529505926187189109560553)
        ·
          refine ⟨4147129444640391832170415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529505926187189109560553 4147129444640391832170415)
          ·
            refine ⟨6220694166960587748255623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147129444640391832170415 6220694166960587748255623)
            ·
              refine ⟨9331041250440881622383435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220694166960587748255623 9331041250440881622383435)
              ·
                refine ⟨13996561875661322433575153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331041250440881622383435 13996561875661322433575153)
                ·
                  refine ⟨10497421406745991825181365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13996561875661322433575153 10497421406745991825181365)
                  ·
                    refine ⟨984133256882436733610753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10497421406745991825181365 984133256882436733610753)
                    ·
                      rfl

theorem cell23_5749778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5749778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749778 prefixEnd_5749778 := by exact prefixLift 5749778
  have htrace : WordTrace (prefixWord ++ tailWord_5749778) baseStart_5749778 baseEnd_5749778 := by
    simpa [prefixWord, tailWord_5749778, baseEnd_5749778] using wordTrace_append hprefix tailTrace_5749778
  have hstable : (prefixWord ++ tailWord_5749778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749778).length < 2 ^ (prefixWord ++ tailWord_5749778).sum := by decide
  have hdescent : baseEnd_5749778 < baseStart_5749778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749814 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_5749814 : Nat := 118140960795 + 5749814 * 2 ^ 59
def prefixEnd_5749814 : Nat := 4983230072969 + 3 ^ 40 * 5749814 * 2
def baseEnd_5749814 : Nat := 2952418255950872059982093

theorem tailTrace_5749814 : CollatzResearch.WordTrace tailWord_5749814 prefixEnd_5749814 2952418255950872059982093 := by
  unfold tailWord_5749814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107059074463333931005531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139808630127608895264058997 13107059074463333931005531)
  ·
    refine ⟨19660588611695000896508297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107059074463333931005531 19660588611695000896508297)
    ·
      refine ⟨14745441458771250672381223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19660588611695000896508297 14745441458771250672381223)
      ·
        refine ⟨22118162188156876008571835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745441458771250672381223 22118162188156876008571835)
        ·
          refine ⟨33177243282235314012857753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22118162188156876008571835 33177243282235314012857753)
          ·
            refine ⟨24882932461676485509643315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33177243282235314012857753 24882932461676485509643315)
            ·
              refine ⟨37324398692514728264464973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24882932461676485509643315 37324398692514728264464973)
              ·
                refine ⟨13996649509693023099174365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37324398692514728264464973 13996649509693023099174365)
                ·
                  refine ⟨5248743566134883662190387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13996649509693023099174365 5248743566134883662190387)
                  ·
                    refine ⟨7873115349202325493285581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5248743566134883662190387 7873115349202325493285581)
                    ·
                      refine ⟨2952418255950872059982093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7873115349202325493285581 2952418255950872059982093)
                      ·
                        rfl

theorem cell23_5749814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_5749814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749814 prefixEnd_5749814 := by exact prefixLift 5749814
  have htrace : WordTrace (prefixWord ++ tailWord_5749814) baseStart_5749814 baseEnd_5749814 := by
    simpa [prefixWord, tailWord_5749814, baseEnd_5749814] using wordTrace_append hprefix tailTrace_5749814
  have hstable : (prefixWord ++ tailWord_5749814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749814).length < 2 ^ (prefixWord ++ tailWord_5749814).sum := by decide
  have hdescent : baseEnd_5749814 < baseStart_5749814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749840 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_5749840 : Nat := 118140960795 + 5749840 * 2 ^ 59
def prefixEnd_5749840 : Nat := 4983230072969 + 3 ^ 40 * 5749840 * 2
def baseEnd_5749840 : Nat := 2952431606447888958256973

theorem tailTrace_5749840 : CollatzResearch.WordTrace tailWord_5749840 prefixEnd_5749840 2952431606447888958256973 := by
  unfold tailWord_5749840
  simp only [CollatzResearch.WordTrace]
  refine ⟨104856946744659574668267487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139809262326212766224356649 104856946744659574668267487)
  ·
    refine ⟨157285420116989362002401231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104856946744659574668267487 157285420116989362002401231)
    ·
      refine ⟨235928130175484043003601847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157285420116989362002401231 235928130175484043003601847)
      ·
        refine ⟨353892195263226064505402771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235928130175484043003601847 353892195263226064505402771)
        ·
          refine ⟨530838292894839096758104157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353892195263226064505402771 530838292894839096758104157)
          ·
            refine ⟨199064359835564661284289059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530838292894839096758104157 199064359835564661284289059)
            ·
              refine ⟨298596539753346991926433589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199064359835564661284289059 298596539753346991926433589)
              ·
                refine ⟨27993425601876280493103149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298596539753346991926433589 27993425601876280493103149)
                ·
                  refine ⟨10497534600703605184913681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27993425601876280493103149 10497534600703605184913681)
                  ·
                    refine ⟨7873150950527703888685261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10497534600703605184913681 7873150950527703888685261)
                    ·
                      refine ⟨2952431606447888958256973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7873150950527703888685261 2952431606447888958256973)
                      ·
                        rfl

theorem cell23_5749840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_5749840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749840 prefixEnd_5749840 := by exact prefixLift 5749840
  have htrace : WordTrace (prefixWord ++ tailWord_5749840) baseStart_5749840 baseEnd_5749840 := by
    simpa [prefixWord, tailWord_5749840, baseEnd_5749840] using wordTrace_append hprefix tailTrace_5749840
  have hstable : (prefixWord ++ tailWord_5749840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749840).length < 2 ^ (prefixWord ++ tailWord_5749840).sum := by decide
  have hdescent : baseEnd_5749840 < baseStart_5749840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749857 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_5749857 : Nat := 118140960795 + 5749857 * 2 ^ 59
def prefixEnd_5749857 : Nat := 4983230072969 + 3 ^ 40 * 5749857 * 2
def baseEnd_5749857 : Nat := 2952440335619015391744395

theorem tailTrace_5749857 : CollatzResearch.WordTrace tailWord_5749857 prefixEnd_5749857 2952440335619015391744395 := by
  unfold tailWord_5749857
  simp only [CollatzResearch.WordTrace]
  refine ⟨209714513530257561239903825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139809675686838374159935883 209714513530257561239903825)
  ·
    refine ⟨157285885147693170929927869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209714513530257561239903825 157285885147693170929927869)
    ·
      refine ⟨58982206930384939098722951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157285885147693170929927869 58982206930384939098722951)
      ·
        refine ⟨88473310395577408648084427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58982206930384939098722951 88473310395577408648084427)
        ·
          refine ⟨132709965593366112972126641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88473310395577408648084427 132709965593366112972126641)
          ·
            refine ⟨99532474195024584729094981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132709965593366112972126641 99532474195024584729094981)
            ·
              refine ⟨18662338911567109636705309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99532474195024584729094981 18662338911567109636705309)
              ·
                refine ⟨6998377091837666113764491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18662338911567109636705309 6998377091837666113764491)
                ·
                  refine ⟨10497565637756499170646737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998377091837666113764491 10497565637756499170646737)
                  ·
                    refine ⟨7873174228317374377985053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10497565637756499170646737 7873174228317374377985053)
                    ·
                      refine ⟨2952440335619015391744395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7873174228317374377985053 2952440335619015391744395)
                      ·
                        rfl

theorem cell23_5749857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_5749857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749857 prefixEnd_5749857 := by exact prefixLift 5749857
  have htrace : WordTrace (prefixWord ++ tailWord_5749857) baseStart_5749857 baseEnd_5749857 := by
    simpa [prefixWord, tailWord_5749857, baseEnd_5749857] using wordTrace_append hprefix tailTrace_5749857
  have hstable : (prefixWord ++ tailWord_5749857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749857).length < 2 ^ (prefixWord ++ tailWord_5749857).sum := by decide
  have hdescent : baseEnd_5749857 < baseStart_5749857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749881 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_5749881 : Nat := 118140960795 + 5749881 * 2 ^ 59
def prefixEnd_5749881 : Nat := 4983230072969 + 3 ^ 40 * 5749881 * 2
def baseEnd_5749881 : Nat := 984150886384907765948095

theorem tailTrace_5749881 : CollatzResearch.WordTrace tailWord_5749881 prefixEnd_5749881 984150886384907765948095 := by
  unfold tailWord_5749881
  simp only [CollatzResearch.WordTrace]
  refine ⟨209715388882170613338777497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139810259254780408892518331 209715388882170613338777497)
  ·
    refine ⟨157286541661627960004083123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209715388882170613338777497 157286541661627960004083123)
    ·
      refine ⟨235929812492441940006124685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157286541661627960004083123 235929812492441940006124685)
      ·
        refine ⟨88473679684665727502296757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235929812492441940006124685 88473679684665727502296757)
        ·
          refine ⟨8294407470437411953340321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88473679684665727502296757 8294407470437411953340321)
          ·
            refine ⟨6220805602828058965005241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294407470437411953340321 6220805602828058965005241)
            ·
              refine ⟨4665604202121044223753931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220805602828058965005241 4665604202121044223753931)
              ·
                refine ⟨6998406303181566335630897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665604202121044223753931 6998406303181566335630897)
                ·
                  refine ⟨5248804727386174751723173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998406303181566335630897 5248804727386174751723173)
                  ·
                    refine ⟨984150886384907765948095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248804727386174751723173 984150886384907765948095)
                    ·
                      rfl

theorem cell23_5749881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_5749881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749881 prefixEnd_5749881 := by exact prefixLift 5749881
  have htrace : WordTrace (prefixWord ++ tailWord_5749881) baseStart_5749881 baseEnd_5749881 := by
    simpa [prefixWord, tailWord_5749881, baseEnd_5749881] using wordTrace_append hprefix tailTrace_5749881
  have hstable : (prefixWord ++ tailWord_5749881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749881).length < 2 ^ (prefixWord ++ tailWord_5749881).sum := by decide
  have hdescent : baseEnd_5749881 < baseStart_5749881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749920 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_5749920 : Nat := 118140960795 + 5749920 * 2 ^ 59
def prefixEnd_5749920 : Nat := 4983230072969 + 3 ^ 40 * 5749920 * 2
def baseEnd_5749920 : Nat := 984157561633416215085535

theorem tailTrace_5749920 : CollatzResearch.WordTrace tailWord_5749920 prefixEnd_5749920 984157561633416215085535 := by
  unfold tailWord_5749920
  simp only [CollatzResearch.WordTrace]
  refine ⟨104858405664514661499723607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139811207552686215332964809 104858405664514661499723607)
  ·
    refine ⟨157287608496771992249585411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104858405664514661499723607 157287608496771992249585411)
    ·
      refine ⟨235931412745157988374378117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157287608496771992249585411 235931412745157988374378117)
      ·
        refine ⟨44237139889717122820195897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235931412745157988374378117 44237139889717122820195897)
        ·
          refine ⟨33177854917287842115146923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44237139889717122820195897 33177854917287842115146923)
          ·
            refine ⟨49766782375931763172720385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33177854917287842115146923 49766782375931763172720385)
            ·
              refine ⟨37325086781948822379540289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49766782375931763172720385 37325086781948822379540289)
              ·
                refine ⟨27993815086461616784655217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37325086781948822379540289 27993815086461616784655217)
                ·
                  refine ⟨20995361314846212588491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27993815086461616784655217 20995361314846212588491413)
                  ·
                    refine ⟨984157561633416215085535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20995361314846212588491413 984157561633416215085535)
                    ·
                      rfl

theorem cell23_5749920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_5749920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749920 prefixEnd_5749920 := by exact prefixLift 5749920
  have htrace : WordTrace (prefixWord ++ tailWord_5749920) baseStart_5749920 baseEnd_5749920 := by
    simpa [prefixWord, tailWord_5749920, baseEnd_5749920] using wordTrace_append hprefix tailTrace_5749920
  have hstable : (prefixWord ++ tailWord_5749920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749920).length < 2 ^ (prefixWord ++ tailWord_5749920).sum := by decide
  have hdescent : baseEnd_5749920 < baseStart_5749920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749922 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5749922 : Nat := 118140960795 + 5749922 * 2 ^ 59
def prefixEnd_5749922 : Nat := 4983230072969 + 3 ^ 40 * 5749922 * 2
def baseEnd_5749922 : Nat := 2952473711861557637431597

theorem tailTrace_5749922 : CollatzResearch.WordTrace tailWord_5749922 prefixEnd_5749922 2952473711861557637431597 := by
  unfold tailWord_5749922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52429221068755519335255005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139811256183348051560680013 52429221068755519335255005)
  ·
    refine ⟨19660957900783319750720627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52429221068755519335255005 19660957900783319750720627)
    ·
      refine ⟨29491436851174979626080941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19660957900783319750720627 29491436851174979626080941)
      ·
        refine ⟨11059288819190617359780353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29491436851174979626080941 11059288819190617359780353)
        ·
          refine ⟨8294466614392963019835265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11059288819190617359780353 8294466614392963019835265)
          ·
            refine ⟨6220849960794722264876449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294466614392963019835265 6220849960794722264876449)
            ·
              refine ⟨4665637470596041698657337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6220849960794722264876449 4665637470596041698657337)
              ·
                refine ⟨3499228102947031273993003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4665637470596041698657337 3499228102947031273993003)
                ·
                  refine ⟨5248842154420546910989505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499228102947031273993003 5248842154420546910989505)
                  ·
                    refine ⟨3936631615815410183242129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5248842154420546910989505 3936631615815410183242129)
                    ·
                      refine ⟨2952473711861557637431597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936631615815410183242129 2952473711861557637431597)
                      ·
                        rfl

theorem cell23_5749922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5749922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749922 prefixEnd_5749922 := by exact prefixLift 5749922
  have htrace : WordTrace (prefixWord ++ tailWord_5749922) baseStart_5749922 baseEnd_5749922 := by
    simpa [prefixWord, tailWord_5749922, baseEnd_5749922] using wordTrace_append hprefix tailTrace_5749922
  have hstable : (prefixWord ++ tailWord_5749922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749922).length < 2 ^ (prefixWord ++ tailWord_5749922).sum := by decide
  have hdescent : baseEnd_5749922 < baseStart_5749922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749927 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5749927 : Nat := 118140960795 + 5749927 * 2 ^ 59
def prefixEnd_5749927 : Nat := 4983230072969 + 3 ^ 40 * 5749927 * 2
def baseEnd_5749927 : Nat := 2952476279264830117869073

theorem tailTrace_5749927 : CollatzResearch.WordTrace tailWord_5749927 prefixEnd_5749927 2952476279264830117869073 := by
  unfold tailWord_5749927
  simp only [CollatzResearch.WordTrace]
  refine ⟨209717066640003963194952035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139811377760002642129968023 209717066640003963194952035)
  ·
    refine ⟨314575599960005944792428053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209717066640003963194952035 314575599960005944792428053)
    ·
      refine ⟨14745731248125278662145065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314575599960005944792428053 14745731248125278662145065)
      ·
        refine ⟨11059298436093958996608799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14745731248125278662145065 11059298436093958996608799)
        ·
          refine ⟨16588947654140938494913199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11059298436093958996608799 16588947654140938494913199)
          ·
            refine ⟨24883421481211407742369799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16588947654140938494913199 24883421481211407742369799)
            ·
              refine ⟨37325132221817111613554699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24883421481211407742369799 37325132221817111613554699)
              ·
                refine ⟨55987698332725667420332049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37325132221817111613554699 55987698332725667420332049)
                ·
                  refine ⟨41990773749544250565249037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55987698332725667420332049 41990773749544250565249037)
                  ·
                    refine ⟨15746540156079093961968389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41990773749544250565249037 15746540156079093961968389)
                    ·
                      refine ⟨2952476279264830117869073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15746540156079093961968389 2952476279264830117869073)
                      ·
                        rfl

theorem cell23_5749927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5749927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749927 prefixEnd_5749927 := by exact prefixLift 5749927
  have htrace : WordTrace (prefixWord ++ tailWord_5749927) baseStart_5749927 baseEnd_5749927 := by
    simpa [prefixWord, tailWord_5749927, baseEnd_5749927] using wordTrace_append hprefix tailTrace_5749927
  have hstable : (prefixWord ++ tailWord_5749927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749927).length < 2 ^ (prefixWord ++ tailWord_5749927).sum := by decide
  have hdescent : baseEnd_5749927 < baseStart_5749927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749937 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_5749937 : Nat := 118140960795 + 5749937 * 2 ^ 59
def prefixEnd_5749937 : Nat := 4983230072969 + 3 ^ 40 * 5749937 * 2
def baseEnd_5749937 : Nat := 984160471357125026248009

theorem tailTrace_5749937 : CollatzResearch.WordTrace tailWord_5749937 prefixEnd_5749937 984160471357125026248009 := by
  unfold tailWord_5749937
  simp only [CollatzResearch.WordTrace]
  refine ⟨209717431369967734902816065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139811620913311823268544043 209717431369967734902816065)
  ·
    refine ⟨157288073527475801177112049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209717431369967734902816065 157288073527475801177112049)
    ·
      refine ⟨117966055145606850882834037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157288073527475801177112049 117966055145606850882834037)
      ·
        refine ⟨11059317669900642270265691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117966055145606850882834037 11059317669900642270265691)
        ·
          refine ⟨16588976504850963405398537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11059317669900642270265691 16588976504850963405398537)
          ·
            refine ⟨12441732378638222554048903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16588976504850963405398537 12441732378638222554048903)
            ·
              refine ⟨18662598567957333831073355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441732378638222554048903 18662598567957333831073355)
              ·
                refine ⟨27993897851936000746610033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18662598567957333831073355 27993897851936000746610033)
                ·
                  refine ⟨20995423388952000559957525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27993897851936000746610033 20995423388952000559957525)
                  ·
                    refine ⟨984160471357125026248009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20995423388952000559957525 984160471357125026248009)
                    ·
                      rfl

theorem cell23_5749937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_5749937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749937 prefixEnd_5749937 := by exact prefixLift 5749937
  have htrace : WordTrace (prefixWord ++ tailWord_5749937) baseStart_5749937 baseEnd_5749937 := by
    simpa [prefixWord, tailWord_5749937, baseEnd_5749937] using wordTrace_append hprefix tailTrace_5749937
  have hstable : (prefixWord ++ tailWord_5749937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749937).length < 2 ^ (prefixWord ++ tailWord_5749937).sum := by decide
  have hdescent : baseEnd_5749937 < baseStart_5749937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749965 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5749965 : Nat := 118140960795 + 5749965 * 2 ^ 59
def prefixEnd_5749965 : Nat := 4983230072969 + 3 ^ 40 * 5749965 * 2
def baseEnd_5749965 : Nat := 2952495791529700969193899

theorem tailTrace_5749965 : CollatzResearch.WordTrace tailWord_5749965 prefixEnd_5749965 2952495791529700969193899 := by
  unfold tailWord_5749965
  simp only [CollatzResearch.WordTrace]
  refine ⟨209718452613866295684835349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139812301742577530456556899 209718452613866295684835349)
  ·
    refine ⟨9830552466274982610226657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209718452613866295684835349 9830552466274982610226657)
    ·
      refine ⟨7372914349706236957669993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9830552466274982610226657 7372914349706236957669993)
      ·
        refine ⟨5529685762279677718252495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7372914349706236957669993 5529685762279677718252495)
        ·
          refine ⟨8294528643419516577378743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529685762279677718252495 8294528643419516577378743)
          ·
            refine ⟨12441792965129274866068115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294528643419516577378743 12441792965129274866068115)
            ·
              refine ⟨18662689447693912299102173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441792965129274866068115 18662689447693912299102173)
              ·
                refine ⟨6998508542885217112163315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18662689447693912299102173 6998508542885217112163315)
                ·
                  refine ⟨10497762814327825668244973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998508542885217112163315 10497762814327825668244973)
                  ·
                    refine ⟨3936661055372934625591865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10497762814327825668244973 3936661055372934625591865)
                    ·
                      refine ⟨2952495791529700969193899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936661055372934625591865 2952495791529700969193899)
                      ·
                        rfl

theorem cell23_5749965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5749965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749965 prefixEnd_5749965 := by exact prefixLift 5749965
  have htrace : WordTrace (prefixWord ++ tailWord_5749965) baseStart_5749965 baseEnd_5749965 := by
    simpa [prefixWord, tailWord_5749965, baseEnd_5749965] using wordTrace_append hprefix tailTrace_5749965
  have hstable : (prefixWord ++ tailWord_5749965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749965).length < 2 ^ (prefixWord ++ tailWord_5749965).sum := by decide
  have hdescent : baseEnd_5749965 < baseStart_5749965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5749997 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_5749997 : Nat := 118140960795 + 5749997 * 2 ^ 59
def prefixEnd_5749997 : Nat := 4983230072969 + 3 ^ 40 * 5749997 * 2
def baseEnd_5749997 : Nat := 984170740970214947997917

theorem tailTrace_5749997 : CollatzResearch.WordTrace tailWord_5749997 prefixEnd_5749997 984170740970214947997917 := by
  unfold tailWord_5749997
  simp only [CollatzResearch.WordTrace]
  refine ⟨209719619749750365150000245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139813079833166910100000163 209719619749750365150000245)
  ·
    refine ⟨19661214351539096732812523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209719619749750365150000245 19661214351539096732812523)
    ·
      refine ⟨29491821527308645099218785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661214351539096732812523 29491821527308645099218785)
      ·
        refine ⟨22118866145481483824414089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29491821527308645099218785 22118866145481483824414089)
        ·
          refine ⟨16589149609111112868310567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22118866145481483824414089 16589149609111112868310567)
          ·
            refine ⟨24883724413666669302465851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16589149609111112868310567 24883724413666669302465851)
            ·
              refine ⟨37325586620500003953698777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24883724413666669302465851 37325586620500003953698777)
              ·
                refine ⟨27994189965375002965274083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37325586620500003953698777 27994189965375002965274083)
                ·
                  refine ⟨41991284948062504447911125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27994189965375002965274083 41991284948062504447911125)
                  ·
                    refine ⟨984170740970214947997917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41991284948062504447911125 984170740970214947997917)
                    ·
                      rfl

theorem cell23_5749997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_5749997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5749997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5749997 prefixEnd_5749997 := by exact prefixLift 5749997
  have htrace : WordTrace (prefixWord ++ tailWord_5749997) baseStart_5749997 baseEnd_5749997 := by
    simpa [prefixWord, tailWord_5749997, baseEnd_5749997] using wordTrace_append hprefix tailTrace_5749997
  have hstable : (prefixWord ++ tailWord_5749997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5749997).length < 2 ^ (prefixWord ++ tailWord_5749997).sum := by decide
  have hdescent : baseEnd_5749997 < baseStart_5749997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5749997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750010 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_5750010 : Nat := 118140960795 + 5750010 * 2 ^ 59
def prefixEnd_5750010 : Nat := 4983230072969 + 3 ^ 40 * 5750010 * 2
def baseEnd_5750010 : Nat := 984172966053051097710397

theorem tailTrace_5750010 : CollatzResearch.WordTrace tailWord_5750010 prefixEnd_5750010 984172966053051097710397 := by
  unfold tailWord_5750010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52430023474675817092555871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139813395932468845580148989 52430023474675817092555871)
  ·
    refine ⟨78645035212013725638833807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52430023474675817092555871 78645035212013725638833807)
    ·
      refine ⟨117967552818020588458250711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78645035212013725638833807 117967552818020588458250711)
      ·
        refine ⟨176951329227030882687376067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117967552818020588458250711 176951329227030882687376067)
        ·
          refine ⟨265426993840546324031064101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176951329227030882687376067 265426993840546324031064101)
          ·
            refine ⟨49767561345102435755824519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265426993840546324031064101 49767561345102435755824519)
            ·
              refine ⟨74651342017653653633736779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49767561345102435755824519 74651342017653653633736779)
              ·
                refine ⟨111977013026480480450605169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74651342017653653633736779 111977013026480480450605169)
                ·
                  refine ⟨83982759769860360337953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111977013026480480450605169 83982759769860360337953877)
                  ·
                    refine ⟨984172966053051097710397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83982759769860360337953877 984172966053051097710397)
                    ·
                      rfl

theorem cell23_5750010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_5750010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750010 prefixEnd_5750010 := by exact prefixLift 5750010
  have htrace : WordTrace (prefixWord ++ tailWord_5750010) baseStart_5750010 baseEnd_5750010 := by
    simpa [prefixWord, tailWord_5750010, baseEnd_5750010] using wordTrace_append hprefix tailTrace_5750010
  have hstable : (prefixWord ++ tailWord_5750010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750010).length < 2 ^ (prefixWord ++ tailWord_5750010).sum := by decide
  have hdescent : baseEnd_5750010 < baseStart_5750010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750017 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5750017 : Nat := 118140960795 + 5750017 * 2 ^ 59
def prefixEnd_5750017 : Nat := 4983230072969 + 3 ^ 40 * 5750017 * 2
def baseEnd_5750017 : Nat := 2952522492523734765743659

theorem tailTrace_5750017 : CollatzResearch.WordTrace tailWord_5750017 prefixEnd_5750017 2952522492523734765743659 := by
  unfold tailWord_5750017
  simp only [CollatzResearch.WordTrace]
  refine ⟨209720349209677908565728305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139813566139785272377152203 209720349209677908565728305)
  ·
    refine ⟨157290261907258431424296229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209720349209677908565728305 157290261907258431424296229)
    ·
      refine ⟨29491924107610955892055543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157290261907258431424296229 29491924107610955892055543)
      ·
        refine ⟨44237886161416433838083315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29491924107610955892055543 44237886161416433838083315)
        ·
          refine ⟨66356829242124650757124973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44237886161416433838083315 66356829242124650757124973)
          ·
            refine ⟨24883810965796744033921865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66356829242124650757124973 24883810965796744033921865)
            ·
              refine ⟨18662858224347558025441399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24883810965796744033921865 18662858224347558025441399)
              ·
                refine ⟨27994287336521337038162099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18662858224347558025441399 27994287336521337038162099)
                ·
                  refine ⟨41991431004782005557243149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27994287336521337038162099 41991431004782005557243149)
                  ·
                    refine ⟨15746786626793252083966181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41991431004782005557243149 15746786626793252083966181)
                    ·
                      refine ⟨2952522492523734765743659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15746786626793252083966181 2952522492523734765743659)
                      ·
                        rfl

theorem cell23_5750017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5750017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750017 prefixEnd_5750017 := by exact prefixLift 5750017
  have htrace : WordTrace (prefixWord ++ tailWord_5750017) baseStart_5750017 baseEnd_5750017 := by
    simpa [prefixWord, tailWord_5750017, baseEnd_5750017] using wordTrace_append hprefix tailTrace_5750017
  have hstable : (prefixWord ++ tailWord_5750017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750017).length < 2 ^ (prefixWord ++ tailWord_5750017).sum := by decide
  have hdescent : baseEnd_5750017 < baseStart_5750017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750018 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_5750018 : Nat := 118140960795 + 5750018 * 2 ^ 59
def prefixEnd_5750018 : Nat := 4983230072969 + 3 ^ 40 * 5750018 * 2
def baseEnd_5750018 : Nat := 328058111778265473536795

theorem tailTrace_5750018 : CollatzResearch.WordTrace tailWord_5750018 prefixEnd_5750018 328058111778265473536795 := by
  unfold tailWord_5750018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52430096420668571434128677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139813590455116190491009805 52430096420668571434128677)
  ·
    refine ⟨9830643078875357143899127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52430096420668571434128677 9830643078875357143899127)
    ·
      refine ⟨14745964618313035715848691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9830643078875357143899127 14745964618313035715848691)
      ·
        refine ⟨22118946927469553573773037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745964618313035715848691 22118946927469553573773037)
        ·
          refine ⟨8294605097801082590164889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22118946927469553573773037 8294605097801082590164889)
          ·
            refine ⟨6220953823350811942623667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294605097801082590164889 6220953823350811942623667)
            ·
              refine ⟨9331430735026217913935501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220953823350811942623667 9331430735026217913935501)
              ·
                refine ⟨3499286525634831717725813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9331430735026217913935501 3499286525634831717725813)
                ·
                  refine ⟨328058111778265473536795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3499286525634831717725813 328058111778265473536795)
                  ·
                    rfl

theorem cell23_5750018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_5750018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750018 prefixEnd_5750018 := by exact prefixLift 5750018
  have htrace : WordTrace (prefixWord ++ tailWord_5750018) baseStart_5750018 baseEnd_5750018 := by
    simpa [prefixWord, tailWord_5750018, baseEnd_5750018] using wordTrace_append hprefix tailTrace_5750018
  have hstable : (prefixWord ++ tailWord_5750018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750018).length < 2 ^ (prefixWord ++ tailWord_5750018).sum := by decide
  have hdescent : baseEnd_5750018 < baseStart_5750018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750044 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_5750044 : Nat := 118140960795 + 5750044 * 2 ^ 59
def prefixEnd_5750044 : Nat := 4983230072969 + 3 ^ 40 * 5750044 * 2
def baseEnd_5750044 : Nat := 984178785500468720035345

theorem tailTrace_5750044 : CollatzResearch.WordTrace tailWord_5750044 prefixEnd_5750044 984178785500468720035345 := by
  unfold tailWord_5750044
  simp only [CollatzResearch.WordTrace]
  refine ⟨104860666990290046088480593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139814222653720061451307457 104860666990290046088480593)
  ·
    refine ⟨78645500242717534566360445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104860666990290046088480593 78645500242717534566360445)
    ·
      refine ⟨29492062591019075462385167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78645500242717534566360445 29492062591019075462385167)
      ·
        refine ⟨44238093886528613193577751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29492062591019075462385167 44238093886528613193577751)
        ·
          refine ⟨66357140829792919790366627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44238093886528613193577751 66357140829792919790366627)
          ·
            refine ⟨99535711244689379685549941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66357140829792919790366627 99535711244689379685549941)
            ·
              refine ⟨9331472929189629345520307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99535711244689379685549941 9331472929189629345520307)
              ·
                refine ⟨13997209393784444018280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331472929189629345520307 13997209393784444018280461)
                ·
                  refine ⟨5248953522669166506855173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13997209393784444018280461 5248953522669166506855173)
                  ·
                    refine ⟨984178785500468720035345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248953522669166506855173 984178785500468720035345)
                    ·
                      rfl

theorem cell23_5750044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_5750044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750044 prefixEnd_5750044 := by exact prefixLift 5750044
  have htrace : WordTrace (prefixWord ++ tailWord_5750044) baseStart_5750044 baseEnd_5750044 := by
    simpa [prefixWord, tailWord_5750044, baseEnd_5750044] using wordTrace_append hprefix tailTrace_5750044
  have hstable : (prefixWord ++ tailWord_5750044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750044).length < 2 ^ (prefixWord ++ tailWord_5750044).sum := by decide
  have hdescent : baseEnd_5750044 < baseStart_5750044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750102 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5750102 : Nat := 118140960795 + 5750102 * 2 ^ 59
def prefixEnd_5750102 : Nat := 4983230072969 + 3 ^ 40 * 5750102 * 2
def baseEnd_5750102 : Nat := 2952566138379366933180769

theorem tailTrace_5750102 : CollatzResearch.WordTrace tailWord_5750102 prefixEnd_5750102 2952566138379366933180769 := by
  unfold tailWord_5750102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107715588398123005160785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139815632942913312055048373 13107715588398123005160785)
  ·
    refine ⟨9830786691298592253870589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13107715588398123005160785 9830786691298592253870589)
    ·
      refine ⟨3686545009236972095201471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9830786691298592253870589 3686545009236972095201471)
      ·
        refine ⟨5529817513855458142802207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686545009236972095201471 5529817513855458142802207)
        ·
          refine ⟨8294726270783187214203311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529817513855458142802207 8294726270783187214203311)
          ·
            refine ⟨12442089406174780821304967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294726270783187214203311 12442089406174780821304967)
            ·
              refine ⟨18663134109262171231957451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12442089406174780821304967 18663134109262171231957451)
              ·
                refine ⟨27994701163893256847936177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18663134109262171231957451 27994701163893256847936177)
                ·
                  refine ⟨20996025872919942635952133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27994701163893256847936177 20996025872919942635952133)
                  ·
                    refine ⟨3936754851172489244241025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20996025872919942635952133 3936754851172489244241025)
                    ·
                      refine ⟨2952566138379366933180769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936754851172489244241025 2952566138379366933180769)
                      ·
                        rfl

theorem cell23_5750102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5750102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750102 prefixEnd_5750102 := by exact prefixLift 5750102
  have htrace : WordTrace (prefixWord ++ tailWord_5750102) baseStart_5750102 baseEnd_5750102 := by
    simpa [prefixWord, tailWord_5750102, baseEnd_5750102] using wordTrace_append hprefix tailTrace_5750102
  have hstable : (prefixWord ++ tailWord_5750102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750102).length < 2 ^ (prefixWord ++ tailWord_5750102).sum := by decide
  have hdescent : baseEnd_5750102 < baseStart_5750102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750124 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_5750124 : Nat := 118140960795 + 5750124 * 2 ^ 59
def prefixEnd_5750124 : Nat := 4983230072969 + 3 ^ 40 * 5750124 * 2
def baseEnd_5750124 : Nat := 2952577434953765847105667

theorem tailTrace_5750124 : CollatzResearch.WordTrace tailWord_5750124 prefixEnd_5750124 2952577434953765847105667 := by
  unfold tailWord_5750124
  simp only [CollatzResearch.WordTrace]
  refine ⟨104862125910145132919936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139816167880193510559915617 104862125910145132919936713)
  ·
    refine ⟨78646594432608849689952535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104862125910145132919936713 78646594432608849689952535)
    ·
      refine ⟨117969891648913274534928803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78646594432608849689952535 117969891648913274534928803)
      ·
        refine ⟨176954837473369911802393205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117969891648913274534928803 176954837473369911802393205)
        ·
          refine ⟨16589516013128429231474363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176954837473369911802393205 16589516013128429231474363)
          ·
            refine ⟨24884274019692643847211545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16589516013128429231474363 24884274019692643847211545)
            ·
              refine ⟨18663205514769482885408659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24884274019692643847211545 18663205514769482885408659)
              ·
                refine ⟨27994808272154224328112989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18663205514769482885408659 27994808272154224328112989)
                ·
                  refine ⟨10498053102057834123042371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27994808272154224328112989 10498053102057834123042371)
                  ·
                    refine ⟨15747079653086751184563557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10498053102057834123042371 15747079653086751184563557)
                    ·
                      refine ⟨2952577434953765847105667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15747079653086751184563557 2952577434953765847105667)
                      ·
                        rfl

theorem cell23_5750124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_5750124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750124 prefixEnd_5750124 := by exact prefixLift 5750124
  have htrace : WordTrace (prefixWord ++ tailWord_5750124) baseStart_5750124 baseEnd_5750124 := by
    simpa [prefixWord, tailWord_5750124, baseEnd_5750124] using wordTrace_append hprefix tailTrace_5750124
  have hstable : (prefixWord ++ tailWord_5750124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750124).length < 2 ^ (prefixWord ++ tailWord_5750124).sum := by decide
  have hdescent : baseEnd_5750124 < baseStart_5750124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750141 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_5750141 : Nat := 118140960795 + 5750141 * 2 ^ 59
def prefixEnd_5750141 : Nat := 4983230072969 + 3 ^ 40 * 5750141 * 2
def baseEnd_5750141 : Nat := 2952586164124892280593089

theorem tailTrace_5750141 : CollatzResearch.WordTrace tailWord_5750141 prefixEnd_5750141 2952586164124892280593089 := by
  unfold tailWord_5750141
  simp only [CollatzResearch.WordTrace]
  refine ⟨209724871861228677743242277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139816581240819118495494851 209724871861228677743242277)
  ·
    refine ⟨39323413473980377076857927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209724871861228677743242277 39323413473980377076857927)
    ·
      refine ⟨58985120210970565615286891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39323413473980377076857927 58985120210970565615286891)
      ·
        refine ⟨88477680316455848422930337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58985120210970565615286891 88477680316455848422930337)
        ·
          refine ⟨66358260237341886317197753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88477680316455848422930337 66358260237341886317197753)
          ·
            refine ⟨49768695178006414737898315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66358260237341886317197753 49768695178006414737898315)
            ·
              refine ⟨74653042767009622106847473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49768695178006414737898315 74653042767009622106847473)
              ·
                refine ⟨55989782075257216580135605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74653042767009622106847473 55989782075257216580135605)
                ·
                  refine ⟨5249042069555364054387713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55989782075257216580135605 5249042069555364054387713)
                  ·
                    refine ⟨3936781552166523040790785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5249042069555364054387713 3936781552166523040790785)
                    ·
                      refine ⟨2952586164124892280593089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3936781552166523040790785 2952586164124892280593089)
                      ·
                        rfl

theorem cell23_5750141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_5750141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750141 prefixEnd_5750141 := by exact prefixLift 5750141
  have htrace : WordTrace (prefixWord ++ tailWord_5750141) baseStart_5750141 baseEnd_5750141 := by
    simpa [prefixWord, tailWord_5750141, baseEnd_5750141] using wordTrace_append hprefix tailTrace_5750141
  have hstable : (prefixWord ++ tailWord_5750141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750141).length < 2 ^ (prefixWord ++ tailWord_5750141).sum := by decide
  have hdescent : baseEnd_5750141 < baseStart_5750141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750147 : List Nat := [1, 1, 1, 3, 5, 2, 10]
def baseStart_5750147 : Nat := 118140960795 + 5750147 * 2 ^ 59
def prefixEnd_5750147 : Nat := 4983230072969 + 3 ^ 40 * 5750147 * 2
def baseEnd_5750147 : Nat := 36451719074182953791581

theorem tailTrace_5750147 : CollatzResearch.WordTrace tailWord_5750147 prefixEnd_5750147 36451719074182953791581 := by
  unfold tailWord_5750147
  simp only [CollatzResearch.WordTrace]
  refine ⟨209725090699206940767960695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139816727132804627178640463 209725090699206940767960695)
  ·
    refine ⟨314587636048810411151941043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209725090699206940767960695 314587636048810411151941043)
    ·
      refine ⟨471881454073215616727911565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314587636048810411151941043 471881454073215616727911565)
      ·
        refine ⟨176955545277455856272966837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471881454073215616727911565 176955545277455856272966837)
        ·
          refine ⟨16589582369761486525590641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176955545277455856272966837 16589582369761486525590641)
          ·
            refine ⟨12442186777321114894192981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16589582369761486525590641 12442186777321114894192981)
            ·
              refine ⟨36451719074182953791581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12442186777321114894192981 36451719074182953791581)
              ·
                rfl

theorem cell23_5750147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 10].length) (baseStart_5750147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750147 prefixEnd_5750147 := by exact prefixLift 5750147
  have htrace : WordTrace (prefixWord ++ tailWord_5750147) baseStart_5750147 baseEnd_5750147 := by
    simpa [prefixWord, tailWord_5750147, baseEnd_5750147] using wordTrace_append hprefix tailTrace_5750147
  have hstable : (prefixWord ++ tailWord_5750147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750147).length < 2 ^ (prefixWord ++ tailWord_5750147).sum := by decide
  have hdescent : baseEnd_5750147 < baseStart_5750147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750151 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 2, 4]
def baseStart_5750151 : Nat := 118140960795 + 5750151 * 2 ^ 59
def prefixEnd_5750151 : Nat := 4983230072969 + 3 ^ 40 * 5750151 * 2
def baseEnd_5750151 : Nat := 984197099643812413822681

theorem tailTrace_5750151 : CollatzResearch.WordTrace tailWord_5750151 prefixEnd_5750151 984197099643812413822681 := by
  unfold tailWord_5750151
  simp only [CollatzResearch.WordTrace]
  refine ⟨209725236591192449451106307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139816824394128299634070871 209725236591192449451106307)
  ·
    refine ⟨314587854886788674176659461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209725236591192449451106307 314587854886788674176659461)
    ·
      refine ⟨58985222791272876408123649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314587854886788674176659461 58985222791272876408123649)
      ·
        refine ⟨44238917093454657306092737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58985222791272876408123649 44238917093454657306092737)
        ·
          refine ⟨33179187820090992979569553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44238917093454657306092737 33179187820090992979569553)
          ·
            refine ⟨24884390865068244734677165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33179187820090992979569553 24884390865068244734677165)
            ·
              refine ⟨9331646574400591775503937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24884390865068244734677165 9331646574400591775503937)
              ·
                refine ⟨6998734930800443831627953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331646574400591775503937 6998734930800443831627953)
                ·
                  refine ⟨5249051198100332873720965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998734930800443831627953 5249051198100332873720965)
                  ·
                    refine ⟨984197099643812413822681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249051198100332873720965 984197099643812413822681)
                    ·
                      rfl

theorem cell23_5750151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_5750151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750151 prefixEnd_5750151 := by exact prefixLift 5750151
  have htrace : WordTrace (prefixWord ++ tailWord_5750151) baseStart_5750151 baseEnd_5750151 := by
    simpa [prefixWord, tailWord_5750151, baseEnd_5750151] using wordTrace_append hprefix tailTrace_5750151
  have hstable : (prefixWord ++ tailWord_5750151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750151).length < 2 ^ (prefixWord ++ tailWord_5750151).sum := by decide
  have hdescent : baseEnd_5750151 < baseStart_5750151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750168 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_5750168 : Nat := 118140960795 + 5750168 * 2 ^ 59
def prefixEnd_5750168 : Nat := 4983230072969 + 3 ^ 40 * 5750168 * 2
def baseEnd_5750168 : Nat := 984200009367521224985155

theorem tailTrace_5750168 : CollatzResearch.WordTrace tailWord_5750168 prefixEnd_5750168 984200009367521224985155 := by
  unfold tailWord_5750168
  simp only [CollatzResearch.WordTrace]
  refine ⟨104862928316065430677237579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139817237754753907569650105 104862928316065430677237579)
  ·
    refine ⟨157294392474098146015856369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104862928316065430677237579 157294392474098146015856369)
    ·
      refine ⟨117970794355573609511892277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157294392474098146015856369 117970794355573609511892277)
      ·
        refine ⟨11059761970835025891739901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117970794355573609511892277 11059761970835025891739901)
        ·
          refine ⟨4147410739063134709402463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11059761970835025891739901 4147410739063134709402463)
          ·
            refine ⟨6221116108594702064103695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147410739063134709402463 6221116108594702064103695)
            ·
              refine ⟨9331674162892053096155543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221116108594702064103695 9331674162892053096155543)
              ·
                refine ⟨13997511244338079644233315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331674162892053096155543 13997511244338079644233315)
                ·
                  refine ⟨20996266866507119466349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13997511244338079644233315 20996266866507119466349973)
                  ·
                    refine ⟨984200009367521224985155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20996266866507119466349973 984200009367521224985155)
                    ·
                      rfl

theorem cell23_5750168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_5750168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750168 prefixEnd_5750168 := by exact prefixLift 5750168
  have htrace : WordTrace (prefixWord ++ tailWord_5750168) baseStart_5750168 baseEnd_5750168 := by
    simpa [prefixWord, tailWord_5750168, baseEnd_5750168] using wordTrace_append hprefix tailTrace_5750168
  have hstable : (prefixWord ++ tailWord_5750168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750168).length < 2 ^ (prefixWord ++ tailWord_5750168).sum := by decide
  have hdescent : baseEnd_5750168 < baseStart_5750168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750178 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5750178 : Nat := 118140960795 + 5750178 * 2 ^ 59
def prefixEnd_5750178 : Nat := 4983230072969 + 3 ^ 40 * 5750178 * 2
def baseEnd_5750178 : Nat := 2952605162909108635830419

theorem tailTrace_5750178 : CollatzResearch.WordTrace tailWord_5750178 prefixEnd_5750178 2952605162909108635830419 := by
  unfold tailWord_5750178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52431555340523658265584797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139817480908063088708226125 52431555340523658265584797)
  ·
    refine ⟨19661833252696371849594299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52431555340523658265584797 19661833252696371849594299)
    ·
      refine ⟨29492749879044557774391449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661833252696371849594299 29492749879044557774391449)
      ·
        refine ⟨22119562409283418330793587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29492749879044557774391449 22119562409283418330793587)
        ·
          refine ⟨33179343613925127496190381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22119562409283418330793587 33179343613925127496190381)
          ·
            refine ⟨12442253855221922811071393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33179343613925127496190381 12442253855221922811071393)
            ·
              refine ⟨9331690391416442108303545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12442253855221922811071393 9331690391416442108303545)
              ·
                refine ⟨6998767793562331581227659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331690391416442108303545 6998767793562331581227659)
                ·
                  refine ⟨10498151690343497371841489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998767793562331581227659 10498151690343497371841489)
                  ·
                    refine ⟨7873613767757623028881117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10498151690343497371841489 7873613767757623028881117)
                    ·
                      refine ⟨2952605162909108635830419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7873613767757623028881117 2952605162909108635830419)
                      ·
                        rfl

theorem cell23_5750178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5750178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750178 prefixEnd_5750178 := by exact prefixLift 5750178
  have htrace : WordTrace (prefixWord ++ tailWord_5750178) baseStart_5750178 baseEnd_5750178 := by
    simpa [prefixWord, tailWord_5750178, baseEnd_5750178] using wordTrace_append hprefix tailTrace_5750178
  have hstable : (prefixWord ++ tailWord_5750178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750178).length < 2 ^ (prefixWord ++ tailWord_5750178).sum := by decide
  have hdescent : baseEnd_5750178 < baseStart_5750178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750207 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 4, 6]
def baseStart_5750207 : Nat := 118140960795 + 5750207 * 2 ^ 59
def prefixEnd_5750207 : Nat := 4983230072969 + 3 ^ 40 * 5750207 * 2
def baseEnd_5750207 : Nat := 984206684616029674122595

theorem tailTrace_5750207 : CollatzResearch.WordTrace tailWord_5750207 prefixEnd_5750207 984206684616029674122595 := by
  unfold tailWord_5750207
  simp only [CollatzResearch.WordTrace]
  refine ⟨209727279078989571015144875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139818186052659714010096583 209727279078989571015144875)
  ·
    refine ⟨314590918618484356522717313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209727279078989571015144875 314590918618484356522717313)
    ·
      refine ⟨235943188963863267392037985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314590918618484356522717313 235943188963863267392037985)
      ·
        refine ⟨176957391722897450544028489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235943188963863267392037985 176957391722897450544028489)
        ·
          refine ⟨132718043792173087908021367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176957391722897450544028489 132718043792173087908021367)
          ·
            refine ⟨199077065688259631862032051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132718043792173087908021367 199077065688259631862032051)
            ·
              refine ⟨298615598532389447793048077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199077065688259631862032051 298615598532389447793048077)
              ·
                refine ⟨111980849449646042922393029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298615598532389447793048077 111980849449646042922393029)
                ·
                  refine ⟨20996409271808633047948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111980849449646042922393029 20996409271808633047948693)
                  ·
                    refine ⟨984206684616029674122595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20996409271808633047948693 984206684616029674122595)
                    ·
                      rfl

theorem cell23_5750207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_5750207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750207 prefixEnd_5750207 := by exact prefixLift 5750207
  have htrace : WordTrace (prefixWord ++ tailWord_5750207) baseStart_5750207 baseEnd_5750207 := by
    simpa [prefixWord, tailWord_5750207, baseEnd_5750207] using wordTrace_append hprefix tailTrace_5750207
  have hstable : (prefixWord ++ tailWord_5750207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750207).length < 2 ^ (prefixWord ++ tailWord_5750207).sum := by decide
  have hdescent : baseEnd_5750207 < baseStart_5750207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750217 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_5750217 : Nat := 118140960795 + 5750217 * 2 ^ 59
def prefixEnd_5750217 : Nat := 4983230072969 + 3 ^ 40 * 5750217 * 2
def baseEnd_5750217 : Nat := 2952625188654633983242739

theorem tailTrace_5750217 : CollatzResearch.WordTrace tailWord_5750217 prefixEnd_5750217 2952625188654633983242739 := by
  unfold tailWord_5750217
  simp only [CollatzResearch.WordTrace]
  refine ⟨209727643808953342723008905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139818429205968895148672603 209727643808953342723008905)
  ·
    refine ⟨157295732856715007042256679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209727643808953342723008905 157295732856715007042256679)
    ·
      refine ⟨235943599285072510563385019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157295732856715007042256679 235943599285072510563385019)
      ·
        refine ⟨353915398927608765845077529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235943599285072510563385019 353915398927608765845077529)
        ·
          refine ⟨265436549195706574383808147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353915398927608765845077529 265436549195706574383808147)
          ·
            refine ⟨398154823793559861575712221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265436549195706574383808147 398154823793559861575712221)
            ·
              refine ⟨149308058922584948090892083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398154823793559861575712221 149308058922584948090892083)
              ·
                refine ⟨223962088383877422136338125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149308058922584948090892083 223962088383877422136338125)
                ·
                  refine ⟨83985783143954033301126797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223962088383877422136338125 83985783143954033301126797)
                  ·
                    refine ⟨31494668678982762487922549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83985783143954033301126797 31494668678982762487922549)
                    ·
                      refine ⟨2952625188654633983242739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31494668678982762487922549 2952625188654633983242739)
                      ·
                        rfl

theorem cell23_5750217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_5750217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750217 prefixEnd_5750217 := by exact prefixLift 5750217
  have htrace : WordTrace (prefixWord ++ tailWord_5750217) baseStart_5750217 baseEnd_5750217 := by
    simpa [prefixWord, tailWord_5750217, baseEnd_5750217] using wordTrace_append hprefix tailTrace_5750217
  have hstable : (prefixWord ++ tailWord_5750217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750217).length < 2 ^ (prefixWord ++ tailWord_5750217).sum := by decide
  have hdescent : baseEnd_5750217 < baseStart_5750217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750234 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_5750234 : Nat := 118140960795 + 5750234 * 2 ^ 59
def prefixEnd_5750234 : Nat := 4983230072969 + 3 ^ 40 * 5750234 * 2
def baseEnd_5750234 : Nat := 2952633917825760416730161

theorem tailTrace_5750234 : CollatzResearch.WordTrace tailWord_5750234 prefixEnd_5750234 2952633917825760416730161 := by
  unfold tailWord_5750234
  simp only [CollatzResearch.WordTrace]
  refine ⟨52432065962472938656594439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139818842566594503084251837 52432065962472938656594439)
  ·
    refine ⟨78648098943709407984891659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52432065962472938656594439 78648098943709407984891659)
    ·
      refine ⟨117972148415564111977337489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78648098943709407984891659 117972148415564111977337489)
      ·
        refine ⟨88479111311673083983003117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117972148415564111977337489 88479111311673083983003117)
        ·
          refine ⟨33179666741877406493626169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88479111311673083983003117 33179666741877406493626169)
          ·
            refine ⟨24884750056408054870219627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33179666741877406493626169 24884750056408054870219627)
            ·
              refine ⟨37327125084612082305329441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24884750056408054870219627 37327125084612082305329441)
              ·
                refine ⟨27995343813459061728997081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37327125084612082305329441 27995343813459061728997081)
                ·
                  refine ⟨20996507860094296296747811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27995343813459061728997081 20996507860094296296747811)
                  ·
                    refine ⟨31494761790141444445121717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20996507860094296296747811 31494761790141444445121717)
                    ·
                      refine ⟨2952633917825760416730161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31494761790141444445121717 2952633917825760416730161)
                      ·
                        rfl

theorem cell23_5750234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_5750234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750234 prefixEnd_5750234 := by exact prefixLift 5750234
  have htrace : WordTrace (prefixWord ++ tailWord_5750234) baseStart_5750234 baseEnd_5750234 := by
    simpa [prefixWord, tailWord_5750234, baseEnd_5750234] using wordTrace_append hprefix tailTrace_5750234
  have hstable : (prefixWord ++ tailWord_5750234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750234).length < 2 ^ (prefixWord ++ tailWord_5750234).sum := by decide
  have hdescent : baseEnd_5750234 < baseStart_5750234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750382 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5750382 : Nat := 118140960795 + 5750382 * 2 ^ 59
def prefixEnd_5750382 : Nat := 4983230072969 + 3 ^ 40 * 5750382 * 2
def baseEnd_5750382 : Nat := 984236637654208612559827

theorem tailTrace_5750382 : CollatzResearch.WordTrace tailWord_5750382 prefixEnd_5750382 984236637654208612559827 := by
  unfold tailWord_5750382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26216707731669446987845675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139822441235570383935176933 26216707731669446987845675)
  ·
    refine ⟨39325061597504170481768513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26216707731669446987845675 39325061597504170481768513)
    ·
      refine ⟨29493796198128127861326385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39325061597504170481768513 29493796198128127861326385)
      ·
        refine ⟨22120347148596095895994789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29493796198128127861326385 22120347148596095895994789)
        ·
          refine ⟨4147565090361767980499023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22120347148596095895994789 4147565090361767980499023)
          ·
            refine ⟨6221347635542651970748535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147565090361767980499023 6221347635542651970748535)
            ·
              refine ⟨9332021453313977956122803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221347635542651970748535 9332021453313977956122803)
              ·
                refine ⟨13998032179970966934184205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9332021453313977956122803 13998032179970966934184205)
                ·
                  refine ⟨5249262067489112600319077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998032179970966934184205 5249262067489112600319077)
                  ·
                    refine ⟨984236637654208612559827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249262067489112600319077 984236637654208612559827)
                    ·
                      rfl

theorem cell23_5750382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5750382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750382 prefixEnd_5750382 := by exact prefixLift 5750382
  have htrace : WordTrace (prefixWord ++ tailWord_5750382) baseStart_5750382 baseEnd_5750382 := by
    simpa [prefixWord, tailWord_5750382, baseEnd_5750382] using wordTrace_append hprefix tailTrace_5750382
  have hstable : (prefixWord ++ tailWord_5750382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750382).length < 2 ^ (prefixWord ++ tailWord_5750382).sum := by decide
  have hdescent : baseEnd_5750382 < baseStart_5750382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750411 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4]
def baseStart_5750411 : Nat := 118140960795 + 5750411 * 2 ^ 59
def prefixEnd_5750411 : Nat := 4983230072969 + 3 ^ 40 * 5750411 * 2
def baseEnd_5750411 : Nat := 2952724803901606224216847

theorem tailTrace_5750411 : CollatzResearch.WordTrace tailWord_5750411 prefixEnd_5750411 2952724803901606224216847 := by
  unfold tailWord_5750411
  simp only [CollatzResearch.WordTrace]
  refine ⟨209734719570250513855571087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139823146380167009237047391 209734719570250513855571087)
  ·
    refine ⟨314602079355375770783356631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209734719570250513855571087 314602079355375770783356631)
    ·
      refine ⟨471903119033063656175034947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314602079355375770783356631 471903119033063656175034947)
      ·
        refine ⟨707854678549595484262552421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471903119033063656175034947 707854678549595484262552421)
        ·
          refine ⟨132722752228049153299228579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 707854678549595484262552421 132722752228049153299228579)
          ·
            refine ⟨199084128342073729948842869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132722752228049153299228579 199084128342073729948842869)
            ·
              refine ⟨18664137032069412182704019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199084128342073729948842869 18664137032069412182704019)
              ·
                refine ⟨27996205548104118274056029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18664137032069412182704019 27996205548104118274056029)
                ·
                  refine ⟨10498577080539044352771011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27996205548104118274056029 10498577080539044352771011)
                  ·
                    refine ⟨15747865620808566529156517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10498577080539044352771011 15747865620808566529156517)
                    ·
                      refine ⟨2952724803901606224216847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15747865620808566529156517 2952724803901606224216847)
                      ·
                        rfl

theorem cell23_5750411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_5750411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750411 prefixEnd_5750411 := by exact prefixLift 5750411
  have htrace : WordTrace (prefixWord ++ tailWord_5750411) baseStart_5750411 baseEnd_5750411 := by
    simpa [prefixWord, tailWord_5750411, baseEnd_5750411] using wordTrace_append hprefix tailTrace_5750411
  have hstable : (prefixWord ++ tailWord_5750411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750411).length < 2 ^ (prefixWord ++ tailWord_5750411).sum := by decide
  have hdescent : baseEnd_5750411 < baseStart_5750411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750421 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_5750421 : Nat := 118140960795 + 5750421 * 2 ^ 59
def prefixEnd_5750421 : Nat := 4983230072969 + 3 ^ 40 * 5750421 * 2
def baseEnd_5750421 : Nat := 984243312902717061697267

theorem tailTrace_5750421 : CollatzResearch.WordTrace tailWord_5750421 prefixEnd_5750421 984243312902717061697267 := by
  unfold tailWord_5750421
  simp only [CollatzResearch.WordTrace]
  refine ⟨209735084300214285563435117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139823389533476190375623411 209735084300214285563435117)
  ·
    refine ⟨78650656612580357086288169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209735084300214285563435117 78650656612580357086288169)
    ·
      refine ⟨58987992459435267814716127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78650656612580357086288169 58987992459435267814716127)
      ·
        refine ⟨88481988689152901722074191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58987992459435267814716127 88481988689152901722074191)
        ·
          refine ⟨132722983033729352583111287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88481988689152901722074191 132722983033729352583111287)
          ·
            refine ⟨199084474550594028874666931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132722983033729352583111287 199084474550594028874666931)
            ·
              refine ⟨298626711825891043312000397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199084474550594028874666931 298626711825891043312000397)
              ·
                refine ⟨111985016934709141242000149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298626711825891043312000397 111985016934709141242000149)
                ·
                  refine ⟨5249297668814490995718757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111985016934709141242000149 5249297668814490995718757)
                  ·
                    refine ⟨984243312902717061697267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249297668814490995718757 984243312902717061697267)
                    ·
                      rfl

theorem cell23_5750421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_5750421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750421 prefixEnd_5750421 := by exact prefixLift 5750421
  have htrace : WordTrace (prefixWord ++ tailWord_5750421) baseStart_5750421 baseEnd_5750421 := by
    simpa [prefixWord, tailWord_5750421, baseEnd_5750421] using wordTrace_append hprefix tailTrace_5750421
  have hstable : (prefixWord ++ tailWord_5750421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750421).length < 2 ^ (prefixWord ++ tailWord_5750421).sum := by decide
  have hdescent : baseEnd_5750421 < baseStart_5750421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750458 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_5750458 : Nat := 118140960795 + 5750458 * 2 ^ 59
def prefixEnd_5750458 : Nat := 4983230072969 + 3 ^ 40 * 5750458 * 2
def baseEnd_5750458 : Nat := 2952748937492367540329131

theorem tailTrace_5750458 : CollatzResearch.WordTrace tailWord_5750458 prefixEnd_5750458 2952748937492367540329131 := by
  unfold tailWord_5750458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52434108450270060220633007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139824289200720160588354685 52434108450270060220633007)
  ·
    refine ⟨78651162675405090330949511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52434108450270060220633007 78651162675405090330949511)
    ·
      refine ⟨117976744013107635496424267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78651162675405090330949511 117976744013107635496424267)
      ·
        refine ⟨176965116019661453244636401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117976744013107635496424267 176965116019661453244636401)
        ·
          refine ⟨132723837014746089933477301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176965116019661453244636401 132723837014746089933477301)
          ·
            refine ⟨12442859720132445931263497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132723837014746089933477301 12442859720132445931263497)
            ·
              refine ⟨9332144790099334448447623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12442859720132445931263497 9332144790099334448447623)
              ·
                refine ⟨13998217185149001672671435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9332144790099334448447623 13998217185149001672671435)
                ·
                  refine ⟨20997325777723502509007153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13998217185149001672671435 20997325777723502509007153)
                  ·
                    refine ⟨15747994333292626881755365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20997325777723502509007153 15747994333292626881755365)
                    ·
                      refine ⟨2952748937492367540329131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15747994333292626881755365 2952748937492367540329131)
                      ·
                        rfl

theorem cell23_5750458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_5750458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750458 prefixEnd_5750458 := by exact prefixLift 5750458
  have htrace : WordTrace (prefixWord ++ tailWord_5750458) baseStart_5750458 baseEnd_5750458 := by
    simpa [prefixWord, tailWord_5750458, baseEnd_5750458] using wordTrace_append hprefix tailTrace_5750458
  have hstable : (prefixWord ++ tailWord_5750458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750458).length < 2 ^ (prefixWord ++ tailWord_5750458).sum := by decide
  have hdescent : baseEnd_5750458 < baseStart_5750458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750462 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_5750462 : Nat := 118140960795 + 5750462 * 2 ^ 59
def prefixEnd_5750462 : Nat := 4983230072969 + 3 ^ 40 * 5750462 * 2
def baseEnd_5750462 : Nat := 2952750991414985524679113

theorem tailTrace_5750462 : CollatzResearch.WordTrace tailWord_5750462 prefixEnd_5750462 2952750991414985524679113 := by
  unfold tailWord_5750462
  simp only [CollatzResearch.WordTrace]
  refine ⟨26217072461633218695709705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139824386462043833043785093 26217072461633218695709705)
  ·
    refine ⟨19662804346224914021782279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26217072461633218695709705 19662804346224914021782279)
    ·
      refine ⟨29494206519337371032673419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19662804346224914021782279 29494206519337371032673419)
      ·
        refine ⟨44241309779006056549010129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29494206519337371032673419 44241309779006056549010129)
        ·
          refine ⟨33180982334254542411757597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44241309779006056549010129 33180982334254542411757597)
          ·
            refine ⟨12442868375345453404409099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33180982334254542411757597 12442868375345453404409099)
            ·
              refine ⟨18664302563018180106613649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12442868375345453404409099 18664302563018180106613649)
              ·
                refine ⟨13998226922263635079960237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18664302563018180106613649 13998226922263635079960237)
                ·
                  refine ⟨5249335095848863154985089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998226922263635079960237 5249335095848863154985089)
                  ·
                    refine ⟨3937001321886647366238817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5249335095848863154985089 3937001321886647366238817)
                    ·
                      refine ⟨2952750991414985524679113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937001321886647366238817 2952750991414985524679113)
                      ·
                        rfl

theorem cell23_5750462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_5750462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750462 prefixEnd_5750462 := by exact prefixLift 5750462
  have htrace : WordTrace (prefixWord ++ tailWord_5750462) baseStart_5750462 baseEnd_5750462 := by
    simpa [prefixWord, tailWord_5750462, baseEnd_5750462] using wordTrace_append hprefix tailTrace_5750462
  have hstable : (prefixWord ++ tailWord_5750462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750462).length < 2 ^ (prefixWord ++ tailWord_5750462).sum := by decide
  have hdescent : baseEnd_5750462 < baseStart_5750462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750468 : List Nat := [2, 3, 3, 1, 1, 1, 5, 7]
def baseStart_5750468 : Nat := 118140960795 + 5750468 * 2 ^ 59
def prefixEnd_5750468 : Nat := 4983230072969 + 3 ^ 40 * 5750468 * 2
def baseEnd_5750468 : Nat := 109361261936996759303855

theorem tailTrace_5750468 : CollatzResearch.WordTrace tailWord_5750468 prefixEnd_5750468 109361261936996759303855 := by
  unfold tailWord_5750468
  simp only [CollatzResearch.WordTrace]
  refine ⟨104868399265522006295198029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139824532354029341726930705 104868399265522006295198029)
  ·
    refine ⟨39325649724570752360699261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104868399265522006295198029 39325649724570752360699261)
    ·
      refine ⟨14747118646714032135262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39325649724570752360699261 14747118646714032135262223)
      ·
        refine ⟨22120677970071048202893335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14747118646714032135262223 22120677970071048202893335)
        ·
          refine ⟨33181016955106572304340003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22120677970071048202893335 33181016955106572304340003)
          ·
            refine ⟨49771525432659858456510005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33181016955106572304340003 49771525432659858456510005)
            ·
              refine ⟨4666080509311861730297813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49771525432659858456510005 4666080509311861730297813)
              ·
                refine ⟨109361261936996759303855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4666080509311861730297813 109361261936996759303855)
                ·
                  rfl

theorem cell23_5750468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 7].length) (baseStart_5750468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750468 prefixEnd_5750468 := by exact prefixLift 5750468
  have htrace : WordTrace (prefixWord ++ tailWord_5750468) baseStart_5750468 baseEnd_5750468 := by
    simpa [prefixWord, tailWord_5750468, baseEnd_5750468] using wordTrace_append hprefix tailTrace_5750468
  have hstable : (prefixWord ++ tailWord_5750468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750468).length < 2 ^ (prefixWord ++ tailWord_5750468).sum := by decide
  have hdescent : baseEnd_5750468 < baseStart_5750468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750478 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_5750478 : Nat := 118140960795 + 5750478 * 2 ^ 59
def prefixEnd_5750478 : Nat := 4983230072969 + 3 ^ 40 * 5750478 * 2
def baseEnd_5750478 : Nat := 2952759207105457462079039

theorem tailTrace_5750478 : CollatzResearch.WordTrace tailWord_5750478 prefixEnd_5750478 2952759207105457462079039 := by
  unfold tailWord_5750478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26217145407625973037282511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139824775507338522865506725 26217145407625973037282511)
  ·
    refine ⟨39325718111438959555923767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26217145407625973037282511 39325718111438959555923767)
    ·
      refine ⟨58988577167158439333885651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39325718111438959555923767 58988577167158439333885651)
      ·
        refine ⟨88482865750737659000828477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58988577167158439333885651 88482865750737659000828477)
        ·
          refine ⟨33181074656526622125310679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88482865750737659000828477 33181074656526622125310679)
          ·
            refine ⟨49771611984789933187966019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33181074656526622125310679 49771611984789933187966019)
            ·
              refine ⟨74657417977184899781949029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49771611984789933187966019 74657417977184899781949029)
              ·
                refine ⟨13998265870722168709115443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74657417977184899781949029 13998265870722168709115443)
                ·
                  refine ⟨20997398806083253063673165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13998265870722168709115443 20997398806083253063673165)
                  ·
                    refine ⟨7874024552281219898877437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20997398806083253063673165 7874024552281219898877437)
                    ·
                      refine ⟨2952759207105457462079039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874024552281219898877437 2952759207105457462079039)
                      ·
                        rfl

theorem cell23_5750478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_5750478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750478 prefixEnd_5750478 := by exact prefixLift 5750478
  have htrace : WordTrace (prefixWord ++ tailWord_5750478) baseStart_5750478 baseEnd_5750478 := by
    simpa [prefixWord, tailWord_5750478, baseEnd_5750478] using wordTrace_append hprefix tailTrace_5750478
  have hstable : (prefixWord ++ tailWord_5750478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750478).length < 2 ^ (prefixWord ++ tailWord_5750478).sum := by decide
  have hdescent : baseEnd_5750478 < baseStart_5750478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750482 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5750482 : Nat := 118140960795 + 5750482 * 2 ^ 59
def prefixEnd_5750482 : Nat := 4983230072969 + 3 ^ 40 * 5750482 * 2
def baseEnd_5750482 : Nat := 2952761261028075446429021

theorem tailTrace_5750482 : CollatzResearch.WordTrace tailWord_5750482 prefixEnd_5750482 2952761261028075446429021 := by
  unfold tailWord_5750482
  simp only [CollatzResearch.WordTrace]
  refine ⟨52434327288248323245351425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139824872768662195320937133 52434327288248323245351425)
  ·
    refine ⟨39325745466186242434013569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52434327288248323245351425 39325745466186242434013569)
    ·
      refine ⟨29494309099639681825510177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39325745466186242434013569 29494309099639681825510177)
      ·
        refine ⟨22120731824729761369132633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29494309099639681825510177 22120731824729761369132633)
        ·
          refine ⟨16590548868547321026849475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22120731824729761369132633 16590548868547321026849475)
          ·
            refine ⟨24885823302820981540274213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16590548868547321026849475 24885823302820981540274213)
            ·
              refine ⟨4666091869278934038801415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24885823302820981540274213 4666091869278934038801415)
              ·
                refine ⟨6999137803918401058202123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666091869278934038801415 6999137803918401058202123)
                ·
                  refine ⟨10498706705877601587303185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6999137803918401058202123 10498706705877601587303185)
                  ·
                    refine ⟨7874030029408201190477389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10498706705877601587303185 7874030029408201190477389)
                    ·
                      refine ⟨2952761261028075446429021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874030029408201190477389 2952761261028075446429021)
                      ·
                        rfl

theorem cell23_5750482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5750482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750482 prefixEnd_5750482 := by exact prefixLift 5750482
  have htrace : WordTrace (prefixWord ++ tailWord_5750482) baseStart_5750482 baseEnd_5750482 := by
    simpa [prefixWord, tailWord_5750482, baseEnd_5750482] using wordTrace_append hprefix tailTrace_5750482
  have hstable : (prefixWord ++ tailWord_5750482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750482).length < 2 ^ (prefixWord ++ tailWord_5750482).sum := by decide
  have hdescent : baseEnd_5750482 < baseStart_5750482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750511 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 6]
def baseStart_5750511 : Nat := 118140960795 + 5750511 * 2 ^ 59
def prefixEnd_5750511 : Nat := 4983230072969 + 3 ^ 40 * 5750511 * 2
def baseEnd_5750511 : Nat := 984258717322351944322129

theorem tailTrace_5750511 : CollatzResearch.WordTrace tailWord_5750511 prefixEnd_5750511 984258717322351944322129 := by
  unfold tailWord_5750511
  simp only [CollatzResearch.WordTrace]
  refine ⟨209738366869888230934211387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139825577913258820622807591 209738366869888230934211387)
  ·
    refine ⟨314607550304832346401317081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209738366869888230934211387 314607550304832346401317081)
    ·
      refine ⟨235955662728624259800987811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314607550304832346401317081 235955662728624259800987811)
      ·
        refine ⟨353933494092936389701481717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235955662728624259800987811 353933494092936389701481717)
        ·
          refine ⟨33181265071212786534513911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 353933494092936389701481717 33181265071212786534513911)
          ·
            refine ⟨49771897606819179801770867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33181265071212786534513911 49771897606819179801770867)
            ·
              refine ⟨74657846410228769702656301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49771897606819179801770867 74657846410228769702656301)
              ·
                refine ⟨27996692403835788638496113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74657846410228769702656301 27996692403835788638496113)
                ·
                  refine ⟨20997519302876841478872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27996692403835788638496113 20997519302876841478872085)
                  ·
                    refine ⟨984258717322351944322129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20997519302876841478872085 984258717322351944322129)
                    ·
                      rfl

theorem cell23_5750511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_5750511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750511 prefixEnd_5750511 := by exact prefixLift 5750511
  have htrace : WordTrace (prefixWord ++ tailWord_5750511) baseStart_5750511 baseEnd_5750511 := by
    simpa [prefixWord, tailWord_5750511, baseEnd_5750511] using wordTrace_append hprefix tailTrace_5750511
  have hstable : (prefixWord ++ tailWord_5750511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750511).length < 2 ^ (prefixWord ++ tailWord_5750511).sum := by decide
  have hdescent : baseEnd_5750511 < baseStart_5750511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750531 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_5750531 : Nat := 118140960795 + 5750531 * 2 ^ 59
def prefixEnd_5750531 : Nat := 4983230072969 + 3 ^ 40 * 5750531 * 2
def baseEnd_5750531 : Nat := 2952786421580145754716295

theorem tailTrace_5750531 : CollatzResearch.WordTrace tailWord_5750531 prefixEnd_5750531 2952786421580145754716295 := by
  unfold tailWord_5750531
  simp only [CollatzResearch.WordTrace]
  refine ⟨209739096329815774349939447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139826064219877182899959631 209739096329815774349939447)
  ·
    refine ⟨314608644494723661524909171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209739096329815774349939447 314608644494723661524909171)
    ·
      refine ⟨471912966742085492287363757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314608644494723661524909171 471912966742085492287363757)
      ·
        refine ⟨176967362528282059607761409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471912966742085492287363757 176967362528282059607761409)
        ·
          refine ⟨132725521896211544705821057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176967362528282059607761409 132725521896211544705821057)
          ·
            refine ⟨99544141422158658529365793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132725521896211544705821057 99544141422158658529365793)
            ·
              refine ⟨74658106066618993897024345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99544141422158658529365793 74658106066618993897024345)
              ·
                refine ⟨55993579549964245422768259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74658106066618993897024345 55993579549964245422768259)
                ·
                  refine ⟨83990369324946368134152389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55993579549964245422768259 83990369324946368134152389)
                  ·
                    refine ⟨15748194248427444025153573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83990369324946368134152389 15748194248427444025153573)
                    ·
                      refine ⟨2952786421580145754716295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15748194248427444025153573 2952786421580145754716295)
                      ·
                        rfl

theorem cell23_5750531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_5750531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750531 prefixEnd_5750531 := by exact prefixLift 5750531
  have htrace : WordTrace (prefixWord ++ tailWord_5750531) baseStart_5750531 baseEnd_5750531 := by
    simpa [prefixWord, tailWord_5750531, baseEnd_5750531] using wordTrace_append hprefix tailTrace_5750531
  have hstable : (prefixWord ++ tailWord_5750531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750531).length < 2 ^ (prefixWord ++ tailWord_5750531).sum := by decide
  have hdescent : baseEnd_5750531 < baseStart_5750531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750538 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5750538 : Nat := 118140960795 + 5750538 * 2 ^ 59
def prefixEnd_5750538 : Nat := 4983230072969 + 3 ^ 40 * 5750538 * 2
def baseEnd_5750538 : Nat := 2952790015944727227328763

theorem tailTrace_5750538 : CollatzResearch.WordTrace tailWord_5750538 prefixEnd_5750538 2952790015944727227328763 := by
  unfold tailWord_5750538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52434837910197603636361067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139826234427193609696962845 52434837910197603636361067)
  ·
    refine ⟨78652256865296405454541601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52434837910197603636361067 78652256865296405454541601)
    ·
      refine ⟨58989192648972304090906201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78652256865296405454541601 58989192648972304090906201)
      ·
        refine ⟨44241894486729228068179651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58989192648972304090906201 44241894486729228068179651)
        ·
          refine ⟨66362841730093842102269477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44241894486729228068179651 66362841730093842102269477)
          ·
            refine ⟨12443032824392595394175527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66362841730093842102269477 12443032824392595394175527)
            ·
              refine ⟨18664549236588893091263291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12443032824392595394175527 18664549236588893091263291)
              ·
                refine ⟨27996823854883339636894937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18664549236588893091263291 27996823854883339636894937)
                ·
                  refine ⟨20997617891162504727671203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27996823854883339636894937 20997617891162504727671203)
                  ·
                    refine ⟨31496426836743757091506805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20997617891162504727671203 31496426836743757091506805)
                    ·
                      refine ⟨2952790015944727227328763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31496426836743757091506805 2952790015944727227328763)
                      ·
                        rfl

theorem cell23_5750538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5750538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750538 prefixEnd_5750538 := by exact prefixLift 5750538
  have htrace : WordTrace (prefixWord ++ tailWord_5750538) baseStart_5750538 baseEnd_5750538 := by
    simpa [prefixWord, tailWord_5750538, baseEnd_5750538] using wordTrace_append hprefix tailTrace_5750538
  have hstable : (prefixWord ++ tailWord_5750538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750538).length < 2 ^ (prefixWord ++ tailWord_5750538).sum := by decide
  have hdescent : baseEnd_5750538 < baseStart_5750538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750588 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_5750588 : Nat := 118140960795 + 5750588 * 2 ^ 59
def prefixEnd_5750588 : Nat := 4983230072969 + 3 ^ 40 * 5750588 * 2
def baseEnd_5750588 : Nat := 984271896659150677234511

theorem tailTrace_5750588 : CollatzResearch.WordTrace tailWord_5750588 prefixEnd_5750588 984271896659150677234511 := by
  unfold tailWord_5750588
  simp only [CollatzResearch.WordTrace]
  refine ⟨104870587645304636542382209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139827450193739515389842945 104870587645304636542382209)
  ·
    refine ⟨78652940733978477406786657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104870587645304636542382209 78652940733978477406786657)
    ·
      refine ⟨58989705550483858055089993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78652940733978477406786657 58989705550483858055089993)
      ·
        refine ⟨44242279162862893541317495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58989705550483858055089993 44242279162862893541317495)
        ·
          refine ⟨66363418744294340311976243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44242279162862893541317495 66363418744294340311976243)
          ·
            refine ⟨99545128116441510467964365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66363418744294340311976243 99545128116441510467964365)
            ·
              refine ⟨37329423043665566425486637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99545128116441510467964365 37329423043665566425486637)
              ·
                refine ⟨13998533641374587409557489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37329423043665566425486637 13998533641374587409557489)
                ·
                  refine ⟨10498900231030940557168117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13998533641374587409557489 10498900231030940557168117)
                  ·
                    refine ⟨984271896659150677234511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10498900231030940557168117 984271896659150677234511)
                    ·
                      rfl

theorem cell23_5750588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_5750588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750588 prefixEnd_5750588 := by exact prefixLift 5750588
  have htrace : WordTrace (prefixWord ++ tailWord_5750588) baseStart_5750588 baseEnd_5750588 := by
    simpa [prefixWord, tailWord_5750588, baseEnd_5750588] using wordTrace_append hprefix tailTrace_5750588
  have hstable : (prefixWord ++ tailWord_5750588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750588).length < 2 ^ (prefixWord ++ tailWord_5750588).sum := by decide
  have hdescent : baseEnd_5750588 < baseStart_5750588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750625 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_5750625 : Nat := 118140960795 + 5750625 * 2 ^ 59
def prefixEnd_5750625 : Nat := 4983230072969 + 3 ^ 40 * 5750625 * 2
def baseEnd_5750625 : Nat := 2952834688761668386940863

theorem tailTrace_5750625 : CollatzResearch.WordTrace tailWord_5750625 prefixEnd_5750625 2952834688761668386940863 := by
  unfold tailWord_5750625
  simp only [CollatzResearch.WordTrace]
  refine ⟨209742524791475228403861329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139828349860983485602574219 209742524791475228403861329)
  ·
    refine ⟨157306893593606421302895997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209742524791475228403861329 157306893593606421302895997)
    ·
      refine ⟨58990085097602407988585999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157306893593606421302895997 58990085097602407988585999)
      ·
        refine ⟨88485127646403611982878999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58990085097602407988585999 88485127646403611982878999)
        ·
          refine ⟨132727691469605417974318499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88485127646403611982878999 132727691469605417974318499)
          ·
            refine ⟨199091537204408126961477749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132727691469605417974318499 199091537204408126961477749)
            ·
              refine ⟨18664831612913261902638539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199091537204408126961477749 18664831612913261902638539)
              ·
                refine ⟨27997247419369892853957809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18664831612913261902638539 27997247419369892853957809)
                ·
                  refine ⟨20997935564527419640468357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27997247419369892853957809 20997935564527419640468357)
                  ·
                    refine ⟨3937112918348891182587817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20997935564527419640468357 3937112918348891182587817)
                    ·
                      refine ⟨2952834688761668386940863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937112918348891182587817 2952834688761668386940863)
                      ·
                        rfl

theorem cell23_5750625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_5750625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750625 prefixEnd_5750625 := by exact prefixLift 5750625
  have htrace : WordTrace (prefixWord ++ tailWord_5750625) baseStart_5750625 baseEnd_5750625 := by
    simpa [prefixWord, tailWord_5750625, baseEnd_5750625] using wordTrace_append hprefix tailTrace_5750625
  have hstable : (prefixWord ++ tailWord_5750625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750625).length < 2 ^ (prefixWord ++ tailWord_5750625).sum := by decide
  have hdescent : baseEnd_5750625 < baseStart_5750625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750645 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5750645 : Nat := 118140960795 + 5750645 * 2 ^ 59
def prefixEnd_5750645 : Nat := 4983230072969 + 3 ^ 40 * 5750645 * 2
def baseEnd_5750645 : Nat := 2952844958374758308690771

theorem tailTrace_5750645 : CollatzResearch.WordTrace tailWord_5750645 prefixEnd_5750645 2952844958374758308690771 := by
  unfold tailWord_5750645
  simp only [CollatzResearch.WordTrace]
  refine ⟨209743254251402771819589389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139828836167601847879726259 209743254251402771819589389)
  ·
    refine ⟨78653720344276039432346021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209743254251402771819589389 78653720344276039432346021)
    ·
      refine ⟨14747572564551757393564879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78653720344276039432346021 14747572564551757393564879)
      ·
        refine ⟨22121358846827636090347319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14747572564551757393564879 22121358846827636090347319)
        ·
          refine ⟨33182038270241454135520979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22121358846827636090347319 33182038270241454135520979)
          ·
            refine ⟨49773057405362181203281469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33182038270241454135520979 49773057405362181203281469)
            ·
              refine ⟨18664896527010817951230551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49773057405362181203281469 18664896527010817951230551)
              ·
                refine ⟨27997344790516226926845827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18664896527010817951230551 27997344790516226926845827)
                ·
                  refine ⟨41996017185774340390268741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27997344790516226926845827 41996017185774340390268741)
                  ·
                    refine ⟨7874253222332688823175389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41996017185774340390268741 7874253222332688823175389)
                    ·
                      refine ⟨2952844958374758308690771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874253222332688823175389 2952844958374758308690771)
                      ·
                        rfl

theorem cell23_5750645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5750645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750645 prefixEnd_5750645 := by exact prefixLift 5750645
  have htrace : WordTrace (prefixWord ++ tailWord_5750645) baseStart_5750645 baseEnd_5750645 := by
    simpa [prefixWord, tailWord_5750645, baseEnd_5750645] using wordTrace_append hprefix tailTrace_5750645
  have hstable : (prefixWord ++ tailWord_5750645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750645).length < 2 ^ (prefixWord ++ tailWord_5750645).sum := by decide
  have hdescent : baseEnd_5750645 < baseStart_5750645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750682 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_5750682 : Nat := 118140960795 + 5750682 * 2 ^ 59
def prefixEnd_5750682 : Nat := 4983230072969 + 3 ^ 40 * 5750682 * 2
def baseEnd_5750682 : Nat := 328095995239886073769789

theorem tailTrace_5750682 : CollatzResearch.WordTrace tailWord_5750682 prefixEnd_5750682 328095995239886073769789 := by
  unfold tailWord_5750682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52436150938067181784671575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139829735834845818092457533 52436150938067181784671575)
  ·
    refine ⟨78654226407100772677007363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52436150938067181784671575 78654226407100772677007363)
    ·
      refine ⟨117981339610651159015511045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78654226407100772677007363 117981339610651159015511045)
      ·
        refine ⟨22121501176997092315408321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117981339610651159015511045 22121501176997092315408321)
        ·
          refine ⟨16591125882747819236556241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22121501176997092315408321 16591125882747819236556241)
          ·
            refine ⟨12443344412060864427417181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16591125882747819236556241 12443344412060864427417181)
            ·
              refine ⟨4666254154522824160281443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12443344412060864427417181 4666254154522824160281443)
              ·
                refine ⟨6999381231784236240422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666254154522824160281443 6999381231784236240422165)
                ·
                  refine ⟨328095995239886073769789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6999381231784236240422165 328095995239886073769789)
                  ·
                    rfl

theorem cell23_5750682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_5750682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750682 prefixEnd_5750682 := by exact prefixLift 5750682
  have htrace : WordTrace (prefixWord ++ tailWord_5750682) baseStart_5750682 baseEnd_5750682 := by
    simpa [prefixWord, tailWord_5750682, baseEnd_5750682] using wordTrace_append hprefix tailTrace_5750682
  have hstable : (prefixWord ++ tailWord_5750682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750682).length < 2 ^ (prefixWord ++ tailWord_5750682).sum := by decide
  have hdescent : baseEnd_5750682 < baseStart_5750682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750692 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_5750692 : Nat := 118140960795 + 5750692 * 2 ^ 59
def prefixEnd_5750692 : Nat := 4983230072969 + 3 ^ 40 * 5750692 * 2
def baseEnd_5750692 : Nat := 2952869091965519624803055

theorem tailTrace_5750692 : CollatzResearch.WordTrace tailWord_5750692 prefixEnd_5750692 2952869091965519624803055 := by
  unfold tailWord_5750692
  simp only [CollatzResearch.WordTrace]
  refine ⟨104872484241116249423275165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139829978988154999231033553 104872484241116249423275165)
  ·
    refine ⟨39327181590418593533728187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104872484241116249423275165 39327181590418593533728187)
    ·
      refine ⟨58990772385627890300592281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39327181590418593533728187 58990772385627890300592281)
      ·
        refine ⟨44243079289220917725444211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58990772385627890300592281 44243079289220917725444211)
        ·
          refine ⟨66364618933831376588166317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44243079289220917725444211 66364618933831376588166317)
          ·
            refine ⟨24886732100186766220562369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66364618933831376588166317 24886732100186766220562369)
            ·
              refine ⟨18665049075140074665421777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24886732100186766220562369 18665049075140074665421777)
              ·
                refine ⟨13998786806355055999066333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18665049075140074665421777 13998786806355055999066333)
                ·
                  refine ⟨5249545052383145999649875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998786806355055999066333 5249545052383145999649875)
                  ·
                    refine ⟨7874317578574718999474813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5249545052383145999649875 7874317578574718999474813)
                    ·
                      refine ⟨2952869091965519624803055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874317578574718999474813 2952869091965519624803055)
                      ·
                        rfl

theorem cell23_5750692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_5750692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750692 prefixEnd_5750692 := by exact prefixLift 5750692
  have htrace : WordTrace (prefixWord ++ tailWord_5750692) baseStart_5750692 baseEnd_5750692 := by
    simpa [prefixWord, tailWord_5750692, baseEnd_5750692] using wordTrace_append hprefix tailTrace_5750692
  have hstable : (prefixWord ++ tailWord_5750692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750692).length < 2 ^ (prefixWord ++ tailWord_5750692).sum := by decide
  have hdescent : baseEnd_5750692 < baseStart_5750692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750735 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_5750735 : Nat := 118140960795 + 5750735 * 2 ^ 59
def prefixEnd_5750735 : Nat := 4983230072969 + 3 ^ 40 * 5750735 * 2
def baseEnd_5750735 : Nat := 2952891171633662956565357

theorem tailTrace_5750735 : CollatzResearch.WordTrace tailWord_5750735 prefixEnd_5750735 2952891171633662956565357 := by
  unfold tailWord_5750735
  simp only [CollatzResearch.WordTrace]
  refine ⟨209746536821076717190365659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139831024547384478126910439 209746536821076717190365659)
  ·
    refine ⟨314619805231615075785548489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209746536821076717190365659 314619805231615075785548489)
    ·
      refine ⟨235964853923711306839161367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314619805231615075785548489 235964853923711306839161367)
      ·
        refine ⟨353947280885566960258742051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235964853923711306839161367 353947280885566960258742051)
        ·
          refine ⟨530920921328350440388113077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353947280885566960258742051 530920921328350440388113077)
          ·
            refine ⟨49773836374532853786385601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 530920921328350440388113077 49773836374532853786385601)
            ·
              refine ⟨37330377280899640339789201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49773836374532853786385601 37330377280899640339789201)
              ·
                refine ⟨27997782960674730254841901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37330377280899640339789201 27997782960674730254841901)
                ·
                  refine ⟨10499168610253023845565713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27997782960674730254841901 10499168610253023845565713)
                  ·
                    refine ⟨7874376457689767884174285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10499168610253023845565713 7874376457689767884174285)
                    ·
                      refine ⟨2952891171633662956565357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874376457689767884174285 2952891171633662956565357)
                      ·
                        rfl

theorem cell23_5750735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_5750735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750735 prefixEnd_5750735 := by exact prefixLift 5750735
  have htrace : WordTrace (prefixWord ++ tailWord_5750735) baseStart_5750735 baseEnd_5750735 := by
    simpa [prefixWord, tailWord_5750735, baseEnd_5750735] using wordTrace_append hprefix tailTrace_5750735
  have hstable : (prefixWord ++ tailWord_5750735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750735).length < 2 ^ (prefixWord ++ tailWord_5750735).sum := by decide
  have hdescent : baseEnd_5750735 < baseStart_5750735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750769 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_5750769 : Nat := 118140960795 + 5750769 * 2 ^ 59
def prefixEnd_5750769 : Nat := 4983230072969 + 3 ^ 40 * 5750769 * 2
def baseEnd_5750769 : Nat := 2952908629975915823540201

theorem tailTrace_5750769 : CollatzResearch.WordTrace tailWord_5750769 prefixEnd_5750769 2952908629975915823540201 := by
  unfold tailWord_5750769
  simp only [CollatzResearch.WordTrace]
  refine ⟨209747776902953540997103361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139831851268635693998068907 209747776902953540997103361)
  ·
    refine ⟨157310832677215155747827521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209747776902953540997103361 157310832677215155747827521)
    ·
      refine ⟨117983124507911366810870641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157310832677215155747827521 117983124507911366810870641)
      ·
        refine ⟨88487343380933525108152981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117983124507911366810870641 88487343380933525108152981)
        ·
          refine ⟨4147844220981258989444671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88487343380933525108152981 4147844220981258989444671)
          ·
            refine ⟨6221766331471888484167007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147844220981258989444671 6221766331471888484167007)
            ·
              refine ⟨9332649497207832726250511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221766331471888484167007 9332649497207832726250511)
              ·
                refine ⟨13998974245811749089375767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9332649497207832726250511 13998974245811749089375767)
                ·
                  refine ⟨20998461368717623634063651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13998974245811749089375767 20998461368717623634063651)
                  ·
                    refine ⟨31497692053076435451095477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20998461368717623634063651 31497692053076435451095477)
                    ·
                      refine ⟨2952908629975915823540201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31497692053076435451095477 2952908629975915823540201)
                      ·
                        rfl

theorem cell23_5750769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_5750769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750769 prefixEnd_5750769 := by exact prefixLift 5750769
  have htrace : WordTrace (prefixWord ++ tailWord_5750769) baseStart_5750769 baseEnd_5750769 := by
    simpa [prefixWord, tailWord_5750769, baseEnd_5750769] using wordTrace_append hprefix tailTrace_5750769
  have hstable : (prefixWord ++ tailWord_5750769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750769).length < 2 ^ (prefixWord ++ tailWord_5750769).sum := by decide
  have hdescent : baseEnd_5750769 < baseStart_5750769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750772 : List Nat := [2, 6, 2, 13]
def baseStart_5750772 : Nat := 118140960795 + 5750772 * 2 ^ 59
def prefixEnd_5750772 : Nat := 4983230072969 + 3 ^ 40 * 5750772 * 2
def baseEnd_5750772 : Nat := 1350210411713707961501

theorem tailTrace_5750772 : CollatzResearch.WordTrace tailWord_5750772 prefixEnd_5750772 1350210411713707961501 := by
  unfold tailWord_5750772
  simp only [CollatzResearch.WordTrace]
  refine ⟨104873943160971336254731285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139831924214628448339641713 104873943160971336254731285)
  ·
    refine ⟨4915966085670531386940529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104873943160971336254731285 4915966085670531386940529)
    ·
      refine ⟨3686974564252898540205397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915966085670531386940529 3686974564252898540205397)
      ·
        refine ⟨1350210411713707961501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3686974564252898540205397 1350210411713707961501)
        ·
          rfl

theorem cell23_5750772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 13].length) (baseStart_5750772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750772 prefixEnd_5750772 := by exact prefixLift 5750772
  have htrace : WordTrace (prefixWord ++ tailWord_5750772) baseStart_5750772 baseEnd_5750772 := by
    simpa [prefixWord, tailWord_5750772, baseEnd_5750772] using wordTrace_append hprefix tailTrace_5750772
  have hstable : (prefixWord ++ tailWord_5750772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750772).length < 2 ^ (prefixWord ++ tailWord_5750772).sum := by decide
  have hdescent : baseEnd_5750772 < baseStart_5750772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750778 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_5750778 : Nat := 118140960795 + 5750778 * 2 ^ 59
def prefixEnd_5750778 : Nat := 4983230072969 + 3 ^ 40 * 5750778 * 2
def baseEnd_5750778 : Nat := 2952913251301806288327659

theorem tailTrace_5750778 : CollatzResearch.WordTrace tailWord_5750778 prefixEnd_5750778 2952913251301806288327659 := by
  unfold tailWord_5750778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52437026289980233883545247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139832070106613957022787325 52437026289980233883545247)
  ·
    refine ⟨78655539434970350825317871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52437026289980233883545247 78655539434970350825317871)
    ·
      refine ⟨117983309152455526237976807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78655539434970350825317871 117983309152455526237976807)
      ·
        refine ⟨176974963728683289356965211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117983309152455526237976807 176974963728683289356965211)
        ·
          refine ⟨265462445593024934035447817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176974963728683289356965211 265462445593024934035447817)
          ·
            refine ⟨199096834194768700526585863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265462445593024934035447817 199096834194768700526585863)
            ·
              refine ⟨298645251292153050789878795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199096834194768700526585863 298645251292153050789878795)
              ·
                refine ⟨447967876938229576184818193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298645251292153050789878795 447967876938229576184818193)
                ·
                  refine ⟨335975907703672182138613645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447967876938229576184818193 335975907703672182138613645)
                  ·
                    refine ⟨125990965388877068301980117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335975907703672182138613645 125990965388877068301980117)
                    ·
                      refine ⟨2952913251301806288327659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125990965388877068301980117 2952913251301806288327659)
                      ·
                        rfl

theorem cell23_5750778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_5750778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750778 prefixEnd_5750778 := by exact prefixLift 5750778
  have htrace : WordTrace (prefixWord ++ tailWord_5750778) baseStart_5750778 baseEnd_5750778 := by
    simpa [prefixWord, tailWord_5750778, baseEnd_5750778] using wordTrace_append hprefix tailTrace_5750778
  have hstable : (prefixWord ++ tailWord_5750778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750778).length < 2 ^ (prefixWord ++ tailWord_5750778).sum := by decide
  have hdescent : baseEnd_5750778 < baseStart_5750778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750792 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_5750792 : Nat := 118140960795 + 5750792 * 2 ^ 59
def prefixEnd_5750792 : Nat := 4983230072969 + 3 ^ 40 * 5750792 * 2
def baseEnd_5750792 : Nat := 2952920440030969233552595

theorem tailTrace_5750792 : CollatzResearch.WordTrace tailWord_5750792 prefixEnd_5750792 2952920440030969233552595 := by
  unfold tailWord_5750792
  simp only [CollatzResearch.WordTrace]
  refine ⟨104874307890935107962595315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139832410521246810616793753 104874307890935107962595315)
  ·
    refine ⟨157311461836402661943892973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104874307890935107962595315 157311461836402661943892973)
    ·
      refine ⟨58991798188650998228959865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157311461836402661943892973 58991798188650998228959865)
      ·
        refine ⟨44243848641488248671719899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58991798188650998228959865 44243848641488248671719899)
        ·
          refine ⟨66365772962232373007579849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44243848641488248671719899 66365772962232373007579849)
          ·
            refine ⟨49774329721674279755684887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66365772962232373007579849 49774329721674279755684887)
            ·
              refine ⟨74661494582511419633527331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49774329721674279755684887 74661494582511419633527331)
              ·
                refine ⟨111992241873767129450290997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74661494582511419633527331 111992241873767129450290997)
                ·
                  refine ⟨10499272675665668385964781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111992241873767129450290997 10499272675665668385964781)
                  ·
                    refine ⟨3937227253374625644736793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10499272675665668385964781 3937227253374625644736793)
                    ·
                      refine ⟨2952920440030969233552595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937227253374625644736793 2952920440030969233552595)
                      ·
                        rfl

theorem cell23_5750792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_5750792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750792 prefixEnd_5750792 := by exact prefixLift 5750792
  have htrace : WordTrace (prefixWord ++ tailWord_5750792) baseStart_5750792 baseEnd_5750792 := by
    simpa [prefixWord, tailWord_5750792, baseEnd_5750792] using wordTrace_append hprefix tailTrace_5750792
  have hstable : (prefixWord ++ tailWord_5750792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750792).length < 2 ^ (prefixWord ++ tailWord_5750792).sum := by decide
  have hdescent : baseEnd_5750792 < baseStart_5750792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750826 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5750826 : Nat := 118140960795 + 5750826 * 2 ^ 59
def prefixEnd_5750826 : Nat := 4983230072969 + 3 ^ 40 * 5750826 * 2
def baseEnd_5750826 : Nat := 2952937898373222100527439

theorem tailTrace_5750826 : CollatzResearch.WordTrace tailWord_5750826 prefixEnd_5750826 2952937898373222100527439 := by
  unfold tailWord_5750826
  simp only [CollatzResearch.WordTrace]
  refine ⟨52437463965936759932982083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139833237242498026487952221 52437463965936759932982083)
  ·
    refine ⟨78656195948905139899473125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52437463965936759932982083 78656195948905139899473125)
    ·
      refine ⟨14748036740419713731151211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78656195948905139899473125 14748036740419713731151211)
      ·
        refine ⟨22122055110629570596726817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14748036740419713731151211 22122055110629570596726817)
        ·
          refine ⟨16591541332972177947545113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22122055110629570596726817 16591541332972177947545113)
          ·
            refine ⟨12443655999729133460658835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16591541332972177947545113 12443655999729133460658835)
            ·
              refine ⟨18665483999593700190988253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12443655999729133460658835 18665483999593700190988253)
              ·
                refine ⟨6999556499847637571620595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18665483999593700190988253 6999556499847637571620595)
                ·
                  refine ⟨10499334749771456357430893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6999556499847637571620595 10499334749771456357430893)
                  ·
                    refine ⟨3937250531164296134036585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10499334749771456357430893 3937250531164296134036585)
                    ·
                      refine ⟨2952937898373222100527439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937250531164296134036585 2952937898373222100527439)
                      ·
                        rfl

theorem cell23_5750826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5750826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750826 prefixEnd_5750826 := by exact prefixLift 5750826
  have htrace : WordTrace (prefixWord ++ tailWord_5750826) baseStart_5750826 baseEnd_5750826 := by
    simpa [prefixWord, tailWord_5750826, baseEnd_5750826] using wordTrace_append hprefix tailTrace_5750826
  have hstable : (prefixWord ++ tailWord_5750826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750826).length < 2 ^ (prefixWord ++ tailWord_5750826).sum := by decide
  have hdescent : baseEnd_5750826 < baseStart_5750826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750835 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_5750835 : Nat := 118140960795 + 5750835 * 2 ^ 59
def prefixEnd_5750835 : Nat := 4983230072969 + 3 ^ 40 * 5750835 * 2
def baseEnd_5750835 : Nat := 2952942519699112565314897

theorem tailTrace_5750835 : CollatzResearch.WordTrace tailWord_5750835 prefixEnd_5750835 2952942519699112565314897 := by
  unfold tailWord_5750835
  simp only [CollatzResearch.WordTrace]
  refine ⟨209750184120714434269005959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139833456080476289512670639 209750184120714434269005959)
  ·
    refine ⟨314625276181071651403508939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209750184120714434269005959 314625276181071651403508939)
    ·
      refine ⟨471937914271607477105263409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314625276181071651403508939 471937914271607477105263409)
      ·
        refine ⟨353953435703705607828947557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471937914271607477105263409 353953435703705607828947557)
        ·
          refine ⟨66366269194444801467927667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353953435703705607828947557 66366269194444801467927667)
          ·
            refine ⟨99549403791667202201891501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66366269194444801467927667 99549403791667202201891501)
            ·
              refine ⟨37331026421875200825709313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99549403791667202201891501 37331026421875200825709313)
              ·
                refine ⟨27998269816406400619281985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37331026421875200825709313 27998269816406400619281985)
                ·
                  refine ⟨20998702362304800464461489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27998269816406400619281985 20998702362304800464461489)
                  ·
                    refine ⟨15749026771728600348346117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20998702362304800464461489 15749026771728600348346117)
                    ·
                      refine ⟨2952942519699112565314897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15749026771728600348346117 2952942519699112565314897)
                      ·
                        rfl

theorem cell23_5750835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_5750835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750835 prefixEnd_5750835 := by exact prefixLift 5750835
  have htrace : WordTrace (prefixWord ++ tailWord_5750835) baseStart_5750835 baseEnd_5750835 := by
    simpa [prefixWord, tailWord_5750835, baseEnd_5750835] using wordTrace_append hprefix tailTrace_5750835
  have hstable : (prefixWord ++ tailWord_5750835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750835).length < 2 ^ (prefixWord ++ tailWord_5750835).sum := by decide
  have hdescent : baseEnd_5750835 < baseStart_5750835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750892 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_5750892 : Nat := 118140960795 + 5750892 * 2 ^ 59
def prefixEnd_5750892 : Nat := 4983230072969 + 3 ^ 40 * 5750892 * 2
def baseEnd_5750892 : Nat := 984323929365472947434045

theorem tailTrace_5750892 : CollatzResearch.WordTrace tailWord_5750892 prefixEnd_5750892 984323929365472947434045 := by
  unfold tailWord_5750892
  simp only [CollatzResearch.WordTrace]
  refine ⟨104876131540753966501915465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139834842054338622002553953 104876131540753966501915465)
  ·
    refine ⟨78657098655565474876436599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104876131540753966501915465 78657098655565474876436599)
    ·
      refine ⟨117985647983348212314654899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78657098655565474876436599 117985647983348212314654899)
      ·
        refine ⟨176978471975022318471982349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117985647983348212314654899 176978471975022318471982349)
        ·
          refine ⟨66366926990633369426993381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176978471975022318471982349 66366926990633369426993381)
          ·
            refine ⟨12443798810743756767561259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66366926990633369426993381 12443798810743756767561259)
            ·
              refine ⟨18665698216115635151341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12443798810743756767561259 18665698216115635151341889)
              ·
                refine ⟨13999273662086726363506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18665698216115635151341889 13999273662086726363506417)
                ·
                  refine ⟨10499455246565044772629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13999273662086726363506417 10499455246565044772629813)
                  ·
                    refine ⟨984323929365472947434045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10499455246565044772629813 984323929365472947434045)
                    ·
                      rfl

theorem cell23_5750892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_5750892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750892 prefixEnd_5750892 := by exact prefixLift 5750892
  have htrace : WordTrace (prefixWord ++ tailWord_5750892) baseStart_5750892 baseEnd_5750892 := by
    simpa [prefixWord, tailWord_5750892, baseEnd_5750892] using wordTrace_append hprefix tailTrace_5750892
  have hstable : (prefixWord ++ tailWord_5750892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750892).length < 2 ^ (prefixWord ++ tailWord_5750892).sum := by decide
  have hdescent : baseEnd_5750892 < baseStart_5750892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750902 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5750902 : Nat := 118140960795 + 5750902 * 2 ^ 59
def prefixEnd_5750902 : Nat := 4983230072969 + 3 ^ 40 * 5750902 * 2
def baseEnd_5750902 : Nat := 2952976922902963803177089

theorem tailTrace_5750902 : CollatzResearch.WordTrace tailWord_5750902 prefixEnd_5750902 2952976922902963803177089 := by
  unfold tailWord_5750902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109539238216981544480935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139835085207647803141129973 13109539238216981544480935)
  ·
    refine ⟨19664308857325472316721403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13109539238216981544480935 19664308857325472316721403)
    ·
      refine ⟨29496463285988208475082105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19664308857325472316721403 29496463285988208475082105)
      ·
        refine ⟨22122347464491156356311579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29496463285988208475082105 22122347464491156356311579)
        ·
          refine ⟨33183521196736734534467369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22122347464491156356311579 33183521196736734534467369)
          ·
            refine ⟨24887640897552550900850527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33183521196736734534467369 24887640897552550900850527)
            ·
              refine ⟨37331461346328826351275791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24887640897552550900850527 37331461346328826351275791)
              ·
                refine ⟨55997192019493239526913687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37331461346328826351275791 55997192019493239526913687)
                ·
                  refine ⟨83995788029239859290370531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55997192019493239526913687 83995788029239859290370531)
                  ·
                    refine ⟨125993682043859788935555797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83995788029239859290370531 125993682043859788935555797)
                    ·
                      refine ⟨2952976922902963803177089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125993682043859788935555797 2952976922902963803177089)
                      ·
                        rfl

theorem cell23_5750902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5750902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750902 prefixEnd_5750902 := by exact prefixLift 5750902
  have htrace : WordTrace (prefixWord ++ tailWord_5750902) baseStart_5750902 baseEnd_5750902 := by
    simpa [prefixWord, tailWord_5750902, baseEnd_5750902] using wordTrace_append hprefix tailTrace_5750902
  have hstable : (prefixWord ++ tailWord_5750902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750902).length < 2 ^ (prefixWord ++ tailWord_5750902).sum := by decide
  have hdescent : baseEnd_5750902 < baseStart_5750902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750912 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2]
def baseStart_5750912 : Nat := 118140960795 + 5750912 * 2 ^ 59
def prefixEnd_5750912 : Nat := 4983230072969 + 3 ^ 40 * 5750912 * 2
def baseEnd_5750912 : Nat := 2952982057709508764052043

theorem tailTrace_5750912 : CollatzResearch.WordTrace tailWord_5750912 prefixEnd_5750912 2952982057709508764052043 := by
  unfold tailWord_5750912
  simp only [CollatzResearch.WordTrace]
  refine ⟨104876496270717738209779495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139835328360956984279705993 104876496270717738209779495)
  ·
    refine ⟨157314744406076607314669243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104876496270717738209779495 157314744406076607314669243)
    ·
      refine ⟨235972116609114910972003865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157314744406076607314669243 235972116609114910972003865)
      ·
        refine ⟨176979087456836183229002899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235972116609114910972003865 176979087456836183229002899)
        ·
          refine ⟨265468631185254274843504349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176979087456836183229002899 265468631185254274843504349)
          ·
            refine ⟨99550736694470353066314131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265468631185254274843504349 99550736694470353066314131)
            ·
              refine ⟨149326105041705529599471197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99550736694470353066314131 149326105041705529599471197)
              ·
                refine ⟨55997289390639573599801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149326105041705529599471197 55997289390639573599801699)
                ·
                  refine ⟨83995934085959360399702549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55997289390639573599801699 83995934085959360399702549)
                  ·
                    refine ⟨3937309410279345018736057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83995934085959360399702549 3937309410279345018736057)
                    ·
                      refine ⟨2952982057709508764052043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937309410279345018736057 2952982057709508764052043)
                      ·
                        rfl

theorem cell23_5750912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_5750912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750912 prefixEnd_5750912 := by exact prefixLift 5750912
  have htrace : WordTrace (prefixWord ++ tailWord_5750912) baseStart_5750912 baseEnd_5750912 := by
    simpa [prefixWord, tailWord_5750912, baseEnd_5750912] using wordTrace_append hprefix tailTrace_5750912
  have hstable : (prefixWord ++ tailWord_5750912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750912).length < 2 ^ (prefixWord ++ tailWord_5750912).sum := by decide
  have hdescent : baseEnd_5750912 < baseStart_5750912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5750975 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_5750975 : Nat := 118140960795 + 5750975 * 2 ^ 59
def prefixEnd_5750975 : Nat := 4983230072969 + 3 ^ 40 * 5750975 * 2
def baseEnd_5750975 : Nat := 2953014406990742017564253

theorem tailTrace_5750975 : CollatzResearch.WordTrace tailWord_5750975 prefixEnd_5750975 2953014406990742017564253 := by
  unfold tailWord_5750975
  simp only [CollatzResearch.WordTrace]
  refine ⟨209755290340207238179102379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139836860226804825452734919 209755290340207238179102379)
  ·
    refine ⟨314632935510310857268653569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209755290340207238179102379 314632935510310857268653569)
    ·
      refine ⟨235974701632733142951490177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314632935510310857268653569 235974701632733142951490177)
      ·
        refine ⟨176981026224549857213617633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235974701632733142951490177 176981026224549857213617633)
        ·
          refine ⟨132735769668412392910213225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176981026224549857213617633 132735769668412392910213225)
          ·
            refine ⟨99551827251309294682659919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132735769668412392910213225 99551827251309294682659919)
            ·
              refine ⟨149327740876963942023989879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99551827251309294682659919 149327740876963942023989879)
              ·
                refine ⟨223991611315445913035984819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149327740876963942023989879 223991611315445913035984819)
                ·
                  refine ⟨335987416973168869553977229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223991611315445913035984819 335987416973168869553977229)
                  ·
                    refine ⟨125995281364938326082741461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335987416973168869553977229 125995281364938326082741461)
                    ·
                      refine ⟨2953014406990742017564253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125995281364938326082741461 2953014406990742017564253)
                      ·
                        rfl

theorem cell23_5750975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_5750975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5750975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5750975 prefixEnd_5750975 := by exact prefixLift 5750975
  have htrace : WordTrace (prefixWord ++ tailWord_5750975) baseStart_5750975 baseEnd_5750975 := by
    simpa [prefixWord, tailWord_5750975, baseEnd_5750975] using wordTrace_append hprefix tailTrace_5750975
  have hstable : (prefixWord ++ tailWord_5750975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5750975).length < 2 ^ (prefixWord ++ tailWord_5750975).sum := by decide
  have hdescent : baseEnd_5750975 < baseStart_5750975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5750975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751013 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5751013 : Nat := 118140960795 + 5751013 * 2 ^ 59
def prefixEnd_5751013 : Nat := 4983230072969 + 3 ^ 40 * 5751013 * 2
def baseEnd_5751013 : Nat := 2953033919255612868889079

theorem tailTrace_5751013 : CollatzResearch.WordTrace tailWord_5751013 prefixEnd_5751013 2953033919255612868889079 := by
  unfold tailWord_5751013
  simp only [CollatzResearch.WordTrace]
  refine ⟨209756676314069570668985693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139837784209379713779323795 209756676314069570668985693)
  ·
    refine ⟨78658753617776089000869635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209756676314069570668985693 78658753617776089000869635)
    ·
      refine ⟨117988130426664133501304453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78658753617776089000869635 117988130426664133501304453)
      ·
        refine ⟨22122774454999525031494585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117988130426664133501304453 22122774454999525031494585)
        ·
          refine ⟨16592080841249643773620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22122774454999525031494585 16592080841249643773620939)
          ·
            refine ⟨24888121261874465660431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16592080841249643773620939 24888121261874465660431409)
            ·
              refine ⟨18666090946405849245323557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24888121261874465660431409 18666090946405849245323557)
              ·
                refine ⟨3499892052451096733498167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18666090946405849245323557 3499892052451096733498167)
                ·
                  refine ⟨5249838078676645100247251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499892052451096733498167 5249838078676645100247251)
                  ·
                    refine ⟨7874757118014967650370877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5249838078676645100247251 7874757118014967650370877)
                    ·
                      refine ⟨2953033919255612868889079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874757118014967650370877 2953033919255612868889079)
                      ·
                        rfl

theorem cell23_5751013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5751013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751013 prefixEnd_5751013 := by exact prefixLift 5751013
  have htrace : WordTrace (prefixWord ++ tailWord_5751013) baseStart_5751013 baseEnd_5751013 := by
    simpa [prefixWord, tailWord_5751013, baseEnd_5751013] using wordTrace_append hprefix tailTrace_5751013
  have hstable : (prefixWord ++ tailWord_5751013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751013).length < 2 ^ (prefixWord ++ tailWord_5751013).sum := by decide
  have hdescent : baseEnd_5751013 < baseStart_5751013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751036 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_5751036 : Nat := 118140960795 + 5751036 * 2 ^ 59
def prefixEnd_5751036 : Nat := 4983230072969 + 3 ^ 40 * 5751036 * 2
def baseEnd_5751036 : Nat := 2953045729310666278901473

theorem tailTrace_5751036 : CollatzResearch.WordTrace tailWord_5751036 prefixEnd_5751036 2953045729310666278901473 := by
  unfold tailWord_5751036
  simp only [CollatzResearch.WordTrace]
  refine ⟨104878757596493122798536481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139838343461990830398048641 104878757596493122798536481)
  ·
    refine ⟨78659068197369842098902361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104878757596493122798536481 78659068197369842098902361)
    ·
      refine ⟨58994301148027381574176771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78659068197369842098902361 58994301148027381574176771)
      ·
        refine ⟨88491451722041072361265157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58994301148027381574176771 88491451722041072361265157)
        ·
          refine ⟨16592147197882701067737217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88491451722041072361265157 16592147197882701067737217)
          ·
            refine ⟨12444110398412025800802913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16592147197882701067737217 12444110398412025800802913)
            ·
              refine ⟨9333082798809019350602185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12444110398412025800802913 9333082798809019350602185)
              ·
                refine ⟨6999812099106764512951639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9333082798809019350602185 6999812099106764512951639)
                ·
                  refine ⟨10499718148660146769427459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6999812099106764512951639 10499718148660146769427459)
                  ·
                    refine ⟨15749577222990220154141189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10499718148660146769427459 15749577222990220154141189)
                    ·
                      refine ⟨2953045729310666278901473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15749577222990220154141189 2953045729310666278901473)
                      ·
                        rfl

theorem cell23_5751036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_5751036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751036 prefixEnd_5751036 := by exact prefixLift 5751036
  have htrace : WordTrace (prefixWord ++ tailWord_5751036) baseStart_5751036 baseEnd_5751036 := by
    simpa [prefixWord, tailWord_5751036, baseEnd_5751036] using wordTrace_append hprefix tailTrace_5751036
  have hstable : (prefixWord ++ tailWord_5751036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751036).length < 2 ^ (prefixWord ++ tailWord_5751036).sum := by decide
  have hdescent : baseEnd_5751036 < baseStart_5751036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751047 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5751047 : Nat := 118140960795 + 5751047 * 2 ^ 59
def prefixEnd_5751047 : Nat := 4983230072969 + 3 ^ 40 * 5751047 * 2
def baseEnd_5751047 : Nat := 2953051377597865735863923

theorem tailTrace_5751047 : CollatzResearch.WordTrace tailWord_5751047 prefixEnd_5751047 2953051377597865735863923 := by
  unfold tailWord_5751047
  simp only [CollatzResearch.WordTrace]
  refine ⟨209757916395946394475723395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139838610930630929650482263 209757916395946394475723395)
  ·
    refine ⟨314636874593919591713585093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209757916395946394475723395 314636874593919591713585093)
    ·
      refine ⟨58994413986359923446297205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314636874593919591713585093 58994413986359923446297205)
      ·
        refine ⟨5530726311221242823090363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58994413986359923446297205 5530726311221242823090363)
        ·
          refine ⟨8296089466831864234635545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530726311221242823090363 8296089466831864234635545)
          ·
            refine ⟨6222067100123898175976659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296089466831864234635545 6222067100123898175976659)
            ·
              refine ⟨9333100650185847263964989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222067100123898175976659 9333100650185847263964989)
              ·
                refine ⟨3499912743819692723986871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9333100650185847263964989 3499912743819692723986871)
                ·
                  refine ⟨5249869115729539085980307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499912743819692723986871 5249869115729539085980307)
                  ·
                    refine ⟨7874803673594308628970461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5249869115729539085980307 7874803673594308628970461)
                    ·
                      refine ⟨2953051377597865735863923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874803673594308628970461 2953051377597865735863923)
                      ·
                        rfl

theorem cell23_5751047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5751047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751047 prefixEnd_5751047 := by exact prefixLift 5751047
  have htrace : WordTrace (prefixWord ++ tailWord_5751047) baseStart_5751047 baseEnd_5751047 := by
    simpa [prefixWord, tailWord_5751047, baseEnd_5751047] using wordTrace_append hprefix tailTrace_5751047
  have hstable : (prefixWord ++ tailWord_5751047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751047).length < 2 ^ (prefixWord ++ tailWord_5751047).sum := by decide
  have hdescent : baseEnd_5751047 < baseStart_5751047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751080 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5751080 : Nat := 118140960795 + 5751080 * 2 ^ 59
def prefixEnd_5751080 : Nat := 4983230072969 + 3 ^ 40 * 5751080 * 2
def baseEnd_5751080 : Nat := 984356107486488035583757

theorem tailTrace_5751080 : CollatzResearch.WordTrace tailWord_5751080 prefixEnd_5751080 984356107486488035583757 := by
  unfold tailWord_5751080
  simp only [CollatzResearch.WordTrace]
  refine ⟨104879560002413420555837347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139839413336551227407783129 104879560002413420555837347)
  ·
    refine ⟨157319340003620130833756021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104879560002413420555837347 157319340003620130833756021)
    ·
      refine ⟨14748688125339387265664627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157319340003620130833756021 14748688125339387265664627)
      ·
        refine ⟨22123032188009080898496941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14748688125339387265664627 22123032188009080898496941)
        ·
          refine ⟨8296137070503405336936353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22123032188009080898496941 8296137070503405336936353)
          ·
            refine ⟨6222102802877554002702265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296137070503405336936353 6222102802877554002702265)
            ·
              refine ⟨4666577102158165502026699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6222102802877554002702265 4666577102158165502026699)
              ·
                refine ⟨6999865653237248253040049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666577102158165502026699 6999865653237248253040049)
                ·
                  refine ⟨5249899239927936189780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6999865653237248253040049 5249899239927936189780037)
                  ·
                    refine ⟨984356107486488035583757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249899239927936189780037 984356107486488035583757)
                    ·
                      rfl

theorem cell23_5751080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5751080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751080 prefixEnd_5751080 := by exact prefixLift 5751080
  have htrace : WordTrace (prefixWord ++ tailWord_5751080) baseStart_5751080 baseEnd_5751080 := by
    simpa [prefixWord, tailWord_5751080, baseEnd_5751080] using wordTrace_append hprefix tailTrace_5751080
  have hstable : (prefixWord ++ tailWord_5751080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751080).length < 2 ^ (prefixWord ++ tailWord_5751080).sum := by decide
  have hdescent : baseEnd_5751080 < baseStart_5751080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751090 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_5751090 : Nat := 118140960795 + 5751090 * 2 ^ 59
def prefixEnd_5751090 : Nat := 4983230072969 + 3 ^ 40 * 5751090 * 2
def baseEnd_5751090 : Nat := 2953073457266009067626225

theorem tailTrace_5751090 : CollatzResearch.WordTrace tailWord_5751090 prefixEnd_5751090 2953073457266009067626225 := by
  unfold tailWord_5751090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52439871183697653204884681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139839656489860408546359149 52439871183697653204884681)
  ·
    refine ⟨39329903387773239903663511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52439871183697653204884681 39329903387773239903663511)
    ·
      refine ⟨58994855081659859855495267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39329903387773239903663511 58994855081659859855495267)
      ·
        refine ⟨88492282622489789783242901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58994855081659859855495267 88492282622489789783242901)
        ·
          refine ⟨4148075747929208896089511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88492282622489789783242901 4148075747929208896089511)
          ·
            refine ⟨6222113621893813344134267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148075747929208896089511 6222113621893813344134267)
            ·
              refine ⟨9333170432840720016201401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222113621893813344134267 9333170432840720016201401)
              ·
                refine ⟨6999877824630540012151051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9333170432840720016201401 6999877824630540012151051)
                ·
                  refine ⟨10499816736945810018226577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6999877824630540012151051 10499816736945810018226577)
                  ·
                    refine ⟨7874862552709357513669933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10499816736945810018226577 7874862552709357513669933)
                    ·
                      refine ⟨2953073457266009067626225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7874862552709357513669933 2953073457266009067626225)
                      ·
                        rfl

theorem cell23_5751090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_5751090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751090 prefixEnd_5751090 := by exact prefixLift 5751090
  have htrace : WordTrace (prefixWord ++ tailWord_5751090) baseStart_5751090 baseEnd_5751090 := by
    simpa [prefixWord, tailWord_5751090, baseEnd_5751090] using wordTrace_append hprefix tailTrace_5751090
  have hstable : (prefixWord ++ tailWord_5751090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751090).length < 2 ^ (prefixWord ++ tailWord_5751090).sum := by decide
  have hdescent : baseEnd_5751090 < baseStart_5751090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751139 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5751139 : Nat := 118140960795 + 5751139 * 2 ^ 59
def prefixEnd_5751139 : Nat := 4983230072969 + 3 ^ 40 * 5751139 * 2
def baseEnd_5751139 : Nat := 2953098617818079375913499

theorem tailTrace_5751139 : CollatzResearch.WordTrace tailWord_5751139 prefixEnd_5751139 2953098617818079375913499 := by
  unfold tailWord_5751139
  simp only [CollatzResearch.WordTrace]
  refine ⟨209761271911613094188072471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139840847941075396125381647 209761271911613094188072471)
  ·
    refine ⟨314641907867419641282108707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209761271911613094188072471 314641907867419641282108707)
    ·
      refine ⟨471962861801129461923163061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314641907867419641282108707 471962861801129461923163061)
      ·
        refine ⟨44246518293855887055296537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 471962861801129461923163061 44246518293855887055296537)
        ·
          refine ⟨33184888720391915291472403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44246518293855887055296537 33184888720391915291472403)
          ·
            refine ⟨49777333080587872937208605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33184888720391915291472403 49777333080587872937208605)
            ·
              refine ⟨18666499905220452351453227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49777333080587872937208605 18666499905220452351453227)
              ·
                refine ⟨27999749857830678527179841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18666499905220452351453227 27999749857830678527179841)
                ·
                  refine ⟨20999812393373008895384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27999749857830678527179841 20999812393373008895384881)
                  ·
                    refine ⟨15749859295029756671538661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20999812393373008895384881 15749859295029756671538661)
                    ·
                      refine ⟨2953098617818079375913499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15749859295029756671538661 2953098617818079375913499)
                      ·
                        rfl

theorem cell23_5751139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5751139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751139 prefixEnd_5751139 := by exact prefixLift 5751139
  have htrace : WordTrace (prefixWord ++ tailWord_5751139) baseStart_5751139 baseEnd_5751139 := by
    simpa [prefixWord, tailWord_5751139, baseEnd_5751139] using wordTrace_append hprefix tailTrace_5751139
  have hstable : (prefixWord ++ tailWord_5751139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751139).length < 2 ^ (prefixWord ++ tailWord_5751139).sum := by decide
  have hdescent : baseEnd_5751139 < baseStart_5751139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751143 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_5751143 : Nat := 118140960795 + 5751143 * 2 ^ 59
def prefixEnd_5751143 : Nat := 4983230072969 + 3 ^ 40 * 5751143 * 2
def baseEnd_5751143 : Nat := 2953100671740697360263481

theorem tailTrace_5751143 : CollatzResearch.WordTrace tailWord_5751143 prefixEnd_5751143 2953100671740697360263481 := by
  unfold tailWord_5751143
  simp only [CollatzResearch.WordTrace]
  refine ⟨209761417803598602871218083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139840945202399068580812055 209761417803598602871218083)
  ·
    refine ⟨314642126705397904306827125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209761417803598602871218083 314642126705397904306827125)
    ·
      refine ⟨29497699378631053528765043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314642126705397904306827125 29497699378631053528765043)
      ·
        refine ⟨44246549067946580293147565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29497699378631053528765043 44246549067946580293147565)
        ·
          refine ⟨16592455900479967609930337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44246549067946580293147565 16592455900479967609930337)
          ·
            refine ⟨12444341925359975707447753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16592455900479967609930337 12444341925359975707447753)
            ·
              refine ⟨9333256444019981780585815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12444341925359975707447753 9333256444019981780585815)
              ·
                refine ⟨13999884666029972670878723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333256444019981780585815 13999884666029972670878723)
                ·
                  refine ⟨20999826999044959006318085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13999884666029972670878723 20999826999044959006318085)
                  ·
                    refine ⟨3937467562320929813684641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20999826999044959006318085 3937467562320929813684641)
                    ·
                      refine ⟨2953100671740697360263481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937467562320929813684641 2953100671740697360263481)
                      ·
                        rfl

theorem cell23_5751143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_5751143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751143 prefixEnd_5751143 := by exact prefixLift 5751143
  have htrace : WordTrace (prefixWord ++ tailWord_5751143) baseStart_5751143 baseEnd_5751143 := by
    simpa [prefixWord, tailWord_5751143, baseEnd_5751143] using wordTrace_append hprefix tailTrace_5751143
  have hstable : (prefixWord ++ tailWord_5751143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751143).length < 2 ^ (prefixWord ++ tailWord_5751143).sum := by decide
  have hdescent : baseEnd_5751143 < baseStart_5751143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751149 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 7]
def baseStart_5751149 : Nat := 118140960795 + 5751149 * 2 ^ 59
def prefixEnd_5751149 : Nat := 4983230072969 + 3 ^ 40 * 5751149 * 2
def baseEnd_5751149 : Nat := 328122639180513815198717

theorem tailTrace_5751149 : CollatzResearch.WordTrace tailWord_5751149 prefixEnd_5751149 328122639180513815198717 := by
  unfold tailWord_5751149
  simp only [CollatzResearch.WordTrace]
  refine ⟨209761636641576865895936501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139841091094384577263957667 209761636641576865895936501)
  ·
    refine ⟨19665153435147831177744047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209761636641576865895936501 19665153435147831177744047)
    ·
      refine ⟨29497730152721746766616071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19665153435147831177744047 29497730152721746766616071)
      ·
        refine ⟨44246595229082620149924107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29497730152721746766616071 44246595229082620149924107)
        ·
          refine ⟨66369892843623930224886161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44246595229082620149924107 66369892843623930224886161)
          ·
            refine ⟨49777419632717947668664621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66369892843623930224886161 49777419632717947668664621)
            ·
              refine ⟨18666532362269230375749233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49777419632717947668664621 18666532362269230375749233)
              ·
                refine ⟨13999899271701922781811925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18666532362269230375749233 13999899271701922781811925)
                ·
                  refine ⟨328122639180513815198717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13999899271701922781811925 328122639180513815198717)
                  ·
                    rfl

theorem cell23_5751149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_5751149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751149 prefixEnd_5751149 := by exact prefixLift 5751149
  have htrace : WordTrace (prefixWord ++ tailWord_5751149) baseStart_5751149 baseEnd_5751149 := by
    simpa [prefixWord, tailWord_5751149, baseEnd_5751149] using wordTrace_append hprefix tailTrace_5751149
  have hstable : (prefixWord ++ tailWord_5751149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751149).length < 2 ^ (prefixWord ++ tailWord_5751149).sum := by decide
  have hdescent : baseEnd_5751149 < baseStart_5751149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751199 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5751199 : Nat := 118140960795 + 5751199 * 2 ^ 59
def prefixEnd_5751199 : Nat := 4983230072969 + 3 ^ 40 * 5751199 * 2
def baseEnd_5751199 : Nat := 2953129426657349141163223

theorem tailTrace_5751199 : CollatzResearch.WordTrace tailWord_5751199 prefixEnd_5751199 2953129426657349141163223 := by
  unfold tailWord_5751199
  simp only [CollatzResearch.WordTrace]
  refine ⟨209763460291395724435256651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139842306860930482956837767 209763460291395724435256651)
  ·
    refine ⟨314645190437093586652884977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209763460291395724435256651 314645190437093586652884977)
    ·
      refine ⟨235983892827820189989663733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314645190437093586652884977 235983892827820189989663733)
      ·
        refine ⟨22123489952608142811530975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235983892827820189989663733 22123489952608142811530975)
        ·
          refine ⟨33185234928912214217296463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22123489952608142811530975 33185234928912214217296463)
          ·
            refine ⟨49777852393368321325944695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33185234928912214217296463 49777852393368321325944695)
            ·
              refine ⟨74666778590052481988917043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49777852393368321325944695 74666778590052481988917043)
              ·
                refine ⟨112000167885078722983375565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74666778590052481988917043 112000167885078722983375565)
                ·
                  refine ⟨42000062956904521118765837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112000167885078722983375565 42000062956904521118765837)
                  ·
                    refine ⟨15750023608839195419537189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42000062956904521118765837 15750023608839195419537189)
                    ·
                      refine ⟨2953129426657349141163223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15750023608839195419537189 2953129426657349141163223)
                      ·
                        rfl

theorem cell23_5751199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5751199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751199 prefixEnd_5751199 := by exact prefixLift 5751199
  have htrace : WordTrace (prefixWord ++ tailWord_5751199) baseStart_5751199 baseEnd_5751199 := by
    simpa [prefixWord, tailWord_5751199, baseEnd_5751199] using wordTrace_append hprefix tailTrace_5751199
  have hstable : (prefixWord ++ tailWord_5751199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751199).length < 2 ^ (prefixWord ++ tailWord_5751199).sum := by decide
  have hdescent : baseEnd_5751199 < baseStart_5751199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751239 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 8]
def baseStart_5751239 : Nat := 118140960795 + 5751239 * 2 ^ 59
def prefixEnd_5751239 : Nat := 4983230072969 + 3 ^ 40 * 5751239 * 2
def baseEnd_5751239 : Nat := 328127773987058776073671

theorem tailTrace_5751239 : CollatzResearch.WordTrace tailWord_5751239 prefixEnd_5751239 328127773987058776073671 := by
  unfold tailWord_5751239
  simp only [CollatzResearch.WordTrace]
  refine ⟨209764919211250811266712771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139843279474167207511141847 209764919211250811266712771)
  ·
    refine ⟨314647378816876216900069157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209764919211250811266712771 314647378816876216900069157)
    ·
      refine ⟨58996383528164290668762967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314647378816876216900069157 58996383528164290668762967)
      ·
        refine ⟨88494575292246436003144451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58996383528164290668762967 88494575292246436003144451)
        ·
          refine ⟨132741862938369654004716677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88494575292246436003144451 132741862938369654004716677)
          ·
            refine ⟨24889099300944310125884377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132741862938369654004716677 24889099300944310125884377)
            ·
              refine ⟨18666824475708232594413283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24889099300944310125884377 18666824475708232594413283)
              ·
                refine ⟨28000236713562348891619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18666824475708232594413283 28000236713562348891619925)
                ·
                  refine ⟨328127773987058776073671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28000236713562348891619925 328127773987058776073671)
                  ·
                    rfl

theorem cell23_5751239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 8].length) (baseStart_5751239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751239 prefixEnd_5751239 := by exact prefixLift 5751239
  have htrace : WordTrace (prefixWord ++ tailWord_5751239) baseStart_5751239 baseEnd_5751239 := by
    simpa [prefixWord, tailWord_5751239, baseEnd_5751239] using wordTrace_append hprefix tailTrace_5751239
  have hstable : (prefixWord ++ tailWord_5751239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751239).length < 2 ^ (prefixWord ++ tailWord_5751239).sum := by decide
  have hdescent : baseEnd_5751239 < baseStart_5751239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751293 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_5751293 : Nat := 118140960795 + 5751293 * 2 ^ 59
def prefixEnd_5751293 : Nat := 4983230072969 + 3 ^ 40 * 5751293 * 2
def baseEnd_5751293 : Nat := 2953177693838871773387791

theorem tailTrace_5751293 : CollatzResearch.WordTrace tailWord_5751293 prefixEnd_5751293 2953177693838871773387791 := by
  unfold tailWord_5751293
  simp only [CollatzResearch.WordTrace]
  refine ⟨209766888753055178489178533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139844592502036785659452355 209766888753055178489178533)
  ·
    refine ⟨39331291641197845966720975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209766888753055178489178533 39331291641197845966720975)
    ·
      refine ⟨58996937461796768950081463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39331291641197845966720975 58996937461796768950081463)
      ·
        refine ⟨88495406192695153425122195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58996937461796768950081463 88495406192695153425122195)
        ·
          refine ⟨132743109289042730137683293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88495406192695153425122195 132743109289042730137683293)
          ·
            refine ⟨49778665983391023801631235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132743109289042730137683293 49778665983391023801631235)
            ·
              refine ⟨74667998975086535702446853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49778665983391023801631235 74667998975086535702446853)
              ·
                refine ⟨14000249807828725444208785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74667998975086535702446853 14000249807828725444208785)
                ·
                  refine ⟨10500187355871544083156589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14000249807828725444208785 10500187355871544083156589)
                  ·
                    refine ⟨3937570258451829031183721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10500187355871544083156589 3937570258451829031183721)
                    ·
                      refine ⟨2953177693838871773387791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937570258451829031183721 2953177693838871773387791)
                      ·
                        rfl

theorem cell23_5751293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_5751293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751293 prefixEnd_5751293 := by exact prefixLift 5751293
  have htrace : WordTrace (prefixWord ++ tailWord_5751293) baseStart_5751293 baseEnd_5751293 := by
    simpa [prefixWord, tailWord_5751293, baseEnd_5751293] using wordTrace_append hprefix tailTrace_5751293
  have hstable : (prefixWord ++ tailWord_5751293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751293).length < 2 ^ (prefixWord ++ tailWord_5751293).sum := by decide
  have hdescent : baseEnd_5751293 < baseStart_5751293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751299 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 6]
def baseStart_5751299 : Nat := 118140960795 + 5751299 * 2 ^ 59
def prefixEnd_5751299 : Nat := 4983230072969 + 3 ^ 40 * 5751299 * 2
def baseEnd_5751299 : Nat := 984393591574266249970921

theorem tailTrace_5751299 : CollatzResearch.WordTrace tailWord_5751299 prefixEnd_5751299 984393591574266249970921 := by
  unfold tailWord_5751299
  simp only [CollatzResearch.WordTrace]
  refine ⟨209767107591033441513896951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139844738394022294342597967 209767107591033441513896951)
  ·
    refine ⟨314650661386550162270845427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209767107591033441513896951 314650661386550162270845427)
    ·
      refine ⟨471975992079825243406268141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314650661386550162270845427 471975992079825243406268141)
      ·
        refine ⟨176990997029934466277350553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471975992079825243406268141 176990997029934466277350553)
        ·
          refine ⟨132743247772450849708012915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176990997029934466277350553 132743247772450849708012915)
          ·
            refine ⟨199114871658676274562019373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132743247772450849708012915 199114871658676274562019373)
            ·
              refine ⟨74668076872003602960757265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199114871658676274562019373 74668076872003602960757265)
              ·
                refine ⟨56001057654002702220567949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74668076872003602960757265 56001057654002702220567949)
                ·
                  refine ⟨21000396620251013332712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56001057654002702220567949 21000396620251013332712981)
                  ·
                    refine ⟨984393591574266249970921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21000396620251013332712981 984393591574266249970921)
                    ·
                      rfl

theorem cell23_5751299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_5751299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751299 prefixEnd_5751299 := by exact prefixLift 5751299
  have htrace : WordTrace (prefixWord ++ tailWord_5751299) baseStart_5751299 baseEnd_5751299 := by
    simpa [prefixWord, tailWord_5751299, baseEnd_5751299] using wordTrace_append hprefix tailTrace_5751299
  have hstable : (prefixWord ++ tailWord_5751299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751299).length < 2 ^ (prefixWord ++ tailWord_5751299).sum := by decide
  have hdescent : baseEnd_5751299 < baseStart_5751299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751306 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5751306 : Nat := 118140960795 + 5751306 * 2 ^ 59
def prefixEnd_5751306 : Nat := 4983230072969 + 3 ^ 40 * 5751306 * 2
def baseEnd_5751306 : Nat := 2953184369087380222525231

theorem tailTrace_5751306 : CollatzResearch.WordTrace tailWord_5751306 prefixEnd_5751306 2953184369087380222525231 := by
  unfold tailWord_5751306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52441840725502020427350443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139844908601338721139601181 52441840725502020427350443)
  ·
    refine ⟨78662761088253030641025665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52441840725502020427350443 78662761088253030641025665)
    ·
      refine ⟨58997070816189772980769249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78662761088253030641025665 58997070816189772980769249)
      ·
        refine ⟨44247803112142329735576937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58997070816189772980769249 44247803112142329735576937)
        ·
          refine ⟨33185852334106747301682703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44247803112142329735576937 33185852334106747301682703)
          ·
            refine ⟨49778778501160120952524055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33185852334106747301682703 49778778501160120952524055)
            ·
              refine ⟨74668167751740181428786083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49778778501160120952524055 74668167751740181428786083)
              ·
                refine ⟨112002251627610272143179125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74668167751740181428786083 112002251627610272143179125)
                ·
                  refine ⟨10500211090088463013423043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112002251627610272143179125 10500211090088463013423043)
                  ·
                    refine ⟨15750316635132694520134565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10500211090088463013423043 15750316635132694520134565)
                    ·
                      refine ⟨2953184369087380222525231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15750316635132694520134565 2953184369087380222525231)
                      ·
                        rfl

theorem cell23_5751306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5751306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751306 prefixEnd_5751306 := by exact prefixLift 5751306
  have htrace : WordTrace (prefixWord ++ tailWord_5751306) baseStart_5751306 baseEnd_5751306 := by
    simpa [prefixWord, tailWord_5751306, baseEnd_5751306] using wordTrace_append hprefix tailTrace_5751306
  have hstable : (prefixWord ++ tailWord_5751306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751306).length < 2 ^ (prefixWord ++ tailWord_5751306).sum := by decide
  have hdescent : baseEnd_5751306 < baseStart_5751306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751350 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5751350 : Nat := 118140960795 + 5751350 * 2 ^ 59
def prefixEnd_5751350 : Nat := 4983230072969 + 3 ^ 40 * 5751350 * 2
def baseEnd_5751350 : Nat := 984402320745392683458343

theorem tailTrace_5751350 : CollatzResearch.WordTrace tailWord_5751350 prefixEnd_5751350 984402320745392683458343 := by
  unfold tailWord_5751350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13110560482115542326500219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139845978475899118149335669 13110560482115542326500219)
  ·
    refine ⟨19665840723173313489750329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13110560482115542326500219 19665840723173313489750329)
    ·
      refine ⟨14749380542379985117312747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19665840723173313489750329 14749380542379985117312747)
      ·
        refine ⟨22124070813569977675969121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14749380542379985117312747 22124070813569977675969121)
        ·
          refine ⟨16593053110177483256976841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22124070813569977675969121 16593053110177483256976841)
          ·
            refine ⟨12444789832633112442732631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593053110177483256976841 12444789832633112442732631)
            ·
              refine ⟨18667184748949668664098947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12444789832633112442732631 18667184748949668664098947)
              ·
                refine ⟨28000777123424502996148421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18667184748949668664098947 28000777123424502996148421)
                ·
                  refine ⟨5250145710642094311777829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28000777123424502996148421 5250145710642094311777829)
                  ·
                    refine ⟨984402320745392683458343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250145710642094311777829 984402320745392683458343)
                    ·
                      rfl

theorem cell23_5751350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5751350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751350 prefixEnd_5751350 := by exact prefixLift 5751350
  have htrace : WordTrace (prefixWord ++ tailWord_5751350) baseStart_5751350 baseEnd_5751350 := by
    simpa [prefixWord, tailWord_5751350, baseEnd_5751350] using wordTrace_append hprefix tailTrace_5751350
  have hstable : (prefixWord ++ tailWord_5751350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751350).length < 2 ^ (prefixWord ++ tailWord_5751350).sum := by decide
  have hdescent : baseEnd_5751350 < baseStart_5751350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751357 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5751357 : Nat := 118140960795 + 5751357 * 2 ^ 59
def prefixEnd_5751357 : Nat := 4983230072969 + 3 ^ 40 * 5751357 * 2
def baseEnd_5751357 : Nat := 2953210556600759522987497

theorem tailTrace_5751357 : CollatzResearch.WordTrace tailWord_5751357 prefixEnd_5751357 2953210556600759522987497 := by
  unfold tailWord_5751357
  simp only [CollatzResearch.WordTrace]
  refine ⟨209769223024823317419508325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139846148683215544946338883 209769223024823317419508325)
  ·
    refine ⟨39331729317154372016157811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209769223024823317419508325 39331729317154372016157811)
    ·
      refine ⟨58997593975731558024236717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39331729317154372016157811 58997593975731558024236717)
      ·
        refine ⟨22124097740899334259088769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58997593975731558024236717 22124097740899334259088769)
        ·
          refine ⟨16593073305674500694316577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22124097740899334259088769 16593073305674500694316577)
          ·
            refine ⟨12444804979255875520737433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593073305674500694316577 12444804979255875520737433)
            ·
              refine ⟨9333603734441906640553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12444804979255875520737433 9333603734441906640553075)
              ·
                refine ⟨14000405601662859960829613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333603734441906640553075 14000405601662859960829613)
                ·
                  refine ⟨5250152100623572485311105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14000405601662859960829613 5250152100623572485311105)
                  ·
                    refine ⟨3937614075467679363983329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5250152100623572485311105 3937614075467679363983329)
                    ·
                      refine ⟨2953210556600759522987497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937614075467679363983329 2953210556600759522987497)
                      ·
                        rfl

theorem cell23_5751357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5751357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751357 prefixEnd_5751357 := by exact prefixLift 5751357
  have htrace : WordTrace (prefixWord ++ tailWord_5751357) baseStart_5751357 baseEnd_5751357 := by
    simpa [prefixWord, tailWord_5751357, baseEnd_5751357] using wordTrace_append hprefix tailTrace_5751357
  have hstable : (prefixWord ++ tailWord_5751357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751357).length < 2 ^ (prefixWord ++ tailWord_5751357).sum := by decide
  have hdescent : baseEnd_5751357 < baseStart_5751357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_5751416 : Nat := 118140960795 + 5751416 * 2 ^ 59
def prefixEnd_5751416 : Nat := 4983230072969 + 3 ^ 40 * 5751416 * 2
def baseEnd_5751416 : Nat := 2953240851959374792149725

theorem tailTrace_5751416 : CollatzResearch.WordTrace tailWord_5751416 prefixEnd_5751416 2953240851959374792149725 := by
  unfold tailWord_5751416
  simp only [CollatzResearch.WordTrace]
  refine ⟨104885687465804785247953051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139847583287739713663937401 104885687465804785247953051)
  ·
    refine ⟨157328531198707177871929577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104885687465804785247953051 157328531198707177871929577)
    ·
      refine ⟨117996398399030383403947183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157328531198707177871929577 117996398399030383403947183)
      ·
        refine ⟨176994597598545575105920775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117996398399030383403947183 176994597598545575105920775)
        ·
          refine ⟨265491896397818362658881163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176994597598545575105920775 265491896397818362658881163)
          ·
            refine ⟨398237844596727543988321745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265491896397818362658881163 398237844596727543988321745)
            ·
              refine ⟨298678383447545657991241309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398237844596727543988321745 298678383447545657991241309)
              ·
                refine ⟨112004393792829621746715491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298678383447545657991241309 112004393792829621746715491)
                ·
                  refine ⟨168006590689244432620073237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112004393792829621746715491 168006590689244432620073237)
                  ·
                    refine ⟨7875308938558332779065933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168006590689244432620073237 7875308938558332779065933)
                    ·
                      refine ⟨2953240851959374792149725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7875308938558332779065933 2953240851959374792149725)
                      ·
                        rfl

theorem cell23_5751416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_5751416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751416 prefixEnd_5751416 := by exact prefixLift 5751416
  have htrace : WordTrace (prefixWord ++ tailWord_5751416) baseStart_5751416 baseEnd_5751416 := by
    simpa [prefixWord, tailWord_5751416, baseEnd_5751416] using wordTrace_append hprefix tailTrace_5751416
  have hstable : (prefixWord ++ tailWord_5751416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751416).length < 2 ^ (prefixWord ++ tailWord_5751416).sum := by decide
  have hdescent : baseEnd_5751416 < baseStart_5751416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751434 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_5751434 : Nat := 118140960795 + 5751434 * 2 ^ 59
def prefixEnd_5751434 : Nat := 4983230072969 + 3 ^ 40 * 5751434 * 2
def baseEnd_5751434 : Nat := 2953250094611155721724643

theorem tailTrace_5751434 : CollatzResearch.WordTrace tailWord_5751434 prefixEnd_5751434 2953250094611155721724643 := by
  unfold tailWord_5751434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52443007861386089892515339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139848020963696239713374237 52443007861386089892515339)
  ·
    refine ⟨78664511792079134838773009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52443007861386089892515339 78664511792079134838773009)
    ·
      refine ⟨58998383844059351129079757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78664511792079134838773009 58998383844059351129079757)
      ·
        refine ⟨22124393941522256673404909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58998383844059351129079757 22124393941522256673404909)
        ·
          refine ⟨8296647728070846252526841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22124393941522256673404909 8296647728070846252526841)
          ·
            refine ⟨6222485796053134689395131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296647728070846252526841 6222485796053134689395131)
            ·
              refine ⟨9333728694079702034092697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222485796053134689395131 9333728694079702034092697)
              ·
                refine ⟨7000296520559776525569523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9333728694079702034092697 7000296520559776525569523)
                ·
                  refine ⟨10500444780839664788354285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7000296520559776525569523 10500444780839664788354285)
                  ·
                    refine ⟨3937666792814874295632857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10500444780839664788354285 3937666792814874295632857)
                    ·
                      refine ⟨2953250094611155721724643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937666792814874295632857 2953250094611155721724643)
                      ·
                        rfl

theorem cell23_5751434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_5751434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751434 prefixEnd_5751434 := by exact prefixLift 5751434
  have htrace : WordTrace (prefixWord ++ tailWord_5751434) baseStart_5751434 baseEnd_5751434 := by
    simpa [prefixWord, tailWord_5751434, baseEnd_5751434] using wordTrace_append hprefix tailTrace_5751434
  have hstable : (prefixWord ++ tailWord_5751434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751434).length < 2 ^ (prefixWord ++ tailWord_5751434).sum := by decide
  have hdescent : baseEnd_5751434 < baseStart_5751434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751500 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_5751500 : Nat := 118140960795 + 5751500 * 2 ^ 59
def prefixEnd_5751500 : Nat := 4983230072969 + 3 ^ 40 * 5751500 * 2
def baseEnd_5751500 : Nat := 984427994778117487833113

theorem tailTrace_5751500 : CollatzResearch.WordTrace tailWord_5751500 prefixEnd_5751500 984427994778117487833113 := by
  unfold tailWord_5751500
  simp only [CollatzResearch.WordTrace]
  refine ⟨104887219331652626420981977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139849625775536835227975969 104887219331652626420981977)
  ·
    refine ⟨78665414498739469815736483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104887219331652626420981977 78665414498739469815736483)
    ·
      refine ⟨117998121748109204723604725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78665414498739469815736483 117998121748109204723604725)
      ·
        refine ⟨11062323913885237942837943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117998121748109204723604725 11062323913885237942837943)
        ·
          refine ⟨16593485870827856914256915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062323913885237942837943 16593485870827856914256915)
          ·
            refine ⟨24890228806241785371385373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16593485870827856914256915 24890228806241785371385373)
            ·
              refine ⟨9333835802340669514269515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24890228806241785371385373 9333835802340669514269515)
              ·
                refine ⟨14000753703511004271404273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333835802340669514269515 14000753703511004271404273)
                ·
                  refine ⟨10500565277633253203553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14000753703511004271404273 10500565277633253203553205)
                  ·
                    refine ⟨984427994778117487833113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10500565277633253203553205 984427994778117487833113)
                    ·
                      rfl

theorem cell23_5751500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_5751500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751500 prefixEnd_5751500 := by exact prefixLift 5751500
  have htrace : WordTrace (prefixWord ++ tailWord_5751500) baseStart_5751500 baseEnd_5751500 := by
    simpa [prefixWord, tailWord_5751500, baseEnd_5751500] using wordTrace_append hprefix tailTrace_5751500
  have hstable : (prefixWord ++ tailWord_5751500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751500).length < 2 ^ (prefixWord ++ tailWord_5751500).sum := by decide
  have hdescent : baseEnd_5751500 < baseStart_5751500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751513 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_5751513 : Nat := 118140960795 + 5751513 * 2 ^ 59
def prefixEnd_5751513 : Nat := 4983230072969 + 3 ^ 40 * 5751513 * 2
def baseEnd_5751513 : Nat := 984430219860953637545593

theorem tailTrace_5751513 : CollatzResearch.WordTrace tailWord_5751513 prefixEnd_5751513 984430219860953637545593 := by
  unfold tailWord_5751513
  simp only [CollatzResearch.WordTrace]
  refine ⟨209774912812258156062187193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139849941874838770708124795 209774912812258156062187193)
  ·
    refine ⟨157331184609193617046640395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209774912812258156062187193 157331184609193617046640395)
    ·
      refine ⟨235996776913790425569960593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157331184609193617046640395 235996776913790425569960593)
      ·
        refine ⟨176997582685342819177470445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235996776913790425569960593 176997582685342819177470445)
        ·
          refine ⟨66374093507003557191551417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176997582685342819177470445 66374093507003557191551417)
          ·
            refine ⟨49780570130252667893663563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66374093507003557191551417 49780570130252667893663563)
            ·
              refine ⟨74670855195379001840495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49780570130252667893663563 74670855195379001840495345)
              ·
                refine ⟨56003141396534251380371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74670855195379001840495345 56003141396534251380371509)
                ·
                  refine ⟨5250294505925086066909829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56003141396534251380371509 5250294505925086066909829)
                  ·
                    refine ⟨984430219860953637545593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250294505925086066909829 984430219860953637545593)
                    ·
                      rfl

theorem cell23_5751513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_5751513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751513 prefixEnd_5751513 := by exact prefixLift 5751513
  have htrace : WordTrace (prefixWord ++ tailWord_5751513) baseStart_5751513 baseEnd_5751513 := by
    simpa [prefixWord, tailWord_5751513, baseEnd_5751513] using wordTrace_append hprefix tailTrace_5751513
  have hstable : (prefixWord ++ tailWord_5751513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751513).length < 2 ^ (prefixWord ++ tailWord_5751513).sum := by decide
  have hdescent : baseEnd_5751513 < baseStart_5751513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751533 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5751533 : Nat := 118140960795 + 5751533 * 2 ^ 59
def prefixEnd_5751533 : Nat := 4983230072969 + 3 ^ 40 * 5751533 * 2
def baseEnd_5751533 : Nat := 2953300929195950834386687

theorem tailTrace_5751533 : CollatzResearch.WordTrace tailWord_5751533 prefixEnd_5751533 2953300929195950834386687 := by
  unfold tailWord_5751533
  simp only [CollatzResearch.WordTrace]
  refine ⟨209775642272185699477915253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139850428181457132985276835 209775642272185699477915253)
  ·
    refine ⟨19666466463017409326054555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209775642272185699477915253 19666466463017409326054555)
    ·
      refine ⟨29499699694526113989081833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19666466463017409326054555 29499699694526113989081833)
      ·
        refine ⟨22124774770894585491811375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29499699694526113989081833 22124774770894585491811375)
        ·
          refine ⟨33187162156341878237717063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22124774770894585491811375 33187162156341878237717063)
          ·
            refine ⟨49780743234512817356575595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33187162156341878237717063 49780743234512817356575595)
            ·
              refine ⟨74671114851769226034863393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49780743234512817356575595 74671114851769226034863393)
              ·
                refine ⟨56003336138826919526147545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74671114851769226034863393 56003336138826919526147545)
                ·
                  refine ⟨42002502104120189644610659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56003336138826919526147545 42002502104120189644610659)
                  ·
                    refine ⟨63003753156180284466915989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42002502104120189644610659 63003753156180284466915989)
                    ·
                      refine ⟨2953300929195950834386687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63003753156180284466915989 2953300929195950834386687)
                      ·
                        rfl

theorem cell23_5751533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5751533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751533 prefixEnd_5751533 := by exact prefixLift 5751533
  have htrace : WordTrace (prefixWord ++ tailWord_5751533) baseStart_5751533 baseEnd_5751533 := by
    simpa [prefixWord, tailWord_5751533, baseEnd_5751533] using wordTrace_append hprefix tailTrace_5751533
  have hstable : (prefixWord ++ tailWord_5751533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751533).length < 2 ^ (prefixWord ++ tailWord_5751533).sum := by decide
  have hdescent : baseEnd_5751533 < baseStart_5751533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751553 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_5751553 : Nat := 118140960795 + 5751553 * 2 ^ 59
def prefixEnd_5751553 : Nat := 4983230072969 + 3 ^ 40 * 5751553 * 2
def baseEnd_5751553 : Nat := 2953311198809040756136595

theorem tailTrace_5751553 : CollatzResearch.WordTrace tailWord_5751553 prefixEnd_5751553 2953311198809040756136595 := by
  unfold tailWord_5751553
  simp only [CollatzResearch.WordTrace]
  refine ⟨209776371732113242893643313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139850914488075495262428875 209776371732113242893643313)
  ·
    refine ⟨157332278799084932170232485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209776371732113242893643313 157332278799084932170232485)
    ·
      refine ⟨29499802274828424781918591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157332278799084932170232485 29499802274828424781918591)
      ·
        refine ⟨44249703412242637172877887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29499802274828424781918591 44249703412242637172877887)
        ·
          refine ⟨66374555118363955759316831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44249703412242637172877887 66374555118363955759316831)
          ·
            refine ⟨99561832677545933638975247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66374555118363955759316831 99561832677545933638975247)
            ·
              refine ⟨149342749016318900458462871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99561832677545933638975247 149342749016318900458462871)
              ·
                refine ⟨224014123524478350687694307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149342749016318900458462871 224014123524478350687694307)
                ·
                  refine ⟨336021185286717526031541461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224014123524478350687694307 336021185286717526031541461)
                  ·
                    refine ⟨7875496530157442016364253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 336021185286717526031541461 7875496530157442016364253)
                    ·
                      refine ⟨2953311198809040756136595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7875496530157442016364253 2953311198809040756136595)
                      ·
                        rfl

theorem cell23_5751553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_5751553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751553 prefixEnd_5751553 := by exact prefixLift 5751553
  have htrace : WordTrace (prefixWord ++ tailWord_5751553) baseStart_5751553 baseEnd_5751553 := by
    simpa [prefixWord, tailWord_5751553, baseEnd_5751553] using wordTrace_append hprefix tailTrace_5751553
  have hstable : (prefixWord ++ tailWord_5751553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751553).length < 2 ^ (prefixWord ++ tailWord_5751553).sum := by decide
  have hdescent : baseEnd_5751553 < baseStart_5751553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751581 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5751581 : Nat := 118140960795 + 5751581 * 2 ^ 59
def prefixEnd_5751581 : Nat := 4983230072969 + 3 ^ 40 * 5751581 * 2
def baseEnd_5751581 : Nat := 984441858755788882195489

theorem tailTrace_5751581 : CollatzResearch.WordTrace tailWord_5751581 prefixEnd_5751581 984441858755788882195489 := by
  unfold tailWord_5751581
  simp only [CollatzResearch.WordTrace]
  refine ⟨209777392976011803675662597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139851595317341202450441731 209777392976011803675662597)
  ·
    refine ⟨39333261183002213189186737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209777392976011803675662597 39333261183002213189186737)
    ·
      refine ⟨29499945887251659891890053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39333261183002213189186737 29499945887251659891890053)
      ·
        refine ⟨5531239853859686229729385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29499945887251659891890053 5531239853859686229729385)
        ·
          refine ⟨4148429890394764672297039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531239853859686229729385 4148429890394764672297039)
          ·
            refine ⟨6222644835592147008445559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148429890394764672297039 6222644835592147008445559)
            ·
              refine ⟨9333967253388220512668339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222644835592147008445559 9333967253388220512668339)
              ·
                refine ⟨14000950880082330769002509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333967253388220512668339 14000950880082330769002509)
                ·
                  refine ⟨5250356580030874038375941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14000950880082330769002509 5250356580030874038375941)
                  ·
                    refine ⟨984441858755788882195489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250356580030874038375941 984441858755788882195489)
                    ·
                      rfl

theorem cell23_5751581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5751581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751581 prefixEnd_5751581 := by exact prefixLift 5751581
  have htrace : WordTrace (prefixWord ++ tailWord_5751581) baseStart_5751581 baseEnd_5751581 := by
    simpa [prefixWord, tailWord_5751581, baseEnd_5751581] using wordTrace_append hprefix tailTrace_5751581
  have hstable : (prefixWord ++ tailWord_5751581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751581).length < 2 ^ (prefixWord ++ tailWord_5751581).sum := by decide
  have hdescent : baseEnd_5751581 < baseStart_5751581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_5751593 : Nat := 118140960795 + 5751593 * 2 ^ 59
def prefixEnd_5751593 : Nat := 4983230072969 + 3 ^ 40 * 5751593 * 2
def baseEnd_5751593 : Nat := 2953331738035220599636411

theorem tailTrace_5751593 : CollatzResearch.WordTrace tailWord_5751593 prefixEnd_5751593 2953331738035220599636411 := by
  unfold tailWord_5751593
  simp only [CollatzResearch.WordTrace]
  refine ⟨209777830651968329725099433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139851887101312219816732955 209777830651968329725099433)
  ·
    refine ⟨157333372988976247293824575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209777830651968329725099433 157333372988976247293824575)
    ·
      refine ⟨236000059483464370940736863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157333372988976247293824575 236000059483464370940736863)
      ·
        refine ⟨354000089225196556411105295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236000059483464370940736863 354000089225196556411105295)
        ·
          refine ⟨531000133837794834616657943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354000089225196556411105295 531000133837794834616657943)
          ·
            refine ⟨796500200756692251924986915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531000133837794834616657943 796500200756692251924986915)
            ·
              refine ⟨1194750301135038377887480373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796500200756692251924986915 1194750301135038377887480373)
              ·
                refine ⟨112007840731409847926951285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194750301135038377887480373 112007840731409847926951285)
                ·
                  refine ⟨10500735068569673243151683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112007840731409847926951285 10500735068569673243151683)
                  ·
                    refine ⟨15751102602854509864727525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10500735068569673243151683 15751102602854509864727525)
                    ·
                      refine ⟨2953331738035220599636411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15751102602854509864727525 2953331738035220599636411)
                      ·
                        rfl

theorem cell23_5751593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_5751593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751593 prefixEnd_5751593 := by exact prefixLift 5751593
  have htrace : WordTrace (prefixWord ++ tailWord_5751593) baseStart_5751593 baseEnd_5751593 := by
    simpa [prefixWord, tailWord_5751593, baseEnd_5751593] using wordTrace_append hprefix tailTrace_5751593
  have hstable : (prefixWord ++ tailWord_5751593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751593).length < 2 ^ (prefixWord ++ tailWord_5751593).sum := by decide
  have hdescent : baseEnd_5751593 < baseStart_5751593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751633 : List Nat := [1, 2, 2, 1, 6, 11]
def baseStart_5751633 : Nat := 118140960795 + 5751633 * 2 ^ 59
def prefixEnd_5751633 : Nat := 4983230072969 + 3 ^ 40 * 5751633 * 2
def baseEnd_5751633 : Nat := 12153713075149796062289

theorem tailTrace_5751633 : CollatzResearch.WordTrace tailWord_5751633 prefixEnd_5751633 12153713075149796062289 := by
  unfold tailWord_5751633
  simp only [CollatzResearch.WordTrace]
  refine ⟨209779289571823416556555553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139852859714548944371037035 209779289571823416556555553)
  ·
    refine ⟨157334467178867562417416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209779289571823416556555553 157334467178867562417416665)
    ·
      refine ⟨118000850384150671813062499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157334467178867562417416665 118000850384150671813062499)
      ·
        refine ⟨177001275576226007719593749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118000850384150671813062499 177001275576226007719593749)
        ·
          refine ⟨8296934792635594111855957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177001275576226007719593749 8296934792635594111855957)
          ·
            refine ⟨12153713075149796062289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8296934792635594111855957 12153713075149796062289)
            ·
              rfl

theorem cell23_5751633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 11].length) (baseStart_5751633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751633 prefixEnd_5751633 := by exact prefixLift 5751633
  have htrace : WordTrace (prefixWord ++ tailWord_5751633) baseStart_5751633 baseEnd_5751633 := by
    simpa [prefixWord, tailWord_5751633, baseEnd_5751633] using wordTrace_append hprefix tailTrace_5751633
  have hstable : (prefixWord ++ tailWord_5751633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751633).length < 2 ^ (prefixWord ++ tailWord_5751633).sum := by decide
  have hdescent : baseEnd_5751633 < baseStart_5751633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751637 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_5751637 : Nat := 118140960795 + 5751637 * 2 ^ 59
def prefixEnd_5751637 : Nat := 4983230072969 + 3 ^ 40 * 5751637 * 2
def baseEnd_5751637 : Nat := 984451443728006142495403

theorem tailTrace_5751637 : CollatzResearch.WordTrace tailWord_5751637 prefixEnd_5751637 984451443728006142495403 := by
  unfold tailWord_5751637
  simp only [CollatzResearch.WordTrace]
  refine ⟨209779435463808925239701165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139852956975872616826467443 209779435463808925239701165)
  ·
    refine ⟨78667288298928346964887937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209779435463808925239701165 78667288298928346964887937)
    ·
      refine ⟨59000466224196260223665953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78667288298928346964887937 59000466224196260223665953)
      ·
        refine ⟨44250349668147195167749465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59000466224196260223665953 44250349668147195167749465)
        ·
          refine ⟨33187762251110396375812099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44250349668147195167749465 33187762251110396375812099)
          ·
            refine ⟨49781643376665594563718149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33187762251110396375812099 49781643376665594563718149)
            ·
              refine ⟨9334058133124798980697153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49781643376665594563718149 9334058133124798980697153)
              ·
                refine ⟨7000543599843599235522865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9334058133124798980697153 7000543599843599235522865)
                ·
                  refine ⟨5250407699882699426642149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000543599843599235522865 5250407699882699426642149)
                  ·
                    refine ⟨984451443728006142495403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250407699882699426642149 984451443728006142495403)
                    ·
                      rfl

theorem cell23_5751637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_5751637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751637 prefixEnd_5751637 := by exact prefixLift 5751637
  have htrace : WordTrace (prefixWord ++ tailWord_5751637) baseStart_5751637 baseEnd_5751637 := by
    simpa [prefixWord, tailWord_5751637, baseEnd_5751637] using wordTrace_append hprefix tailTrace_5751637
  have hstable : (prefixWord ++ tailWord_5751637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751637).length < 2 ^ (prefixWord ++ tailWord_5751637).sum := by decide
  have hdescent : baseEnd_5751637 < baseStart_5751637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751653 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5751653 : Nat := 118140960795 + 5751653 * 2 ^ 59
def prefixEnd_5751653 : Nat := 4983230072969 + 3 ^ 40 * 5751653 * 2
def baseEnd_5751653 : Nat := 2953362546874490364886135

theorem tailTrace_5751653 : CollatzResearch.WordTrace tailWord_5751653 prefixEnd_5751653 2953362546874490364886135 := by
  unfold tailWord_5751653
  simp only [CollatzResearch.WordTrace]
  refine ⟨209780019031750959972283613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139853346021167306648189075 209780019031750959972283613)
  ·
    refine ⟨78667507136906609989606355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209780019031750959972283613 78667507136906609989606355)
    ·
      refine ⟨118001260705359914984409533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78667507136906609989606355 118001260705359914984409533)
      ·
        refine ⟨44250472764509968119153575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118001260705359914984409533 44250472764509968119153575)
        ·
          refine ⟨66375709146764952178730363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44250472764509968119153575 66375709146764952178730363)
          ·
            refine ⟨99563563720147428268095545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66375709146764952178730363 99563563720147428268095545)
            ·
              refine ⟨74672672790110571201071659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99563563720147428268095545 74672672790110571201071659)
              ·
                refine ⟨112009009185165856801607489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74672672790110571201071659 112009009185165856801607489)
                ·
                  refine ⟨84006756888874392601205617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112009009185165856801607489 84006756888874392601205617)
                  ·
                    refine ⟨63005067666655794450904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84006756888874392601205617 63005067666655794450904213)
                    ·
                      refine ⟨2953362546874490364886135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63005067666655794450904213 2953362546874490364886135)
                      ·
                        rfl

theorem cell23_5751653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5751653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751653 prefixEnd_5751653 := by exact prefixLift 5751653
  have htrace : WordTrace (prefixWord ++ tailWord_5751653) baseStart_5751653 baseEnd_5751653 := by
    simpa [prefixWord, tailWord_5751653, baseEnd_5751653] using wordTrace_append hprefix tailTrace_5751653
  have hstable : (prefixWord ++ tailWord_5751653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751653).length < 2 ^ (prefixWord ++ tailWord_5751653).sum := by decide
  have hdescent : baseEnd_5751653 < baseStart_5751653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751678 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5751678 : Nat := 118140960795 + 5751678 * 2 ^ 59
def prefixEnd_5751678 : Nat := 4983230072969 + 3 ^ 40 * 5751678 * 2
def baseEnd_5751678 : Nat := 2953375383890852767073521

theorem tailTrace_5751678 : CollatzResearch.WordTrace tailWord_5751678 prefixEnd_5751678 2953375383890852767073521 := by
  unfold tailWord_5751678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222616357082548655242961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139853953904440259494629125 26222616357082548655242961)
  ·
    refine ⟨19666962267811911491432221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26222616357082548655242961 19666962267811911491432221)
    ·
      refine ⟨7375110850429466809287083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19666962267811911491432221 7375110850429466809287083)
      ·
        refine ⟨11062666275644200213930625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7375110850429466809287083 11062666275644200213930625)
        ·
          refine ⟨8296999706733150160447969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11062666275644200213930625 8296999706733150160447969)
          ·
            refine ⟨6222749780049862620335977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296999706733150160447969 6222749780049862620335977)
            ·
              refine ⟨4667062335037396965251983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6222749780049862620335977 4667062335037396965251983)
              ·
                refine ⟨7000593502556095447877975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667062335037396965251983 7000593502556095447877975)
                ·
                  refine ⟨10500890253834143171816963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7000593502556095447877975 10500890253834143171816963)
                  ·
                    refine ⟨15751335380751214757725445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10500890253834143171816963 15751335380751214757725445)
                    ·
                      refine ⟨2953375383890852767073521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15751335380751214757725445 2953375383890852767073521)
                      ·
                        rfl

theorem cell23_5751678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5751678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751678 prefixEnd_5751678 := by exact prefixLift 5751678
  have htrace : WordTrace (prefixWord ++ tailWord_5751678) baseStart_5751678 baseEnd_5751678 := by
    simpa [prefixWord, tailWord_5751678, baseEnd_5751678] using wordTrace_append hprefix tailTrace_5751678
  have hstable : (prefixWord ++ tailWord_5751678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751678).length < 2 ^ (prefixWord ++ tailWord_5751678).sum := by decide
  have hdescent : baseEnd_5751678 < baseStart_5751678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751711 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 2, 1, 3]
def baseStart_5751711 : Nat := 118140960795 + 5751711 * 2 ^ 59
def prefixEnd_5751711 : Nat := 4983230072969 + 3 ^ 40 * 5751711 * 2
def baseEnd_5751711 : Nat := 2953392328752451137960869

theorem tailTrace_5751711 : CollatzResearch.WordTrace tailWord_5751711 prefixEnd_5751711 2953392328752451137960869 := by
  unfold tailWord_5751711
  simp only [CollatzResearch.WordTrace]
  refine ⟨209782134465540835877894987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139854756310360557251929991 209782134465540835877894987)
  ·
    refine ⟨314673201698311253816842481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209782134465540835877894987 314673201698311253816842481)
    ·
      refine ⟨236004901273733440362631861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314673201698311253816842481 236004901273733440362631861)
      ·
        refine ⟨22125459494412510033996737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236004901273733440362631861 22125459494412510033996737)
        ·
          refine ⟨16594094620809382525497553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22125459494412510033996737 16594094620809382525497553)
          ·
            refine ⟨12445570965607036894123165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16594094620809382525497553 12445570965607036894123165)
            ·
              refine ⟨4667089112102638835296187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12445570965607036894123165 4667089112102638835296187)
              ·
                refine ⟨7000633668153958252944281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667089112102638835296187 7000633668153958252944281)
                ·
                  refine ⟨5250475251115468689708211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000633668153958252944281 5250475251115468689708211)
                  ·
                    refine ⟨7875712876673203034562317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250475251115468689708211 7875712876673203034562317)
                    ·
                      refine ⟨2953392328752451137960869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7875712876673203034562317 2953392328752451137960869)
                      ·
                        rfl

theorem cell23_5751711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_5751711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751711 prefixEnd_5751711 := by exact prefixLift 5751711
  have htrace : WordTrace (prefixWord ++ tailWord_5751711) baseStart_5751711 baseEnd_5751711 := by
    simpa [prefixWord, tailWord_5751711, baseEnd_5751711] using wordTrace_append hprefix tailTrace_5751711
  have hstable : (prefixWord ++ tailWord_5751711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751711).length < 2 ^ (prefixWord ++ tailWord_5751711).sum := by decide
  have hdescent : baseEnd_5751711 < baseStart_5751711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751768 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_5751768 : Nat := 118140960795 + 5751768 * 2 ^ 59
def prefixEnd_5751768 : Nat := 4983230072969 + 3 ^ 40 * 5751768 * 2
def baseEnd_5751768 : Nat := 2953421597149757414948107

theorem tailTrace_5751768 : CollatzResearch.WordTrace tailWord_5751768 prefixEnd_5751768 2953421597149757414948107 := by
  unfold tailWord_5751768
  simp only [CollatzResearch.WordTrace]
  refine ⟨104892106713167167306359979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139856142284222889741813305 104892106713167167306359979)
  ·
    refine ⟨157338160069750750959539969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104892106713167167306359979 157338160069750750959539969)
    ·
      refine ⟨118003620052313063219654977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157338160069750750959539969 118003620052313063219654977)
      ·
        refine ⟨88502715039234797414741233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118003620052313063219654977 88502715039234797414741233)
        ·
          refine ⟨66377036279426098061055925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88502715039234797414741233 66377036279426098061055925)
          ·
            refine ⟨6222847151196196693223993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66377036279426098061055925 6222847151196196693223993)
            ·
              refine ⟨4667135363397147519917995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6222847151196196693223993 4667135363397147519917995)
              ·
                refine ⟨7000703045095721279876993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667135363397147519917995 7000703045095721279876993)
                ·
                  refine ⟨5250527283821790959907745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000703045095721279876993 5250527283821790959907745)
                  ·
                    refine ⟨3937895462866343219930809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5250527283821790959907745 3937895462866343219930809)
                    ·
                      refine ⟨2953421597149757414948107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937895462866343219930809 2953421597149757414948107)
                      ·
                        rfl

theorem cell23_5751768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_5751768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751768 prefixEnd_5751768 := by exact prefixLift 5751768
  have htrace : WordTrace (prefixWord ++ tailWord_5751768) baseStart_5751768 baseEnd_5751768 := by
    simpa [prefixWord, tailWord_5751768, baseEnd_5751768] using wordTrace_append hprefix tailTrace_5751768
  have hstable : (prefixWord ++ tailWord_5751768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751768).length < 2 ^ (prefixWord ++ tailWord_5751768).sum := by decide
  have hdescent : baseEnd_5751768 < baseStart_5751768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751844 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5751844 : Nat := 118140960795 + 5751844 * 2 ^ 59
def prefixEnd_5751844 : Nat := 4983230072969 + 3 ^ 40 * 5751844 * 2
def baseEnd_5751844 : Nat := 2953460621679499117597757

theorem tailTrace_5751844 : CollatzResearch.WordTrace tailWord_5751844 prefixEnd_5751844 2953460621679499117597757 := by
  unfold tailWord_5751844
  simp only [CollatzResearch.WordTrace]
  refine ⟨104893492687029499796243293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139857990249372666394991057 104893492687029499796243293)
  ·
    refine ⟨39335059757636062423591235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104893492687029499796243293 39335059757636062423591235)
    ·
      refine ⟨59002589636454093635386853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39335059757636062423591235 59002589636454093635386853)
      ·
        refine ⟨11062985556835142556635035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59002589636454093635386853 11062985556835142556635035)
        ·
          refine ⟨16594478335252713834952553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062985556835142556635035 16594478335252713834952553)
          ·
            refine ⟨12445858751439535376214415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16594478335252713834952553 12445858751439535376214415)
            ·
              refine ⟨18668788127159303064321623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12445858751439535376214415 18668788127159303064321623)
              ·
                refine ⟨28003182190738954596482435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18668788127159303064321623 28003182190738954596482435)
                ·
                  refine ⟨42004773286108431894723653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28003182190738954596482435 42004773286108431894723653)
                  ·
                    refine ⟨7875894991145330980260685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42004773286108431894723653 7875894991145330980260685)
                    ·
                      refine ⟨2953460621679499117597757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7875894991145330980260685 2953460621679499117597757)
                      ·
                        rfl

theorem cell23_5751844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5751844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751844 prefixEnd_5751844 := by exact prefixLift 5751844
  have htrace : WordTrace (prefixWord ++ tailWord_5751844) baseStart_5751844 baseEnd_5751844 := by
    simpa [prefixWord, tailWord_5751844, baseEnd_5751844] using wordTrace_append hprefix tailTrace_5751844
  have hstable : (prefixWord ++ tailWord_5751844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751844).length < 2 ^ (prefixWord ++ tailWord_5751844).sum := by decide
  have hdescent : baseEnd_5751844 < baseStart_5751844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751864 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 6]
def baseStart_5751864 : Nat := 118140960795 + 5751864 * 2 ^ 59
def prefixEnd_5751864 : Nat := 4983230072969 + 3 ^ 40 * 5751864 * 2
def baseEnd_5751864 : Nat := 328163432365843226594185

theorem tailTrace_5751864 : CollatzResearch.WordTrace tailWord_5751864 prefixEnd_5751864 328163432365843226594185 := by
  unfold tailWord_5751864
  simp only [CollatzResearch.WordTrace]
  refine ⟨104893857416993271504107323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139858476555991028672143097 104893857416993271504107323)
  ·
    refine ⟨157340786125489907256160985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104893857416993271504107323 157340786125489907256160985)
    ·
      refine ⟨118005589594117430442120739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157340786125489907256160985 118005589594117430442120739)
      ·
        refine ⟨177008384391176145663181109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118005589594117430442120739 177008384391176145663181109)
        ·
          refine ⟨16594536036672763655923229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177008384391176145663181109 16594536036672763655923229)
          ·
            refine ⟨6222951013752286370971211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16594536036672763655923229 6222951013752286370971211)
            ·
              refine ⟨9334426520628429556456817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222951013752286370971211 9334426520628429556456817)
              ·
                refine ⟨7000819890471322167342613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9334426520628429556456817 7000819890471322167342613)
                ·
                  refine ⟨328163432365843226594185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7000819890471322167342613 328163432365843226594185)
                  ·
                    rfl

theorem cell23_5751864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_5751864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751864 prefixEnd_5751864 := by exact prefixLift 5751864
  have htrace : WordTrace (prefixWord ++ tailWord_5751864) baseStart_5751864 baseEnd_5751864 := by
    simpa [prefixWord, tailWord_5751864, baseEnd_5751864] using wordTrace_append hprefix tailTrace_5751864
  have hstable : (prefixWord ++ tailWord_5751864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751864).length < 2 ^ (prefixWord ++ tailWord_5751864).sum := by decide
  have hdescent : baseEnd_5751864 < baseStart_5751864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751867 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 5, 2]
def baseStart_5751867 : Nat := 118140960795 + 5751867 * 2 ^ 59
def prefixEnd_5751867 : Nat := 4983230072969 + 3 ^ 40 * 5751867 * 2
def baseEnd_5751867 : Nat := 2953472431734552527610151

theorem tailTrace_5751867 : CollatzResearch.WordTrace tailWord_5751867 prefixEnd_5751867 2953472431734552527610151 := by
  unfold tailWord_5751867
  simp only [CollatzResearch.WordTrace]
  refine ⟨209787824252975674520573855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139858549501983783013715903 209787824252975674520573855)
  ·
    refine ⟨314681736379463511780860783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209787824252975674520573855 314681736379463511780860783)
    ·
      refine ⟨472022604569195267671291175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314681736379463511780860783 472022604569195267671291175)
      ·
        refine ⟨708033906853792901506936763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472022604569195267671291175 708033906853792901506936763)
        ·
          refine ⟨1062050860280689352260405145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708033906853792901506936763 1062050860280689352260405145)
          ·
            refine ⟨796538145210517014195303859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062050860280689352260405145 796538145210517014195303859)
            ·
              refine ⟨1194807217815775521292955789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796538145210517014195303859 1194807217815775521292955789)
              ·
                refine ⟨448052706680915820484858421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194807217815775521292955789 448052706680915820484858421)
                ·
                  refine ⟨42004941251335858170455477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 448052706680915820484858421 42004941251335858170455477)
                  ·
                    refine ⟨3937963242312736703480201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42004941251335858170455477 3937963242312736703480201)
                    ·
                      refine ⟨2953472431734552527610151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3937963242312736703480201 2953472431734552527610151)
                      ·
                        rfl

theorem cell23_5751867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5, 2].length) (baseStart_5751867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751867 prefixEnd_5751867 := by exact prefixLift 5751867
  have htrace : WordTrace (prefixWord ++ tailWord_5751867) baseStart_5751867 baseEnd_5751867 := by
    simpa [prefixWord, tailWord_5751867, baseEnd_5751867] using wordTrace_append hprefix tailTrace_5751867
  have hstable : (prefixWord ++ tailWord_5751867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751867).length < 2 ^ (prefixWord ++ tailWord_5751867).sum := by decide
  have hdescent : baseEnd_5751867 < baseStart_5751867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751902 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5751902 : Nat := 118140960795 + 5751902 * 2 ^ 59
def prefixEnd_5751902 : Nat := 4983230072969 + 3 ^ 40 * 5751902 * 2
def baseEnd_5751902 : Nat := 984496801185819963557497

theorem tailTrace_5751902 : CollatzResearch.WordTrace tailWord_5751902 prefixEnd_5751902 984496801185819963557497 := by
  unfold tailWord_5751902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26223637600981109437262245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139859400538565916998731973 26223637600981109437262245)
  ·
    refine ⟨4916932050183958019486671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26223637600981109437262245 4916932050183958019486671)
    ·
      refine ⟨7375398075275937029230007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916932050183958019486671 7375398075275937029230007)
      ·
        refine ⟨11063097112913905543845011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7375398075275937029230007 11063097112913905543845011)
        ·
          refine ⟨16594645669370858315767517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11063097112913905543845011 16594645669370858315767517)
          ·
            refine ⟨6222992126014071868412819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16594645669370858315767517 6222992126014071868412819)
            ·
              refine ⟨9334488189021107802619229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222992126014071868412819 9334488189021107802619229)
              ·
                refine ⟨3500433070882915425982211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9334488189021107802619229 3500433070882915425982211)
                ·
                  refine ⟨5250649606324373138973317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500433070882915425982211 5250649606324373138973317)
                  ·
                    refine ⟨984496801185819963557497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250649606324373138973317 984496801185819963557497)
                    ·
                      rfl

theorem cell23_5751902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5751902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751902 prefixEnd_5751902 := by exact prefixLift 5751902
  have htrace : WordTrace (prefixWord ++ tailWord_5751902) baseStart_5751902 baseEnd_5751902 := by
    simpa [prefixWord, tailWord_5751902, baseEnd_5751902] using wordTrace_append hprefix tailTrace_5751902
  have hstable : (prefixWord ++ tailWord_5751902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751902).length < 2 ^ (prefixWord ++ tailWord_5751902).sum := by decide
  have hdescent : baseEnd_5751902 < baseStart_5751902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751925 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5751925 : Nat := 118140960795 + 5751925 * 2 ^ 59
def prefixEnd_5751925 : Nat := 4983230072969 + 3 ^ 40 * 5751925 * 2
def baseEnd_5751925 : Nat := 2953502213612513300684885

theorem tailTrace_5751925 : CollatzResearch.WordTrace tailWord_5751925 prefixEnd_5751925 2953502213612513300684885 := by
  unfold tailWord_5751925
  simp only [CollatzResearch.WordTrace]
  refine ⟨209789939686765550426185229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139859959791177033617456819 209789939686765550426185229)
  ·
    refine ⟨78671227382537081409819461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209789939686765550426185229 78671227382537081409819461)
    ·
      refine ⟨14750855134225702764341149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78671227382537081409819461 14750855134225702764341149)
      ·
        refine ⟨5531570675334638536627931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14750855134225702764341149 5531570675334638536627931)
        ·
          refine ⟨8297356013001957804941897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5531570675334638536627931 8297356013001957804941897)
          ·
            refine ⟨6223017009751468353706423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8297356013001957804941897 6223017009751468353706423)
            ·
              refine ⟨9334525514627202530559635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223017009751468353706423 9334525514627202530559635)
              ·
                refine ⟨14001788271940803795839453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334525514627202530559635 14001788271940803795839453)
                ·
                  refine ⟨5250670601977801423439795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14001788271940803795839453 5250670601977801423439795)
                  ·
                    refine ⟨7876005902966702135159693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250670601977801423439795 7876005902966702135159693)
                    ·
                      refine ⟨2953502213612513300684885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876005902966702135159693 2953502213612513300684885)
                      ·
                        rfl

theorem cell23_5751925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5751925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751925 prefixEnd_5751925 := by exact prefixLift 5751925
  have htrace : WordTrace (prefixWord ++ tailWord_5751925) baseStart_5751925 baseEnd_5751925 := by
    simpa [prefixWord, tailWord_5751925, baseEnd_5751925] using wordTrace_append hprefix tailTrace_5751925
  have hstable : (prefixWord ++ tailWord_5751925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751925).length < 2 ^ (prefixWord ++ tailWord_5751925).sum := by decide
  have hdescent : baseEnd_5751925 < baseStart_5751925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751937 : List Nat := [1, 2, 4, 2, 2, 1, 1, 10]
def baseStart_5751937 : Nat := 118140960795 + 5751937 * 2 ^ 59
def prefixEnd_5751937 : Nat := 4983230072969 + 3 ^ 40 * 5751937 * 2
def baseEnd_5751937 : Nat := 109389199088161750138327

theorem tailTrace_5751937 : CollatzResearch.WordTrace tailWord_5751937 prefixEnd_5751937 109389199088161750138327 := by
  unfold tailWord_5751937
  simp only [CollatzResearch.WordTrace]
  refine ⟨209790377362722076475622065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139860251575148050983748043 209790377362722076475622065)
  ·
    refine ⟨157342783022041557356716549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209790377362722076475622065 157342783022041557356716549)
    ·
      refine ⟨29501771816632792004384353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157342783022041557356716549 29501771816632792004384353)
      ·
        refine ⟨22126328862474594003288265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29501771816632792004384353 22126328862474594003288265)
        ·
          refine ⟨16594746646855945502466199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22126328862474594003288265 16594746646855945502466199)
          ·
            refine ⟨24892119970283918253699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594746646855945502466199 24892119970283918253699299)
            ·
              refine ⟨37338179955425877380548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24892119970283918253699299 37338179955425877380548949)
              ·
                refine ⟨109389199088161750138327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37338179955425877380548949 109389199088161750138327)
                ·
                  rfl

theorem cell23_5751937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 10].length) (baseStart_5751937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751937 prefixEnd_5751937 := by exact prefixLift 5751937
  have htrace : WordTrace (prefixWord ++ tailWord_5751937) baseStart_5751937 baseEnd_5751937 := by
    simpa [prefixWord, tailWord_5751937, baseEnd_5751937] using wordTrace_append hprefix tailTrace_5751937
  have hstable : (prefixWord ++ tailWord_5751937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751937).length < 2 ^ (prefixWord ++ tailWord_5751937).sum := by decide
  have hdescent : baseEnd_5751937 < baseStart_5751937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751941 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_5751941 : Nat := 118140960795 + 5751941 * 2 ^ 59
def prefixEnd_5751941 : Nat := 4983230072969 + 3 ^ 40 * 5751941 * 2
def baseEnd_5751941 : Nat := 984503476434328412694937

theorem tailTrace_5751941 : CollatzResearch.WordTrace tailWord_5751941 prefixEnd_5751941 984503476434328412694937 := by
  unfold tailWord_5751941
  simp only [CollatzResearch.WordTrace]
  refine ⟨209790523254707585158767677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139860348836471723439178451 209790523254707585158767677)
  ·
    refine ⟨78671446220515344434537879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209790523254707585158767677 78671446220515344434537879)
    ·
      refine ⟨118007169330773016651806819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78671446220515344434537879 118007169330773016651806819)
      ·
        refine ⟨177010753996159524977710229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118007169330773016651806819 177010753996159524977710229)
        ·
          refine ⟨8297379093569977733330167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177010753996159524977710229 8297379093569977733330167)
          ·
            refine ⟨12446068640354966599995251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8297379093569977733330167 12446068640354966599995251)
            ·
              refine ⟨18669102960532449899992877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446068640354966599995251 18669102960532449899992877)
              ·
                refine ⟨7000913610199668712497329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18669102960532449899992877 7000913610199668712497329)
                ·
                  refine ⟨5250685207649751534372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000913610199668712497329 5250685207649751534372997)
                  ·
                    refine ⟨984503476434328412694937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250685207649751534372997 984503476434328412694937)
                    ·
                      rfl

theorem cell23_5751941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_5751941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751941 prefixEnd_5751941 := by exact prefixLift 5751941
  have htrace : WordTrace (prefixWord ++ tailWord_5751941) baseStart_5751941 baseEnd_5751941 := by
    simpa [prefixWord, tailWord_5751941, baseEnd_5751941] using wordTrace_append hprefix tailTrace_5751941
  have hstable : (prefixWord ++ tailWord_5751941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751941).length < 2 ^ (prefixWord ++ tailWord_5751941).sum := by decide
  have hdescent : baseEnd_5751941 < baseStart_5751941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751947 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3]
def baseStart_5751947 : Nat := 118140960795 + 5751947 * 2 ^ 59
def prefixEnd_5751947 : Nat := 4983230072969 + 3 ^ 40 * 5751947 * 2
def baseEnd_5751947 : Nat := 2953513510186912214609783

theorem tailTrace_5751947 : CollatzResearch.WordTrace tailWord_5751947 prefixEnd_5751947 2953513510186912214609783 := by
  unfold tailWord_5751947
  simp only [CollatzResearch.WordTrace]
  refine ⟨209790742092685848183486095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139860494728457232122324063 209790742092685848183486095)
  ·
    refine ⟨314686113139028772275229143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209790742092685848183486095 314686113139028772275229143)
    ·
      refine ⟨472029169708543158412843715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314686113139028772275229143 472029169708543158412843715)
      ·
        refine ⟨708043754562814737619265573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472029169708543158412843715 708043754562814737619265573)
        ·
          refine ⟨132758203980527763303612295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 708043754562814737619265573 132758203980527763303612295)
          ·
            refine ⟨199137305970791644955418443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132758203980527763303612295 199137305970791644955418443)
            ·
              refine ⟨298705958956187467433127665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199137305970791644955418443 298705958956187467433127665)
              ·
                refine ⟨224029469217140600574845749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298705958956187467433127665 224029469217140600574845749)
                ·
                  refine ⟨21002762739106931303891789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224029469217140600574845749 21002762739106931303891789)
                  ·
                    refine ⟨7876036027165099238959421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21002762739106931303891789 7876036027165099238959421)
                    ·
                      refine ⟨2953513510186912214609783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876036027165099238959421 2953513510186912214609783)
                      ·
                        rfl

theorem cell23_5751947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].length) (baseStart_5751947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751947 prefixEnd_5751947 := by exact prefixLift 5751947
  have htrace : WordTrace (prefixWord ++ tailWord_5751947) baseStart_5751947 baseEnd_5751947 := by
    simpa [prefixWord, tailWord_5751947, baseEnd_5751947] using wordTrace_append hprefix tailTrace_5751947
  have hstable : (prefixWord ++ tailWord_5751947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751947).length < 2 ^ (prefixWord ++ tailWord_5751947).sum := by decide
  have hdescent : baseEnd_5751947 < baseStart_5751947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751964 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5751964 : Nat := 118140960795 + 5751964 * 2 ^ 59
def prefixEnd_5751964 : Nat := 4983230072969 + 3 ^ 40 * 5751964 * 2
def baseEnd_5751964 : Nat := 2953522239358038648097205

theorem tailTrace_5751964 : CollatzResearch.WordTrace tailWord_5751964 prefixEnd_5751964 2953522239358038648097205 := by
  unfold tailWord_5751964
  simp only [CollatzResearch.WordTrace]
  refine ⟨104895681066812130043427473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139860908089082840057903297 104895681066812130043427473)
  ·
    refine ⟨78671760800109097532570605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104895681066812130043427473 78671760800109097532570605)
    ·
      refine ⟨29501910300040911574713977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78671760800109097532570605 29501910300040911574713977)
      ·
        refine ⟨22126432725030683681035483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29501910300040911574713977 22126432725030683681035483)
        ·
          refine ⟨33189649087546025521553225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22126432725030683681035483 33189649087546025521553225)
          ·
            refine ⟨24892236815659519141164919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33189649087546025521553225 24892236815659519141164919)
            ·
              refine ⟨37338355223489278711747379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24892236815659519141164919 37338355223489278711747379)
              ·
                refine ⟨56007532835233918067621069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37338355223489278711747379 56007532835233918067621069)
                ·
                  refine ⟨21002824813212719275357901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56007532835233918067621069 21002824813212719275357901)
                  ·
                    refine ⟨7876059304954769728259213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21002824813212719275357901 7876059304954769728259213)
                    ·
                      refine ⟨2953522239358038648097205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876059304954769728259213 2953522239358038648097205)
                      ·
                        rfl

theorem cell23_5751964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5751964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751964 prefixEnd_5751964 := by exact prefixLift 5751964
  have htrace : WordTrace (prefixWord ++ tailWord_5751964) baseStart_5751964 baseEnd_5751964 := by
    simpa [prefixWord, tailWord_5751964, baseEnd_5751964] using wordTrace_append hprefix tailTrace_5751964
  have hstable : (prefixWord ++ tailWord_5751964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751964).length < 2 ^ (prefixWord ++ tailWord_5751964).sum := by decide
  have hdescent : baseEnd_5751964 < baseStart_5751964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751987 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_5751987 : Nat := 118140960795 + 5751987 * 2 ^ 59
def prefixEnd_5751987 : Nat := 4983230072969 + 3 ^ 40 * 5751987 * 2
def baseEnd_5751987 : Nat := 2953534049413092058109599

theorem tailTrace_5751987 : CollatzResearch.WordTrace tailWord_5751987 prefixEnd_5751987 2953534049413092058109599 := by
  unfold tailWord_5751987
  simp only [CollatzResearch.WordTrace]
  refine ⟨209792201012540935014942215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139861467341693956676628143 209792201012540935014942215)
  ·
    refine ⟨314688301518811402522413323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209792201012540935014942215 314688301518811402522413323)
    ·
      refine ⟨472032452278217103783619985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314688301518811402522413323 472032452278217103783619985)
      ·
        refine ⟨354024339208662827837714989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472032452278217103783619985 354024339208662827837714989)
        ·
          refine ⟨132759127203248560439143121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354024339208662827837714989 132759127203248560439143121)
          ·
            refine ⟨99569345402436420329357341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132759127203248560439143121 99569345402436420329357341)
            ·
              refine ⟨37338504525913657623509003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99569345402436420329357341 37338504525913657623509003)
              ·
                refine ⟨56007756788870486435263505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37338504525913657623509003 56007756788870486435263505)
                ·
                  refine ⟨42005817591652864826447629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56007756788870486435263505 42005817591652864826447629)
                  ·
                    refine ⟨15752181596869824309917861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42005817591652864826447629 15752181596869824309917861)
                    ·
                      refine ⟨2953534049413092058109599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15752181596869824309917861 2953534049413092058109599)
                      ·
                        rfl

theorem cell23_5751987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_5751987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751987 prefixEnd_5751987 := by exact prefixLift 5751987
  have htrace : WordTrace (prefixWord ++ tailWord_5751987) baseStart_5751987 baseEnd_5751987 := by
    simpa [prefixWord, tailWord_5751987, baseEnd_5751987] using wordTrace_append hprefix tailTrace_5751987
  have hstable : (prefixWord ++ tailWord_5751987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751987).length < 2 ^ (prefixWord ++ tailWord_5751987).sum := by decide
  have hdescent : baseEnd_5751987 < baseStart_5751987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751997 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_5751997 : Nat := 118140960795 + 5751997 * 2 ^ 59
def prefixEnd_5751997 : Nat := 4983230072969 + 3 ^ 40 * 5751997 * 2
def baseEnd_5751997 : Nat := 984513061406545672994851

theorem tailTrace_5751997 : CollatzResearch.WordTrace tailWord_5751997 prefixEnd_5751997 984513061406545672994851 := by
  unfold tailWord_5751997
  simp only [CollatzResearch.WordTrace]
  refine ⟨209792565742504706722806245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139861710495003137815204163 209792565742504706722806245)
  ·
    refine ⟨39336106076719632510526171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209792565742504706722806245 39336106076719632510526171)
    ·
      refine ⟨59004159115079448765789257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39336106076719632510526171 59004159115079448765789257)
      ·
        refine ⟨44253119336309586574341943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59004159115079448765789257 44253119336309586574341943)
        ·
          refine ⟨66379679004464379861512915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44253119336309586574341943 66379679004464379861512915)
          ·
            refine ⟨99569518506696569792269373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66379679004464379861512915 99569518506696569792269373)
            ·
              refine ⟨37338569440011213672101015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99569518506696569792269373 37338569440011213672101015)
              ·
                refine ⟨56007854160016820508151523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37338569440011213672101015 56007854160016820508151523)
                ·
                  refine ⟨84011781240025230762227285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56007854160016820508151523 84011781240025230762227285)
                  ·
                    refine ⟨984513061406545672994851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84011781240025230762227285 984513061406545672994851)
                    ·
                      rfl

theorem cell23_5751997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_5751997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751997 prefixEnd_5751997 := by exact prefixLift 5751997
  have htrace : WordTrace (prefixWord ++ tailWord_5751997) baseStart_5751997 baseEnd_5751997 := by
    simpa [prefixWord, tailWord_5751997, baseEnd_5751997] using wordTrace_append hprefix tailTrace_5751997
  have hstable : (prefixWord ++ tailWord_5751997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751997).length < 2 ^ (prefixWord ++ tailWord_5751997).sum := by decide
  have hdescent : baseEnd_5751997 < baseStart_5751997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5751998 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5751998 : Nat := 118140960795 + 5751998 * 2 ^ 59
def prefixEnd_5751998 : Nat := 4983230072969 + 3 ^ 40 * 5751998 * 2
def baseEnd_5751998 : Nat := 2953539697700291515072049

theorem tailTrace_5751998 : CollatzResearch.WordTrace tailWord_5751998 prefixEnd_5751998 2953539697700291515072049 := by
  unfold tailWord_5751998
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224075276937635486699081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139861734810334055929061765 26224075276937635486699081)
  ·
    refine ⟨19668056457703226615024311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26224075276937635486699081 19668056457703226615024311)
    ·
      refine ⟨29502084686554839922536467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19668056457703226615024311 29502084686554839922536467)
      ·
        refine ⟨44253127029832259883804701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29502084686554839922536467 44253127029832259883804701)
        ·
          refine ⟨16594922636187097456426763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44253127029832259883804701 16594922636187097456426763)
          ·
            refine ⟨24892383954280646184640145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594922636187097456426763 24892383954280646184640145)
            ·
              refine ⟨18669287965710484638480109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24892383954280646184640145 18669287965710484638480109)
              ·
                refine ⟨7000982987141431739430041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18669287965710484638480109 7000982987141431739430041)
                ·
                  refine ⟨5250737240356073804572531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000982987141431739430041 5250737240356073804572531)
                  ·
                    refine ⟨7876105860534110706858797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250737240356073804572531 7876105860534110706858797)
                    ·
                      refine ⟨2953539697700291515072049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876105860534110706858797 2953539697700291515072049)
                      ·
                        rfl

theorem cell23_5751998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5751998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5751998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5751998 prefixEnd_5751998 := by exact prefixLift 5751998
  have htrace : WordTrace (prefixWord ++ tailWord_5751998) baseStart_5751998 baseEnd_5751998 := by
    simpa [prefixWord, tailWord_5751998, baseEnd_5751998] using wordTrace_append hprefix tailTrace_5751998
  have hstable : (prefixWord ++ tailWord_5751998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5751998).length < 2 ^ (prefixWord ++ tailWord_5751998).sum := by decide
  have hdescent : baseEnd_5751998 < baseStart_5751998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5751998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5752007 : Nat := 118140960795 + 5752007 * 2 ^ 59
def prefixEnd_5752007 : Nat := 4983230072969 + 3 ^ 40 * 5752007 * 2
def baseEnd_5752007 : Nat := 2953544319026181979859507

theorem tailTrace_5752007 : CollatzResearch.WordTrace tailWord_5752007 prefixEnd_5752007 2953544319026181979859507 := by
  unfold tailWord_5752007
  simp only [CollatzResearch.WordTrace]
  refine ⟨209792930472468478430670275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139861953648312318953780183 209792930472468478430670275)
  ·
    refine ⟨314689395708702717646005413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209792930472468478430670275 314689395708702717646005413)
    ·
      refine ⟨59004261695381759558626015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314689395708702717646005413 59004261695381759558626015)
      ·
        refine ⟨88506392543072639337939023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59004261695381759558626015 88506392543072639337939023)
        ·
          refine ⟨132759588814608959006908535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88506392543072639337939023 132759588814608959006908535)
          ·
            refine ⟨199139383221913438510362803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132759588814608959006908535 199139383221913438510362803)
            ·
              refine ⟨298709074832870157765544205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199139383221913438510362803 298709074832870157765544205)
              ·
                refine ⟨112015903062326309162079077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298709074832870157765544205 112015903062326309162079077)
                ·
                  refine ⟨21002981824186182967889827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112015903062326309162079077 21002981824186182967889827)
                  ·
                    refine ⟨31504472736279274451834741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21002981824186182967889827 31504472736279274451834741)
                    ·
                      refine ⟨2953544319026181979859507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31504472736279274451834741 2953544319026181979859507)
                      ·
                        rfl

theorem cell23_5752007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5752007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752007 prefixEnd_5752007 := by exact prefixLift 5752007
  have htrace : WordTrace (prefixWord ++ tailWord_5752007) baseStart_5752007 baseEnd_5752007 := by
    simpa [prefixWord, tailWord_5752007, baseEnd_5752007] using wordTrace_append hprefix tailTrace_5752007
  have hstable : (prefixWord ++ tailWord_5752007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752007).length < 2 ^ (prefixWord ++ tailWord_5752007).sum := by decide
  have hdescent : baseEnd_5752007 < baseStart_5752007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752017 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_5752017 : Nat := 118140960795 + 5752017 * 2 ^ 59
def prefixEnd_5752017 : Nat := 4983230072969 + 3 ^ 40 * 5752017 * 2
def baseEnd_5752017 : Nat := 2953549453832726940734461

theorem tailTrace_5752017 : CollatzResearch.WordTrace tailWord_5752017 prefixEnd_5752017 2953549453832726940734461 := by
  unfold tailWord_5752017
  simp only [CollatzResearch.WordTrace]
  refine ⟨209793295202432250138534305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139862196801621500092356203 209793295202432250138534305)
  ·
    refine ⟨157344971401824187603900729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209793295202432250138534305 157344971401824187603900729)
    ·
      refine ⟨118008728551368140702925547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157344971401824187603900729 118008728551368140702925547)
      ·
        refine ⟨177013092827052211054388321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118008728551368140702925547 177013092827052211054388321)
        ·
          refine ⟨132759819620289158290791241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177013092827052211054388321 132759819620289158290791241)
          ·
            refine ⟨99569864715216868718093431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132759819620289158290791241 99569864715216868718093431)
            ·
              refine ⟨149354797072825303077140147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99569864715216868718093431 149354797072825303077140147)
              ·
                refine ⟨224032195609237954615710221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149354797072825303077140147 224032195609237954615710221)
                ·
                  refine ⟨84012073353464232980891333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224032195609237954615710221 84012073353464232980891333)
                  ·
                    refine ⟨15752263753774543683917125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84012073353464232980891333 15752263753774543683917125)
                    ·
                      refine ⟨2953549453832726940734461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15752263753774543683917125 2953549453832726940734461)
                      ·
                        rfl

theorem cell23_5752017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_5752017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752017 prefixEnd_5752017 := by exact prefixLift 5752017
  have htrace : WordTrace (prefixWord ++ tailWord_5752017) baseStart_5752017 baseEnd_5752017 := by
    simpa [prefixWord, tailWord_5752017, baseEnd_5752017] using wordTrace_append hprefix tailTrace_5752017
  have hstable : (prefixWord ++ tailWord_5752017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752017).length < 2 ^ (prefixWord ++ tailWord_5752017).sum := by decide
  have hdescent : baseEnd_5752017 < baseStart_5752017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752044 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 7]
def baseStart_5752044 : Nat := 118140960795 + 5752044 * 2 ^ 59
def prefixEnd_5752044 : Nat := 4983230072969 + 3 ^ 40 * 5752044 * 2
def baseEnd_5752044 : Nat := 328173701978933148344093

theorem tailTrace_5752044 : CollatzResearch.WordTrace tailWord_5752044 prefixEnd_5752044 328173701978933148344093 := by
  unfold tailWord_5752044
  simp only [CollatzResearch.WordTrace]
  refine ⟨104897139986667216874883593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139862853315556289166511457 104897139986667216874883593)
  ·
    refine ⟨78672854990000412656162695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104897139986667216874883593 78672854990000412656162695)
    ·
      refine ⟨118009282485000618984244043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78672854990000412656162695 118009282485000618984244043)
      ·
        refine ⟨177013923727500928476366065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118009282485000618984244043 177013923727500928476366065)
        ·
          refine ⟨132760442795625696357274549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177013923727500928476366065 132760442795625696357274549)
          ·
            refine ⟨12446291512089909033494489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132760442795625696357274549 12446291512089909033494489)
            ·
              refine ⟨9334718634067431775120867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12446291512089909033494489 9334718634067431775120867)
              ·
                refine ⟨14002077951101147662681301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334718634067431775120867 14002077951101147662681301)
                ·
                  refine ⟨328173701978933148344093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14002077951101147662681301 328173701978933148344093)
                  ·
                    rfl

theorem cell23_5752044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_5752044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752044 prefixEnd_5752044 := by exact prefixLift 5752044
  have htrace : WordTrace (prefixWord ++ tailWord_5752044) baseStart_5752044 baseEnd_5752044 := by
    simpa [prefixWord, tailWord_5752044, baseEnd_5752044] using wordTrace_append hprefix tailTrace_5752044
  have hstable : (prefixWord ++ tailWord_5752044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752044).length < 2 ^ (prefixWord ++ tailWord_5752044).sum := by decide
  have hdescent : baseEnd_5752044 < baseStart_5752044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752057 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_5752057 : Nat := 118140960795 + 5752057 * 2 ^ 59
def prefixEnd_5752057 : Nat := 4983230072969 + 3 ^ 40 * 5752057 * 2
def baseEnd_5752057 : Nat := 984523331019635594744759

theorem tailTrace_5752057 : CollatzResearch.WordTrace tailWord_5752057 prefixEnd_5752057 984523331019635594744759 := by
  unfold tailWord_5752057
  simp only [CollatzResearch.WordTrace]
  refine ⟨209794754122287336969990425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139863169414858224646660283 209794754122287336969990425)
  ·
    refine ⟨157346065591715502727492819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209794754122287336969990425 157346065591715502727492819)
    ·
      refine ⟨236019098387573254091239229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157346065591715502727492819 236019098387573254091239229)
      ·
        refine ⟨88507161895339970284214711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236019098387573254091239229 88507161895339970284214711)
        ·
          refine ⟨132760742843009955426322067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88507161895339970284214711 132760742843009955426322067)
          ·
            refine ⟨199141114264514933139483101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132760742843009955426322067 199141114264514933139483101)
            ·
              refine ⟨74677917849193099927306163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199141114264514933139483101 74677917849193099927306163)
              ·
                refine ⟨112016876773789649890959245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74677917849193099927306163 112016876773789649890959245)
                ·
                  refine ⟨42006328790171118709109717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112016876773789649890959245 42006328790171118709109717)
                  ·
                    refine ⟨984523331019635594744759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42006328790171118709109717 984523331019635594744759)
                    ·
                      rfl

theorem cell23_5752057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_5752057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752057 prefixEnd_5752057 := by exact prefixLift 5752057
  have htrace : WordTrace (prefixWord ++ tailWord_5752057) baseStart_5752057 baseEnd_5752057 := by
    simpa [prefixWord, tailWord_5752057, baseEnd_5752057] using wordTrace_append hprefix tailTrace_5752057
  have hstable : (prefixWord ++ tailWord_5752057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752057).length < 2 ^ (prefixWord ++ tailWord_5752057).sum := by decide
  have hdescent : baseEnd_5752057 < baseStart_5752057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752074 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_5752074 : Nat := 118140960795 + 5752074 * 2 ^ 59
def prefixEnd_5752074 : Nat := 4983230072969 + 3 ^ 40 * 5752074 * 2
def baseEnd_5752074 : Nat := 984526240743344405907233

theorem tailTrace_5752074 : CollatzResearch.WordTrace tailWord_5752074 prefixEnd_5752074 984526240743344405907233 := by
  unfold tailWord_5752074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52448843540806437218339819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139863582775483832582239517 52448843540806437218339819)
  ·
    refine ⟨78673265311209655827509729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52448843540806437218339819 78673265311209655827509729)
    ·
      refine ⟨59004948983407241870632297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78673265311209655827509729 59004948983407241870632297)
      ·
        refine ⟨44253711737555431402974223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59004948983407241870632297 44253711737555431402974223)
        ·
          refine ⟨66380567606333147104461335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44253711737555431402974223 66380567606333147104461335)
          ·
            refine ⟨99570851409499720656692003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66380567606333147104461335 99570851409499720656692003)
            ·
              refine ⟨149356277114249580985038005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99570851409499720656692003 149356277114249580985038005)
              ·
                refine ⟨14002150979460898217347313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149356277114249580985038005 14002150979460898217347313)
                ·
                  refine ⟨10501613234595673663010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14002150979460898217347313 10501613234595673663010485)
                  ·
                    refine ⟨984526240743344405907233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10501613234595673663010485 984526240743344405907233)
                    ·
                      rfl

theorem cell23_5752074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_5752074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752074 prefixEnd_5752074 := by exact prefixLift 5752074
  have htrace : WordTrace (prefixWord ++ tailWord_5752074) baseStart_5752074 baseEnd_5752074 := by
    simpa [prefixWord, tailWord_5752074, baseEnd_5752074] using wordTrace_append hprefix tailTrace_5752074
  have hstable : (prefixWord ++ tailWord_5752074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752074).length < 2 ^ (prefixWord ++ tailWord_5752074).sum := by decide
  have hdescent : baseEnd_5752074 < baseStart_5752074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752078 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_5752078 : Nat := 118140960795 + 5752078 * 2 ^ 59
def prefixEnd_5752078 : Nat := 4983230072969 + 3 ^ 40 * 5752078 * 2
def baseEnd_5752078 : Nat := 328175641794739022452409

theorem tailTrace_5752078 : CollatzResearch.WordTrace tailWord_5752078 prefixEnd_5752078 328175641794739022452409 := by
  unfold tailWord_5752078
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224440006901407194563111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139863680036807505037669925 26224440006901407194563111)
  ·
    refine ⟨39336660010352110791844667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224440006901407194563111 39336660010352110791844667)
    ·
      refine ⟨59004990015528166187767001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39336660010352110791844667 59004990015528166187767001)
      ·
        refine ⟨44253742511646124640825251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59004990015528166187767001 44253742511646124640825251)
        ·
          refine ⟨66380613767469186961237877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44253742511646124640825251 66380613767469186961237877)
          ·
            refine ⟨6223182540700236277616051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66380613767469186961237877 6223182540700236277616051)
            ·
              refine ⟨9334773811050354416424077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223182540700236277616051 9334773811050354416424077)
              ·
                refine ⟨3500540179143882906159029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9334773811050354416424077 3500540179143882906159029)
                ·
                  refine ⟨328175641794739022452409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3500540179143882906159029 328175641794739022452409)
                  ·
                    rfl

theorem cell23_5752078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_5752078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752078 prefixEnd_5752078 := by exact prefixLift 5752078
  have htrace : WordTrace (prefixWord ++ tailWord_5752078) baseStart_5752078 baseEnd_5752078 := by
    simpa [prefixWord, tailWord_5752078, baseEnd_5752078] using wordTrace_append hprefix tailTrace_5752078
  have hstable : (prefixWord ++ tailWord_5752078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752078).length < 2 ^ (prefixWord ++ tailWord_5752078).sum := by decide
  have hdescent : baseEnd_5752078 < baseStart_5752078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752151 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 6]
def baseStart_5752151 : Nat := 118140960795 + 5752151 * 2 ^ 59
def prefixEnd_5752151 : Nat := 4983230072969 + 3 ^ 40 * 5752151 * 2
def baseEnd_5752151 : Nat := 328179806693381046273205

theorem tailTrace_5752151 : CollatzResearch.WordTrace tailWord_5752151 prefixEnd_5752151 328179806693381046273205 := by
  unfold tailWord_5752151
  simp only [CollatzResearch.WordTrace]
  refine ⟨209798182583946791023912307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139865455055964527349274871 209798182583946791023912307)
  ·
    refine ⟨314697273875920186535868461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209798182583946791023912307 314697273875920186535868461)
    ·
      refine ⟨118011477703470069950950673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314697273875920186535868461 118011477703470069950950673)
      ·
        refine ⟨88508608277602552463213005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118011477703470069950950673 88508608277602552463213005)
        ·
          refine ⟨33190728104100957173704877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88508608277602552463213005 33190728104100957173704877)
          ·
            refine ⟨12446523039037858940139329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33190728104100957173704877 12446523039037858940139329)
            ·
              refine ⟨9334892279278394205104497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12446523039037858940139329 9334892279278394205104497)
              ·
                refine ⟨7001169209458795653828373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9334892279278394205104497 7001169209458795653828373)
                ·
                  refine ⟨328179806693381046273205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7001169209458795653828373 328179806693381046273205)
                  ·
                    rfl

theorem cell23_5752151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 6].length) (baseStart_5752151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752151 prefixEnd_5752151 := by exact prefixLift 5752151
  have htrace : WordTrace (prefixWord ++ tailWord_5752151) baseStart_5752151 baseEnd_5752151 := by
    simpa [prefixWord, tailWord_5752151, baseEnd_5752151] using wordTrace_append hprefix tailTrace_5752151
  have hstable : (prefixWord ++ tailWord_5752151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752151).length < 2 ^ (prefixWord ++ tailWord_5752151).sum := by decide
  have hdescent : baseEnd_5752151 < baseStart_5752151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752161 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_5752161 : Nat := 118140960795 + 5752161 * 2 ^ 59
def prefixEnd_5752161 : Nat := 4983230072969 + 3 ^ 40 * 5752161 * 2
def baseEnd_5752161 : Nat := 2953623395046974377333799

theorem tailTrace_5752161 : CollatzResearch.WordTrace tailWord_5752161 prefixEnd_5752161 2953623395046974377333799 := by
  unfold tailWord_5752161
  simp only [CollatzResearch.WordTrace]
  refine ⟨209798547313910562731776337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139865698209273708487850891 209798547313910562731776337)
  ·
    refine ⟨157348910485432922048832253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209798547313910562731776337 157348910485432922048832253)
    ·
      refine ⟨59005841432037345768312095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157348910485432922048832253 59005841432037345768312095)
      ·
        refine ⟨88508762148056018652468143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59005841432037345768312095 88508762148056018652468143)
        ·
          refine ⟨132763143222084027978702215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88508762148056018652468143 132763143222084027978702215)
          ·
            refine ⟨199144714833126041968053323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132763143222084027978702215 199144714833126041968053323)
            ·
              refine ⟨298717072249689062952079985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199144714833126041968053323 298717072249689062952079985)
              ·
                refine ⟨224037804187266797214059989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298717072249689062952079985 224037804187266797214059989)
                ·
                  refine ⟨5250886035639065559704531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224037804187266797214059989 5250886035639065559704531)
                  ·
                    refine ⟨7876329053458598339556797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250886035639065559704531 7876329053458598339556797)
                    ·
                      refine ⟨2953623395046974377333799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876329053458598339556797 2953623395046974377333799)
                      ·
                        rfl

theorem cell23_5752161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_5752161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752161 prefixEnd_5752161 := by exact prefixLift 5752161
  have htrace : WordTrace (prefixWord ++ tailWord_5752161) baseStart_5752161 baseEnd_5752161 := by
    simpa [prefixWord, tailWord_5752161, baseEnd_5752161] using wordTrace_append hprefix tailTrace_5752161
  have hstable : (prefixWord ++ tailWord_5752161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752161).length < 2 ^ (prefixWord ++ tailWord_5752161).sum := by decide
  have hdescent : baseEnd_5752161 < baseStart_5752161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752178 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_5752178 : Nat := 118140960795 + 5752178 * 2 ^ 59
def prefixEnd_5752178 : Nat := 4983230072969 + 3 ^ 40 * 5752178 * 2
def baseEnd_5752178 : Nat := 2953632124218100810821221

theorem tailTrace_5752178 : CollatzResearch.WordTrace tailWord_5752178 prefixEnd_5752178 2953632124218100810821221 := by
  unfold tailWord_5752178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52449791838712243658786297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139866111569899316423430125 52449791838712243658786297)
  ·
    refine ⟨39337343879034182744089723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52449791838712243658786297 39337343879034182744089723)
    ·
      refine ⟨59006015818551274116134585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39337343879034182744089723 59006015818551274116134585)
      ·
        refine ⟨44254511863913455587100939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59006015818551274116134585 44254511863913455587100939)
        ·
          refine ⟨66381767795870183380651409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44254511863913455587100939 66381767795870183380651409)
          ·
            refine ⟨49786325846902637535488557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66381767795870183380651409 49786325846902637535488557)
            ·
              refine ⟨18669872192588489075808209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49786325846902637535488557 18669872192588489075808209)
              ·
                refine ⟨14002404144441366806856157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18669872192588489075808209 14002404144441366806856157)
                ·
                  refine ⟨5250901554165512552571059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14002404144441366806856157 5250901554165512552571059)
                  ·
                    refine ⟨7876352331248268828856589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250901554165512552571059 7876352331248268828856589)
                    ·
                      refine ⟨2953632124218100810821221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876352331248268828856589 2953632124218100810821221)
                      ·
                        rfl

theorem cell23_5752178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_5752178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752178 prefixEnd_5752178 := by exact prefixLift 5752178
  have htrace : WordTrace (prefixWord ++ tailWord_5752178) baseStart_5752178 baseEnd_5752178 := by
    simpa [prefixWord, tailWord_5752178, baseEnd_5752178] using wordTrace_append hprefix tailTrace_5752178
  have hstable : (prefixWord ++ tailWord_5752178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752178).length < 2 ^ (prefixWord ++ tailWord_5752178).sum := by decide
  have hdescent : baseEnd_5752178 < baseStart_5752178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752195 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 1, 1, 3]
def baseStart_5752195 : Nat := 118140960795 + 5752195 * 2 ^ 59
def prefixEnd_5752195 : Nat := 4983230072969 + 3 ^ 40 * 5752195 * 2
def baseEnd_5752195 : Nat := 2953640853389227244308643

theorem tailTrace_5752195 : CollatzResearch.WordTrace tailWord_5752195 prefixEnd_5752195 2953640853389227244308643 := by
  unfold tailWord_5752195
  simp only [CollatzResearch.WordTrace]
  refine ⟨209799787395787386538514039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139866524930524924359009359 209799787395787386538514039)
  ·
    refine ⟨314699681093681079807771059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209799787395787386538514039 314699681093681079807771059)
    ·
      refine ⟨472049521640521619711656589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314699681093681079807771059 472049521640521619711656589)
      ·
        refine ⟨177018570615195607391871221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472049521640521619711656589 177018570615195607391871221)
        ·
          refine ⟨16595490995174588192987927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177018570615195607391871221 16595490995174588192987927)
          ·
            refine ⟨24893236492761882289481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16595490995174588192987927 24893236492761882289481891)
            ·
              refine ⟨37339854739142823434222837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24893236492761882289481891 37339854739142823434222837)
              ·
                refine ⟨3500611381794639696958391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37339854739142823434222837 3500611381794639696958391)
                ·
                  refine ⟨5250917072691959545437587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500611381794639696958391 5250917072691959545437587)
                  ·
                    refine ⟨7876375609037939318156381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250917072691959545437587 7876375609037939318156381)
                    ·
                      refine ⟨2953640853389227244308643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876375609037939318156381 2953640853389227244308643)
                      ·
                        rfl

theorem cell23_5752195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_5752195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752195 prefixEnd_5752195 := by exact prefixLift 5752195
  have htrace : WordTrace (prefixWord ++ tailWord_5752195) baseStart_5752195 baseEnd_5752195 := by
    simpa [prefixWord, tailWord_5752195, baseEnd_5752195] using wordTrace_append hprefix tailTrace_5752195
  have hstable : (prefixWord ++ tailWord_5752195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752195).length < 2 ^ (prefixWord ++ tailWord_5752195).sum := by decide
  have hdescent : baseEnd_5752195 < baseStart_5752195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752212 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5752212 : Nat := 118140960795 + 5752212 * 2 ^ 59
def prefixEnd_5752212 : Nat := 4983230072969 + 3 ^ 40 * 5752212 * 2
def baseEnd_5752212 : Nat := 2953649582560353677796065

theorem tailTrace_5752212 : CollatzResearch.WordTrace tailWord_5752212 prefixEnd_5752212 2953649582560353677796065 := by
  unfold tailWord_5752212
  simp only [CollatzResearch.WordTrace]
  refine ⟨104900203718362899220941445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139866938291150532294588593 104900203718362899220941445)
  ·
    refine ⟨19668788197193043603926521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104900203718362899220941445 19668788197193043603926521)
    ·
      refine ⟨14751591147894782702944891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19668788197193043603926521 14751591147894782702944891)
      ·
        refine ⟨22127386721842174054417337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14751591147894782702944891 22127386721842174054417337)
        ·
          refine ⟨16595540041381630540813003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22127386721842174054417337 16595540041381630540813003)
          ·
            refine ⟨24893310062072445811219505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16595540041381630540813003 24893310062072445811219505)
            ·
              refine ⟨18669982546554334358414629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24893310062072445811219505 18669982546554334358414629)
              ·
                refine ⟨3500621727478937692202743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18669982546554334358414629 3500621727478937692202743)
                ·
                  refine ⟨5250932591218406538304115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500621727478937692202743 5250932591218406538304115)
                  ·
                    refine ⟨7876398886827609807456173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250932591218406538304115 7876398886827609807456173)
                    ·
                      refine ⟨2953649582560353677796065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7876398886827609807456173 2953649582560353677796065)
                      ·
                        rfl

theorem cell23_5752212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5752212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752212 prefixEnd_5752212 := by exact prefixLift 5752212
  have htrace : WordTrace (prefixWord ++ tailWord_5752212) baseStart_5752212 baseEnd_5752212 := by
    simpa [prefixWord, tailWord_5752212, baseEnd_5752212] using wordTrace_append hprefix tailTrace_5752212
  have hstable : (prefixWord ++ tailWord_5752212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752212).length < 2 ^ (prefixWord ++ tailWord_5752212).sum := by decide
  have hdescent : baseEnd_5752212 < baseStart_5752212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752221 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5752221 : Nat := 118140960795 + 5752221 * 2 ^ 59
def prefixEnd_5752221 : Nat := 4983230072969 + 3 ^ 40 * 5752221 * 2
def baseEnd_5752221 : Nat := 2953654203886244142583523

theorem tailTrace_5752221 : CollatzResearch.WordTrace tailWord_5752221 prefixEnd_5752221 2953654203886244142583523 := by
  unfold tailWord_5752221
  simp only [CollatzResearch.WordTrace]
  refine ⟨209800735693693192978960517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139867157129128795319307011 209800735693693192978960517)
  ·
    refine ⟨39337637942567473683555097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209800735693693192978960517 39337637942567473683555097)
    ·
      refine ⟨29503228456925605262666323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39337637942567473683555097 29503228456925605262666323)
      ·
        refine ⟨44254842685388407893999485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29503228456925605262666323 44254842685388407893999485)
        ·
          refine ⟨16595566007020652960249807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44254842685388407893999485 16595566007020652960249807)
          ·
            refine ⟨24893349010530979440374711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16595566007020652960249807 24893349010530979440374711)
            ·
              refine ⟨37340023515796469160562067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24893349010530979440374711 37340023515796469160562067)
              ·
                refine ⟨56010035273694703740843101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37340023515796469160562067 56010035273694703740843101)
                ·
                  refine ⟨21003763227635513902816163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56010035273694703740843101 21003763227635513902816163)
                  ·
                    refine ⟨31505644841453270854224245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21003763227635513902816163 31505644841453270854224245)
                    ·
                      refine ⟨2953654203886244142583523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31505644841453270854224245 2953654203886244142583523)
                      ·
                        rfl

theorem cell23_5752221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5752221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752221 prefixEnd_5752221 := by exact prefixLift 5752221
  have htrace : WordTrace (prefixWord ++ tailWord_5752221) baseStart_5752221 baseEnd_5752221 := by
    simpa [prefixWord, tailWord_5752221, baseEnd_5752221] using wordTrace_append hprefix tailTrace_5752221
  have hstable : (prefixWord ++ tailWord_5752221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752221).length < 2 ^ (prefixWord ++ tailWord_5752221).sum := by decide
  have hdescent : baseEnd_5752221 < baseStart_5752221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752224 : List Nat := [2, 1, 1, 4, 1, 2, 2, 10]
def baseStart_5752224 : Nat := 118140960795 + 5752224 * 2 ^ 59
def prefixEnd_5752224 : Nat := 4983230072969 + 3 ^ 40 * 5752224 * 2
def baseEnd_5752224 : Nat := 109394657197341023364667

theorem tailTrace_5752224 : CollatzResearch.WordTrace tailWord_5752224 prefixEnd_5752224 109394657197341023364667 := by
  unfold tailWord_5752224
  simp only [CollatzResearch.WordTrace]
  refine ⟨104900422556341162245659863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139867230075121549660879817 104900422556341162245659863)
  ·
    refine ⟨157350633834511743368489795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104900422556341162245659863 157350633834511743368489795)
    ·
      refine ⟨236025950751767615052734693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157350633834511743368489795 236025950751767615052734693)
      ·
        refine ⟨44254865765956427822387755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236025950751767615052734693 44254865765956427822387755)
        ·
          refine ⟨66382298648934641733581633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44254865765956427822387755 66382298648934641733581633)
          ·
            refine ⟨49786723986700981300186225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66382298648934641733581633 49786723986700981300186225)
            ·
              refine ⟨37340042990025735975139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49786723986700981300186225 37340042990025735975139669)
              ·
                refine ⟨109394657197341023364667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37340042990025735975139669 109394657197341023364667)
                ·
                  rfl

theorem cell23_5752224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_5752224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752224 prefixEnd_5752224 := by exact prefixLift 5752224
  have htrace : WordTrace (prefixWord ++ tailWord_5752224) baseStart_5752224 baseEnd_5752224 := by
    simpa [prefixWord, tailWord_5752224, baseEnd_5752224] using wordTrace_append hprefix tailTrace_5752224
  have hstable : (prefixWord ++ tailWord_5752224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752224).length < 2 ^ (prefixWord ++ tailWord_5752224).sum := by decide
  have hdescent : baseEnd_5752224 < baseStart_5752224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752231 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5752231 : Nat := 118140960795 + 5752231 * 2 ^ 59
def prefixEnd_5752231 : Nat := 4983230072969 + 3 ^ 40 * 5752231 * 2
def baseEnd_5752231 : Nat := 2953659338692789103458477

theorem tailTrace_5752231 : CollatzResearch.WordTrace tailWord_5752231 prefixEnd_5752231 2953659338692789103458477 := by
  unfold tailWord_5752231
  simp only [CollatzResearch.WordTrace]
  refine ⟨209801100423656964686824547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139867400282437976457883031 209801100423656964686824547)
  ·
    refine ⟨314701650635485447030236821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209801100423656964686824547 314701650635485447030236821)
    ·
      refine ⟨14751639873538380329542351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314701650635485447030236821 14751639873538380329542351)
      ·
        refine ⟨22127459810307570494313527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14751639873538380329542351 22127459810307570494313527)
        ·
          refine ⟨33191189715461355741470291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127459810307570494313527 33191189715461355741470291)
          ·
            refine ⟨49786784573192033612205437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33191189715461355741470291 49786784573192033612205437)
            ·
              refine ⟨18670044214947012604577039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49786784573192033612205437 18670044214947012604577039)
              ·
                refine ⟨28005066322420518906865559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18670044214947012604577039 28005066322420518906865559)
                ·
                  refine ⟨42007599483630778360298339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28005066322420518906865559 42007599483630778360298339)
                  ·
                    refine ⟨63011399225446167540447509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42007599483630778360298339 63011399225446167540447509)
                    ·
                      refine ⟨2953659338692789103458477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63011399225446167540447509 2953659338692789103458477)
                      ·
                        rfl

theorem cell23_5752231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5752231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752231 prefixEnd_5752231 := by exact prefixLift 5752231
  have htrace : WordTrace (prefixWord ++ tailWord_5752231) baseStart_5752231 baseEnd_5752231 := by
    simpa [prefixWord, tailWord_5752231, baseEnd_5752231] using wordTrace_append hprefix tailTrace_5752231
  have hstable : (prefixWord ++ tailWord_5752231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752231).length < 2 ^ (prefixWord ++ tailWord_5752231).sum := by decide
  have hdescent : baseEnd_5752231 < baseStart_5752231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752295 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5752295 : Nat := 118140960795 + 5752295 * 2 ^ 59
def prefixEnd_5752295 : Nat := 4983230072969 + 3 ^ 40 * 5752295 * 2
def baseEnd_5752295 : Nat := 2953692201454676853058183

theorem tailTrace_5752295 : CollatzResearch.WordTrace tailWord_5752295 prefixEnd_5752295 2953692201454676853058183 := by
  unfold tailWord_5752295
  simp only [CollatzResearch.WordTrace]
  refine ⟨209803434695425103617154339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139868956463616735744769559 209803434695425103617154339)
  ·
    refine ⟨314705152043137655425731509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209803434695425103617154339 314705152043137655425731509)
    ·
      refine ⟨29503608004044155196162329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314705152043137655425731509 29503608004044155196162329)
      ·
        refine ⟨22127706003033116397121747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29503608004044155196162329 22127706003033116397121747)
        ·
          refine ⟨33191559004549674595682621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127706003033116397121747 33191559004549674595682621)
          ·
            refine ⟨12446834626706127973380983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33191559004549674595682621 12446834626706127973380983)
            ·
              refine ⟨18670251940059191960071475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446834626706127973380983 18670251940059191960071475)
              ·
                refine ⟨28005377910088787940107213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18670251940059191960071475 28005377910088787940107213)
                ·
                  refine ⟨10502016716283295477540205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28005377910088787940107213 10502016716283295477540205)
                  ·
                    refine ⟨3938256268606235804077577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502016716283295477540205 3938256268606235804077577)
                    ·
                      refine ⟨2953692201454676853058183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938256268606235804077577 2953692201454676853058183)
                      ·
                        rfl

theorem cell23_5752295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5752295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752295 prefixEnd_5752295 := by exact prefixLift 5752295
  have htrace : WordTrace (prefixWord ++ tailWord_5752295) baseStart_5752295 baseEnd_5752295 := by
    simpa [prefixWord, tailWord_5752295, baseEnd_5752295] using wordTrace_append hprefix tailTrace_5752295
  have hstable : (prefixWord ++ tailWord_5752295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752295).length < 2 ^ (prefixWord ++ tailWord_5752295).sum := by decide
  have hdescent : baseEnd_5752295 < baseStart_5752295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752312 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_5752312 : Nat := 118140960795 + 5752312 * 2 ^ 59
def prefixEnd_5752312 : Nat := 4983230072969 + 3 ^ 40 * 5752312 * 2
def baseEnd_5752312 : Nat := 2953700930625803286545605

theorem tailTrace_5752312 : CollatzResearch.WordTrace tailWord_5752312 prefixEnd_5752312 2953700930625803286545605 := by
  unfold tailWord_5752312
  simp only [CollatzResearch.WordTrace]
  refine ⟨104902027368181757760261595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139869369824242343680348793 104902027368181757760261595)
  ·
    refine ⟨157353041052272636640392393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104902027368181757760261595 157353041052272636640392393)
    ·
      refine ⟨118014780789204477480294295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157353041052272636640392393 118014780789204477480294295)
      ·
        refine ⟨177022171183806716220441443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118014780789204477480294295 177022171183806716220441443)
        ·
          refine ⟨265533256775710074330662165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177022171183806716220441443 265533256775710074330662165)
          ·
            refine ⟨12446871411361409734249789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265533256775710074330662165 12446871411361409734249789)
            ·
              refine ⟨4667576779260528650343671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12446871411361409734249789 4667576779260528650343671)
              ·
                refine ⟨7001365168890792975515507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667576779260528650343671 7001365168890792975515507)
                ·
                  refine ⟨10502047753336189463273261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001365168890792975515507 10502047753336189463273261)
                  ·
                    refine ⟨3938267907501071048727473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502047753336189463273261 3938267907501071048727473)
                    ·
                      refine ⟨2953700930625803286545605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938267907501071048727473 2953700930625803286545605)
                      ·
                        rfl

theorem cell23_5752312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_5752312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752312 prefixEnd_5752312 := by exact prefixLift 5752312
  have htrace : WordTrace (prefixWord ++ tailWord_5752312) baseStart_5752312 baseEnd_5752312 := by
    simpa [prefixWord, tailWord_5752312, baseEnd_5752312] using wordTrace_append hprefix tailTrace_5752312
  have hstable : (prefixWord ++ tailWord_5752312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752312).length < 2 ^ (prefixWord ++ tailWord_5752312).sum := by decide
  have hdescent : baseEnd_5752312 < baseStart_5752312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752451 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 9]
def baseStart_5752451 : Nat := 118140960795 + 5752451 * 2 ^ 59
def prefixEnd_5752451 : Nat := 4983230072969 + 3 ^ 40 * 5752451 * 2
def baseEnd_5752451 : Nat := 984590768145592747569155

theorem tailTrace_5752451 : CollatzResearch.WordTrace tailWord_5752451 prefixEnd_5752451 984590768145592747569155 := by
  unfold tailWord_5752451
  simp only [CollatzResearch.WordTrace]
  refine ⟨209809124482859942259833207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139872749655239961506555471 209809124482859942259833207)
  ·
    refine ⟨314713686724289913389749811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209809124482859942259833207 314713686724289913389749811)
    ·
      refine ⟨472070530086434870084624717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314713686724289913389749811 472070530086434870084624717)
      ·
        refine ⟨177026448782413076281734269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472070530086434870084624717 177026448782413076281734269)
        ·
          refine ⟨66384918293404903605650351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177026448782413076281734269 66384918293404903605650351)
          ·
            refine ⟨99577377440107355408475527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66384918293404903605650351 99577377440107355408475527)
            ·
              refine ⟨149366066160161033112713291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99577377440107355408475527 149366066160161033112713291)
              ·
                refine ⟨224049099240241549669069937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149366066160161033112713291 224049099240241549669069937)
                ·
                  refine ⟨168036824430181162251802453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224049099240241549669069937 168036824430181162251802453)
                  ·
                    refine ⟨984590768145592747569155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168036824430181162251802453 984590768145592747569155)
                    ·
                      rfl

theorem cell23_5752451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_5752451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752451 prefixEnd_5752451 := by exact prefixLift 5752451
  have htrace : WordTrace (prefixWord ++ tailWord_5752451) baseStart_5752451 baseEnd_5752451 := by
    simpa [prefixWord, tailWord_5752451, baseEnd_5752451] using wordTrace_append hprefix tailTrace_5752451
  have hstable : (prefixWord ++ tailWord_5752451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752451).length < 2 ^ (prefixWord ++ tailWord_5752451).sum := by decide
  have hdescent : baseEnd_5752451 < baseStart_5752451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752455 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 6]
def baseStart_5752455 : Nat := 118140960795 + 5752455 * 2 ^ 59
def prefixEnd_5752455 : Nat := 4983230072969 + 3 ^ 40 * 5752455 * 2
def baseEnd_5752455 : Nat := 328197150928821803006383

theorem tailTrace_5752455 : CollatzResearch.WordTrace tailWord_5752455 prefixEnd_5752455 328197150928821803006383 := by
  unfold tailWord_5752455
  simp only [CollatzResearch.WordTrace]
  refine ⟨209809270374845450942978819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139872846916563633961985879 209809270374845450942978819)
  ·
    refine ⟨314713905562268176414468229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209809270374845450942978819 314713905562268176414468229)
    ·
      refine ⟨59008857292925283077712793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314713905562268176414468229 59008857292925283077712793)
      ·
        refine ⟨44256642969693962308284595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59008857292925283077712793 44256642969693962308284595)
        ·
          refine ⟨66384964454540943462426893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44256642969693962308284595 66384964454540943462426893)
          ·
            refine ⟨24894361670452853798410085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66384964454540943462426893 24894361670452853798410085)
            ·
              refine ⟨4667692813209910087201891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24894361670452853798410085 4667692813209910087201891)
              ·
                refine ⟨7001539219814865130802837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667692813209910087201891 7001539219814865130802837)
                ·
                  refine ⟨328197150928821803006383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7001539219814865130802837 328197150928821803006383)
                  ·
                    rfl

theorem cell23_5752455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 6].length) (baseStart_5752455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752455 prefixEnd_5752455 := by exact prefixLift 5752455
  have htrace : WordTrace (prefixWord ++ tailWord_5752455) baseStart_5752455 baseEnd_5752455 := by
    simpa [prefixWord, tailWord_5752455, baseEnd_5752455] using wordTrace_append hprefix tailTrace_5752455
  have hstable : (prefixWord ++ tailWord_5752455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752455).length < 2 ^ (prefixWord ++ tailWord_5752455).sum := by decide
  have hdescent : baseEnd_5752455 < baseStart_5752455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752502 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5752502 : Nat := 118140960795 + 5752502 * 2 ^ 59
def prefixEnd_5752502 : Nat := 4983230072969 + 3 ^ 40 * 5752502 * 2
def baseEnd_5752502 : Nat := 984599497316719181056577

theorem tailTrace_5752502 : CollatzResearch.WordTrace tailWord_5752502 prefixEnd_5752502 984599497316719181056577 := by
  unfold tailWord_5752502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113186537854698623121235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139873989737116785313293173 13113186537854698623121235)
  ·
    refine ⟨19669779806782047934681853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13113186537854698623121235 19669779806782047934681853)
    ·
      refine ⟨7376167427543267975505695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19669779806782047934681853 7376167427543267975505695)
      ·
        refine ⟨11064251141314901963258543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7376167427543267975505695 11064251141314901963258543)
        ·
          refine ⟨16596376711972352944887815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11064251141314901963258543 16596376711972352944887815)
          ·
            refine ⟨24894565067958529417331723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596376711972352944887815 24894565067958529417331723)
            ·
              refine ⟨37341847601937794125997585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24894565067958529417331723 37341847601937794125997585)
              ·
                refine ⟨28006385701453345594498189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37341847601937794125997585 28006385701453345594498189)
                ·
                  refine ⟨10502394638045004597936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28006385701453345594498189 10502394638045004597936821)
                  ·
                    refine ⟨984599497316719181056577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10502394638045004597936821 984599497316719181056577)
                    ·
                      rfl

theorem cell23_5752502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5752502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752502 prefixEnd_5752502 := by exact prefixLift 5752502
  have htrace : WordTrace (prefixWord ++ tailWord_5752502) baseStart_5752502 baseEnd_5752502 := by
    simpa [prefixWord, tailWord_5752502, baseEnd_5752502] using wordTrace_append hprefix tailTrace_5752502
  have hstable : (prefixWord ++ tailWord_5752502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752502).length < 2 ^ (prefixWord ++ tailWord_5752502).sum := by decide
  have hdescent : baseEnd_5752502 < baseStart_5752502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752588 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_5752588 : Nat := 118140960795 + 5752588 * 2 ^ 59
def prefixEnd_5752588 : Nat := 4983230072969 + 3 ^ 40 * 5752588 * 2
def baseEnd_5752588 : Nat := 984614217095481402231445

theorem tailTrace_5752588 : CollatzResearch.WordTrace tailWord_5752588 prefixEnd_5752588 984614217095481402231445 := by
  unfold tailWord_5752588
  simp only [CollatzResearch.WordTrace]
  refine ⟨104907060641681807328785209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139876080855575743105046945 104907060641681807328785209)
  ·
    refine ⟨78680295481261355496588907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104907060641681807328785209 78680295481261355496588907)
    ·
      refine ⟨118020443221892033244883361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78680295481261355496588907 118020443221892033244883361)
      ·
        refine ⟨88515332416419024933662521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118020443221892033244883361 88515332416419024933662521)
        ·
          refine ⟨66386499312314268700246891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88515332416419024933662521 66386499312314268700246891)
          ·
            refine ⟨99579748968471403050370337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66386499312314268700246891 99579748968471403050370337)
            ·
              refine ⟨74684811726353552287777753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99579748968471403050370337 74684811726353552287777753)
              ·
                refine ⟨56013608794765164215833315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74684811726353552287777753 56013608794765164215833315)
                ·
                  refine ⟨84020413192147746323749973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56013608794765164215833315 84020413192147746323749973)
                  ·
                    refine ⟨984614217095481402231445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84020413192147746323749973 984614217095481402231445)
                    ·
                      rfl

theorem cell23_5752588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_5752588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752588 prefixEnd_5752588 := by exact prefixLift 5752588
  have htrace : WordTrace (prefixWord ++ tailWord_5752588) baseStart_5752588 baseEnd_5752588 := by
    simpa [prefixWord, tailWord_5752588, baseEnd_5752588] using wordTrace_append hprefix tailTrace_5752588
  have hstable : (prefixWord ++ tailWord_5752588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752588).length < 2 ^ (prefixWord ++ tailWord_5752588).sum := by decide
  have hdescent : baseEnd_5752588 < baseStart_5752588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752596 : List Nat := [2, 4, 4, 1, 2, 1, 9]
def baseStart_5752596 : Nat := 118140960795 + 5752596 * 2 ^ 59
def prefixEnd_5752596 : Nat := 4983230072969 + 3 ^ 40 * 5752596 * 2
def baseEnd_5752596 : Nat := 36467243939897286115979

theorem tailTrace_5752596 : CollatzResearch.WordTrace tailWord_5752596 prefixEnd_5752596 36467243939897286115979 := by
  unfold tailWord_5752596
  simp only [CollatzResearch.WordTrace]
  refine ⟨104907206533667316011930821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139876275378223088015907761 104907206533667316011930821)
  ·
    refine ⟨19670101225062621752237029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104907206533667316011930821 19670101225062621752237029)
    ·
      refine ⟨3688143979699241578544443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19670101225062621752237029 3688143979699241578544443)
      ·
        refine ⟨5532215969548862367816665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688143979699241578544443 5532215969548862367816665)
        ·
          refine ⟨4149161977161646775862499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5532215969548862367816665 4149161977161646775862499)
          ·
            refine ⟨6223742965742470163793749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149161977161646775862499 6223742965742470163793749)
            ·
              refine ⟨36467243939897286115979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6223742965742470163793749 36467243939897286115979)
              ·
                rfl

theorem cell23_5752596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 9].length) (baseStart_5752596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752596 prefixEnd_5752596 := by exact prefixLift 5752596
  have htrace : WordTrace (prefixWord ++ tailWord_5752596) baseStart_5752596 baseEnd_5752596 := by
    simpa [prefixWord, tailWord_5752596, baseEnd_5752596] using wordTrace_append hprefix tailTrace_5752596
  have hstable : (prefixWord ++ tailWord_5752596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752596).length < 2 ^ (prefixWord ++ tailWord_5752596).sum := by decide
  have hdescent : baseEnd_5752596 < baseStart_5752596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752599 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5752599 : Nat := 118140960795 + 5752599 * 2 ^ 59
def prefixEnd_5752599 : Nat := 4983230072969 + 3 ^ 40 * 5752599 * 2
def baseEnd_5752599 : Nat := 2953848299573643663656785

theorem tailTrace_5752599 : CollatzResearch.WordTrace tailWord_5752599 prefixEnd_5752599 2953848299573643663656785 := by
  unfold tailWord_5752599
  simp only [CollatzResearch.WordTrace]
  refine ⟨209814522486323763536220851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139876348324215842357480567 209814522486323763536220851)
  ·
    refine ⟨314721783729485645304331277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209814522486323763536220851 314721783729485645304331277)
    ·
      refine ⟨118020668898557116989124229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314721783729485645304331277 118020668898557116989124229)
      ·
        refine ⟨22128875418479459435460793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118020668898557116989124229 22128875418479459435460793)
        ·
          refine ⟨16596656563859594576595595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22128875418479459435460793 16596656563859594576595595)
          ·
            refine ⟨24894984845789391864893393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596656563859594576595595 24894984845789391864893393)
            ·
              refine ⟨18671238634342043898670045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24894984845789391864893393 18671238634342043898670045)
              ·
                refine ⟨7001714487878266462001267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18671238634342043898670045 7001714487878266462001267)
                ·
                  refine ⟨10502571731817399693001901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001714487878266462001267 10502571731817399693001901)
                  ·
                    refine ⟨3938464399431524884875713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502571731817399693001901 3938464399431524884875713)
                    ·
                      refine ⟨2953848299573643663656785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938464399431524884875713 2953848299573643663656785)
                      ·
                        rfl

theorem cell23_5752599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5752599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752599 prefixEnd_5752599 := by exact prefixLift 5752599
  have htrace : WordTrace (prefixWord ++ tailWord_5752599) baseStart_5752599 baseEnd_5752599 := by
    simpa [prefixWord, tailWord_5752599, baseEnd_5752599] using wordTrace_append hprefix tailTrace_5752599
  have hstable : (prefixWord ++ tailWord_5752599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752599).length < 2 ^ (prefixWord ++ tailWord_5752599).sum := by decide
  have hdescent : baseEnd_5752599 < baseStart_5752599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752633 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5752633 : Nat := 118140960795 + 5752633 * 2 ^ 59
def prefixEnd_5752633 : Nat := 4983230072969 + 3 ^ 40 * 5752633 * 2
def baseEnd_5752633 : Nat := 2953865757915896530631629

theorem tailTrace_5752633 : CollatzResearch.WordTrace tailWord_5752633 prefixEnd_5752633 2953865757915896530631629 := by
  unfold tailWord_5752633
  simp only [CollatzResearch.WordTrace]
  refine ⟨209815762568200587342958553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139877175045467058228639035 209815762568200587342958553)
  ·
    refine ⟨157361821926150440507218915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209815762568200587342958553 157361821926150440507218915)
    ·
      refine ⟨236042732889225660760828373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157361821926150440507218915 236042732889225660760828373)
      ·
        refine ⟨5532251552091226424081915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 236042732889225660760828373 5532251552091226424081915)
        ·
          refine ⟨8298377328136839636122873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532251552091226424081915 8298377328136839636122873)
          ·
            refine ⟨6223782996102629727092155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8298377328136839636122873 6223782996102629727092155)
            ·
              refine ⟨9335674494153944590638233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223782996102629727092155 9335674494153944590638233)
              ·
                refine ⟨7001755870615458442978675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335674494153944590638233 7001755870615458442978675)
                ·
                  refine ⟨10502633805923187664468013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001755870615458442978675 10502633805923187664468013)
                  ·
                    refine ⟨3938487677221195374175505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502633805923187664468013 3938487677221195374175505)
                    ·
                      refine ⟨2953865757915896530631629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938487677221195374175505 2953865757915896530631629)
                      ·
                        rfl

theorem cell23_5752633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5752633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752633 prefixEnd_5752633 := by exact prefixLift 5752633
  have htrace : WordTrace (prefixWord ++ tailWord_5752633) baseStart_5752633 baseEnd_5752633 := by
    simpa [prefixWord, tailWord_5752633, baseEnd_5752633] using wordTrace_append hprefix tailTrace_5752633
  have hstable : (prefixWord ++ tailWord_5752633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752633).length < 2 ^ (prefixWord ++ tailWord_5752633).sum := by decide
  have hdescent : baseEnd_5752633 < baseStart_5752633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752646 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5752646 : Nat := 118140960795 + 5752646 * 2 ^ 59
def prefixEnd_5752646 : Nat := 4983230072969 + 3 ^ 40 * 5752646 * 2
def baseEnd_5752646 : Nat := 2953872433164404979769069

theorem tailTrace_5752646 : CollatzResearch.WordTrace tailWord_5752646 prefixEnd_5752646 2953872433164404979769069 := by
  unfold tailWord_5752646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556757397411046580099431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139877491144768993708787861 6556757397411046580099431)
  ·
    refine ⟨9835136096116569870149147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6556757397411046580099431 9835136096116569870149147)
    ·
      refine ⟨14752704144174854805223721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835136096116569870149147 14752704144174854805223721)
      ·
        refine ⟨11064528108131141103917791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14752704144174854805223721 11064528108131141103917791)
        ·
          refine ⟨16596792162196711655876687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11064528108131141103917791 16596792162196711655876687)
          ·
            refine ⟨24895188243295067483815031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596792162196711655876687 24895188243295067483815031)
            ·
              refine ⟨37342782364942601225722547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24895188243295067483815031 37342782364942601225722547)
              ·
                refine ⟨56014173547413901838583821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37342782364942601225722547 56014173547413901838583821)
                ·
                  refine ⟨21005315080280213189468933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56014173547413901838583821 21005315080280213189468933)
                  ·
                    refine ⟨3938496577552539973025425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21005315080280213189468933 3938496577552539973025425)
                    ·
                      refine ⟨2953872433164404979769069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938496577552539973025425 2953872433164404979769069)
                      ·
                        rfl

theorem cell23_5752646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5752646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752646 prefixEnd_5752646 := by exact prefixLift 5752646
  have htrace : WordTrace (prefixWord ++ tailWord_5752646) baseStart_5752646 baseEnd_5752646 := by
    simpa [prefixWord, tailWord_5752646, baseEnd_5752646] using wordTrace_append hprefix tailTrace_5752646
  have hstable : (prefixWord ++ tailWord_5752646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752646).length < 2 ^ (prefixWord ++ tailWord_5752646).sum := by decide
  have hdescent : baseEnd_5752646 < baseStart_5752646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752665 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_5752665 : Nat := 118140960795 + 5752665 * 2 ^ 59
def prefixEnd_5752665 : Nat := 4983230072969 + 3 ^ 40 * 5752665 * 2
def baseEnd_5752665 : Nat := 984627396432280135143827

theorem tailTrace_5752665 : CollatzResearch.WordTrace tailWord_5752665 prefixEnd_5752665 984627396432280135143827 := by
  unfold tailWord_5752665
  simp only [CollatzResearch.WordTrace]
  refine ⟨209816929704084656808123449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139877953136056437872082299 209816929704084656808123449)
  ·
    refine ⟨157362697278063492606092587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209816929704084656808123449 157362697278063492606092587)
    ·
      refine ⟨236044045917095238909138881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157362697278063492606092587 236044045917095238909138881)
      ·
        refine ⟨177033034437821429181854161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236044045917095238909138881 177033034437821429181854161)
        ·
          refine ⟨132774775828366071886390621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177033034437821429181854161 132774775828366071886390621)
          ·
            refine ⟨49790540935637276957396483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132774775828366071886390621 49790540935637276957396483)
            ·
              refine ⟨74685811403455915436094725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49790540935637276957396483 74685811403455915436094725)
              ·
                refine ⟨14003589638147984144267761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74685811403455915436094725 14003589638147984144267761)
                ·
                  refine ⟨10502692228610988108200821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14003589638147984144267761 10502692228610988108200821)
                  ·
                    refine ⟨984627396432280135143827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10502692228610988108200821 984627396432280135143827)
                    ·
                      rfl

theorem cell23_5752665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_5752665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752665 prefixEnd_5752665 := by exact prefixLift 5752665
  have htrace : WordTrace (prefixWord ++ tailWord_5752665) baseStart_5752665 baseEnd_5752665 := by
    simpa [prefixWord, tailWord_5752665, baseEnd_5752665] using wordTrace_append hprefix tailTrace_5752665
  have hstable : (prefixWord ++ tailWord_5752665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752665).length < 2 ^ (prefixWord ++ tailWord_5752665).sum := by decide
  have hdescent : baseEnd_5752665 < baseStart_5752665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752672 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2]
def baseStart_5752672 : Nat := 118140960795 + 5752672 * 2 ^ 59
def prefixEnd_5752672 : Nat := 4983230072969 + 3 ^ 40 * 5752672 * 2
def baseEnd_5752672 : Nat := 2953885783661421878043949

theorem tailTrace_5752672 : CollatzResearch.WordTrace tailWord_5752672 prefixEnd_5752672 2953885783661421878043949 := by
  unfold tailWord_5752672
  simp only [CollatzResearch.WordTrace]
  refine ⟨104908592507529648501814135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139878123343372864669085513 104908592507529648501814135)
  ·
    refine ⟨157362888761294472752721203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104908592507529648501814135 157362888761294472752721203)
    ·
      refine ⟨236044333141941709129081805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157362888761294472752721203 236044333141941709129081805)
      ·
        refine ⟨88516624928228140923405677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236044333141941709129081805 88516624928228140923405677)
        ·
          refine ⟨33193734348085552846277129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88516624928228140923405677 33193734348085552846277129)
          ·
            refine ⟨24895300761064164634707847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33193734348085552846277129 24895300761064164634707847)
            ·
              refine ⟨37342951141596246952061771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24895300761064164634707847 37342951141596246952061771)
              ·
                refine ⟨56014426712394370428092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37342951141596246952061771 56014426712394370428092657)
                ·
                  refine ⟨42010820034295777821069493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56014426712394370428092657 42010820034295777821069493)
                  ·
                    refine ⟨3938514378215229170725265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42010820034295777821069493 3938514378215229170725265)
                    ·
                      refine ⟨2953885783661421878043949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938514378215229170725265 2953885783661421878043949)
                      ·
                        rfl

theorem cell23_5752672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_5752672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752672 prefixEnd_5752672 := by exact prefixLift 5752672
  have htrace : WordTrace (prefixWord ++ tailWord_5752672) baseStart_5752672 baseEnd_5752672 := by
    simpa [prefixWord, tailWord_5752672, baseEnd_5752672] using wordTrace_append hprefix tailTrace_5752672
  have hstable : (prefixWord ++ tailWord_5752672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752672).length < 2 ^ (prefixWord ++ tailWord_5752672).sum := by decide
  have hdescent : baseEnd_5752672 < baseStart_5752672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752725 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 8]
def baseStart_5752725 : Nat := 118140960795 + 5752725 * 2 ^ 59
def prefixEnd_5752725 : Nat := 4983230072969 + 3 ^ 40 * 5752725 * 2
def baseEnd_5752725 : Nat := 328212555348456685631245

theorem tailTrace_5752725 : CollatzResearch.WordTrace tailWord_5752725 prefixEnd_5752725 328212555348456685631245 := by
  unfold tailWord_5752725
  simp only [CollatzResearch.WordTrace]
  refine ⟨209819118083867287055307629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139879412055911524703538419 209819118083867287055307629)
  ·
    refine ⟨78682169281450232645740361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209819118083867287055307629 78682169281450232645740361)
    ·
      refine ⟨59011626961087674484305271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78682169281450232645740361 59011626961087674484305271)
      ·
        refine ⟨88517440441631511726457907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59011626961087674484305271 88517440441631511726457907)
        ·
          refine ⟨132776160662447267589686861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88517440441631511726457907 132776160662447267589686861)
          ·
            refine ⟨49791060248417725346132573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132776160662447267589686861 49791060248417725346132573)
            ·
              refine ⟨18671647593156647004799715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49791060248417725346132573 18671647593156647004799715)
              ·
                refine ⟨28007471389734970507199573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18671647593156647004799715 28007471389734970507199573)
                ·
                  refine ⟨328212555348456685631245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28007471389734970507199573 328212555348456685631245)
                  ·
                    rfl

theorem cell23_5752725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_5752725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752725 prefixEnd_5752725 := by exact prefixLift 5752725
  have htrace : WordTrace (prefixWord ++ tailWord_5752725) baseStart_5752725 baseEnd_5752725 := by
    simpa [prefixWord, tailWord_5752725, baseEnd_5752725] using wordTrace_append hprefix tailTrace_5752725
  have hstable : (prefixWord ++ tailWord_5752725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752725).length < 2 ^ (prefixWord ++ tailWord_5752725).sum := by decide
  have hdescent : baseEnd_5752725 < baseStart_5752725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752729 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 1, 4]
def baseStart_5752729 : Nat := 118140960795 + 5752729 * 2 ^ 59
def prefixEnd_5752729 : Nat := 4983230072969 + 3 ^ 40 * 5752729 * 2
def baseEnd_5752729 : Nat := 984638350686242718343729

theorem tailTrace_5752729 : CollatzResearch.WordTrace tailWord_5752729 prefixEnd_5752729 984638350686242718343729 := by
  unfold tailWord_5752729
  simp only [CollatzResearch.WordTrace]
  refine ⟨209819263975852795738453241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139879509317235197158968827 209819263975852795738453241)
  ·
    refine ⟨157364447981889596803839931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209819263975852795738453241 157364447981889596803839931)
    ·
      refine ⟨236046671972834395205759897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157364447981889596803839931 236046671972834395205759897)
      ·
        refine ⟨177035003979625796404319923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236046671972834395205759897 177035003979625796404319923)
        ·
          refine ⟨265552505969438694606479885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177035003979625796404319923 265552505969438694606479885)
          ·
            refine ⟨99582189738539510477429957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265552505969438694606479885 99582189738539510477429957)
            ·
              refine ⟨18671660575976158214518117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99582189738539510477429957 18671660575976158214518117)
              ·
                refine ⟨3500936357995529665222147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18671660575976158214518117 3500936357995529665222147)
                ·
                  refine ⟨5251404536993294497833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500936357995529665222147 5251404536993294497833221)
                  ·
                    refine ⟨984638350686242718343729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5251404536993294497833221 984638350686242718343729)
                    ·
                      rfl

theorem cell23_5752729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_5752729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752729 prefixEnd_5752729 := by exact prefixLift 5752729
  have htrace : WordTrace (prefixWord ++ tailWord_5752729) baseStart_5752729 baseEnd_5752729 := by
    simpa [prefixWord, tailWord_5752729, baseEnd_5752729] using wordTrace_append hprefix tailTrace_5752729
  have hstable : (prefixWord ++ tailWord_5752729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752729).length < 2 ^ (prefixWord ++ tailWord_5752729).sum := by decide
  have hdescent : baseEnd_5752729 < baseStart_5752729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752779 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 2, 3, 2]
def baseStart_5752779 : Nat := 118140960795 + 5752779 * 2 ^ 59
def prefixEnd_5752779 : Nat := 4983230072969 + 3 ^ 40 * 5752779 * 2
def baseEnd_5752779 : Nat := 2953940726091452959405957

theorem tailTrace_5752779 : CollatzResearch.WordTrace tailWord_5752779 prefixEnd_5752779 2953940726091452959405957 := by
  unfold tailWord_5752779
  simp only [CollatzResearch.WordTrace]
  refine ⟨209821087625671654277773391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139880725083781102851848927 209821087625671654277773391)
  ·
    refine ⟨314731631438507481416660087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209821087625671654277773391 314731631438507481416660087)
    ·
      refine ⟨472097447157761222124990131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314731631438507481416660087 472097447157761222124990131)
      ·
        refine ⟨708146170736641833187485197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472097447157761222124990131 708146170736641833187485197)
        ·
          refine ⟨265554814026240687445306949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708146170736641833187485197 265554814026240687445306949)
          ·
            refine ⟨49791527629920128895995053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265554814026240687445306949 49791527629920128895995053)
            ·
              refine ⟨18671822861220048335998145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49791527629920128895995053 18671822861220048335998145)
              ·
                refine ⟨14003867145915036251998609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18671822861220048335998145 14003867145915036251998609)
                ·
                  refine ⟨10502900359436277188998957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14003867145915036251998609 10502900359436277188998957)
                  ·
                    refine ⟨3938587634788603945874609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502900359436277188998957 3938587634788603945874609)
                    ·
                      refine ⟨2953940726091452959405957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938587634788603945874609 2953940726091452959405957)
                      ·
                        rfl

theorem cell23_5752779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3, 2].length) (baseStart_5752779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752779 prefixEnd_5752779 := by exact prefixLift 5752779
  have htrace : WordTrace (prefixWord ++ tailWord_5752779) baseStart_5752779 baseEnd_5752779 := by
    simpa [prefixWord, tailWord_5752779, baseEnd_5752779] using wordTrace_append hprefix tailTrace_5752779
  have hstable : (prefixWord ++ tailWord_5752779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752779).length < 2 ^ (prefixWord ++ tailWord_5752779).sum := by decide
  have hdescent : baseEnd_5752779 < baseStart_5752779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752785 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_5752785 : Nat := 118140960795 + 5752785 * 2 ^ 59
def prefixEnd_5752785 : Nat := 4983230072969 + 3 ^ 40 * 5752785 * 2
def baseEnd_5752785 : Nat := 984647935658459978643643

theorem tailTrace_5752785 : CollatzResearch.WordTrace tailWord_5752785 prefixEnd_5752785 984647935658459978643643 := by
  unfold tailWord_5752785
  simp only [CollatzResearch.WordTrace]
  refine ⟨209821306463649917302491809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139880870975766611534994539 209821306463649917302491809)
  ·
    refine ⟨157365979847737437976868857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209821306463649917302491809 157365979847737437976868857)
    ·
      refine ⟨118024484885803078482651643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157365979847737437976868857 118024484885803078482651643)
      ·
        refine ⟨177036727328704617723977465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118024484885803078482651643 177036727328704617723977465)
        ·
          refine ⟨132777545496528463292983099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177036727328704617723977465 132777545496528463292983099)
          ·
            refine ⟨199166318244792694939474649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132777545496528463292983099 199166318244792694939474649)
            ·
              refine ⟨149374738683594521204605987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199166318244792694939474649 149374738683594521204605987)
              ·
                refine ⟨224062108025391781806908981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149374738683594521204605987 224062108025391781806908981)
                ·
                  refine ⟨21005822627380479544397717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224062108025391781806908981 21005822627380479544397717)
                  ·
                    refine ⟨984647935658459978643643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21005822627380479544397717 984647935658459978643643)
                    ·
                      rfl

theorem cell23_5752785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_5752785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752785 prefixEnd_5752785 := by exact prefixLift 5752785
  have htrace : WordTrace (prefixWord ++ tailWord_5752785) baseStart_5752785 baseEnd_5752785 := by
    simpa [prefixWord, tailWord_5752785, baseEnd_5752785] using wordTrace_append hprefix tailTrace_5752785
  have hstable : (prefixWord ++ tailWord_5752785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752785).length < 2 ^ (prefixWord ++ tailWord_5752785).sum := by decide
  have hdescent : baseEnd_5752785 < baseStart_5752785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752792 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5752792 : Nat := 118140960795 + 5752792 * 2 ^ 59
def prefixEnd_5752792 : Nat := 4983230072969 + 3 ^ 40 * 5752792 * 2
def baseEnd_5752792 : Nat := 2953947401339961408543397

theorem tailTrace_5752792 : CollatzResearch.WordTrace tailWord_5752792 prefixEnd_5752792 2953947401339961408543397 := by
  unfold tailWord_5752792
  simp only [CollatzResearch.WordTrace]
  refine ⟨104910780887312278748998315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139881041183083038331997753 104910780887312278748998315)
  ·
    refine ⟨157366171330968418123497473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104910780887312278748998315 157366171330968418123497473)
    ·
      refine ⟨118024628498226313592623105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157366171330968418123497473 118024628498226313592623105)
      ·
        refine ⟨88518471373669735194467329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118024628498226313592623105 88518471373669735194467329)
        ·
          refine ⟨66388853530252301395850497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88518471373669735194467329 66388853530252301395850497)
          ·
            refine ⟨49791640147689226046887873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66388853530252301395850497 49791640147689226046887873)
            ·
              refine ⟨37343730110766919535165905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49791640147689226046887873 37343730110766919535165905)
              ·
                refine ⟨28007797583075189651374429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37343730110766919535165905 28007797583075189651374429)
                ·
                  refine ⟨10502924093653196119265411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28007797583075189651374429 10502924093653196119265411)
                  ·
                    refine ⟨15754386140479794178898117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10502924093653196119265411 15754386140479794178898117)
                    ·
                      refine ⟨2953947401339961408543397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15754386140479794178898117 2953947401339961408543397)
                      ·
                        rfl

theorem cell23_5752792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5752792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752792 prefixEnd_5752792 := by exact prefixLift 5752792
  have htrace : WordTrace (prefixWord ++ tailWord_5752792) baseStart_5752792 baseEnd_5752792 := by
    simpa [prefixWord, tailWord_5752792, baseEnd_5752792] using wordTrace_append hprefix tailTrace_5752792
  have hstable : (prefixWord ++ tailWord_5752792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752792).length < 2 ^ (prefixWord ++ tailWord_5752792).sum := by decide
  have hdescent : baseEnd_5752792 < baseStart_5752792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752815 : List Nat := [1, 1, 2, 1, 4, 2, 1, 11]
def baseStart_5752815 : Nat := 118140960795 + 5752815 * 2 ^ 59
def prefixEnd_5752815 : Nat := 4983230072969 + 3 ^ 40 * 5752815 * 2
def baseEnd_5752815 : Nat := 109405896718333882168733

theorem tailTrace_5752815 : CollatzResearch.WordTrace tailWord_5752815 prefixEnd_5752815 109405896718333882168733 := by
  unfold tailWord_5752815
  simp only [CollatzResearch.WordTrace]
  refine ⟨209822400653541232426083899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139881600435694154950722599 209822400653541232426083899)
  ·
    refine ⟨314733600980311848639125849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209822400653541232426083899 314733600980311848639125849)
    ·
      refine ⟨236050200735233886479344387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314733600980311848639125849 236050200735233886479344387)
      ·
        refine ⟨354075301102850829719016581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236050200735233886479344387 354075301102850829719016581)
        ·
          refine ⟨66389118956784530572315609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354075301102850829719016581 66389118956784530572315609)
          ·
            refine ⟨49791839217588397929236707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66389118956784530572315609 49791839217588397929236707)
            ·
              refine ⟨74687758826382596893855061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49791839217588397929236707 74687758826382596893855061)
              ·
                refine ⟨109405896718333882168733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74687758826382596893855061 109405896718333882168733)
                ·
                  rfl

theorem cell23_5752815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 11].length) (baseStart_5752815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752815 prefixEnd_5752815 := by exact prefixLift 5752815
  have htrace : WordTrace (prefixWord ++ tailWord_5752815) baseStart_5752815 baseEnd_5752815 := by
    simpa [prefixWord, tailWord_5752815, baseEnd_5752815] using wordTrace_append hprefix tailTrace_5752815
  have hstable : (prefixWord ++ tailWord_5752815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752815).length < 2 ^ (prefixWord ++ tailWord_5752815).sum := by decide
  have hdescent : baseEnd_5752815 < baseStart_5752815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752829 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_5752829 : Nat := 118140960795 + 5752829 * 2 ^ 59
def prefixEnd_5752829 : Nat := 4983230072969 + 3 ^ 40 * 5752829 * 2
def baseEnd_5752829 : Nat := 2953966400124177763780727

theorem tailTrace_5752829 : CollatzResearch.WordTrace tailWord_5752829 prefixEnd_5752829 2953966400124177763780727 := by
  unfold tailWord_5752829
  simp only [CollatzResearch.WordTrace]
  refine ⟨209822911275490512817093541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139881940850327008544729027 209822911275490512817093541)
  ·
    refine ⟨39341795864154471153205039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209822911275490512817093541 39341795864154471153205039)
    ·
      refine ⟨59012693796231706729807559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39341795864154471153205039 59012693796231706729807559)
      ·
        refine ⟨88519040694347560094711339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59012693796231706729807559 88519040694347560094711339)
        ·
          refine ⟨132778561041521340142067009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88519040694347560094711339 132778561041521340142067009)
          ·
            refine ⟨99583920781141005106550257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132778561041521340142067009 99583920781141005106550257)
            ·
              refine ⟨74687940585855753829912693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99583920781141005106550257 74687940585855753829912693)
              ·
                refine ⟨7001994429923976921554315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74687940585855753829912693 7001994429923976921554315)
                ·
                  refine ⟨10502991644885965382331473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001994429923976921554315 10502991644885965382331473)
                  ·
                    refine ⟨7877243733664474036748605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10502991644885965382331473 7877243733664474036748605)
                    ·
                      refine ⟨2953966400124177763780727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877243733664474036748605 2953966400124177763780727)
                      ·
                        rfl

theorem cell23_5752829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_5752829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752829 prefixEnd_5752829 := by exact prefixLift 5752829
  have htrace : WordTrace (prefixWord ++ tailWord_5752829) baseStart_5752829 baseEnd_5752829 := by
    simpa [prefixWord, tailWord_5752829, baseEnd_5752829] using wordTrace_append hprefix tailTrace_5752829
  have hstable : (prefixWord ++ tailWord_5752829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752829).length < 2 ^ (prefixWord ++ tailWord_5752829).sum := by decide
  have hdescent : baseEnd_5752829 < baseStart_5752829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752843 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 1, 2, 2]
def baseStart_5752843 : Nat := 118140960795 + 5752843 * 2 ^ 59
def prefixEnd_5752843 : Nat := 4983230072969 + 3 ^ 40 * 5752843 * 2
def baseEnd_5752843 : Nat := 2953973588853340709005663

theorem tailTrace_5752843 : CollatzResearch.WordTrace tailWord_5752843 prefixEnd_5752843 2953973588853340709005663 := by
  unfold tailWord_5752843
  simp only [CollatzResearch.WordTrace]
  refine ⟨209823421897439793208103183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139882281264959862138735455 209823421897439793208103183)
  ·
    refine ⟨314735132846159689812154775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209823421897439793208103183 314735132846159689812154775)
    ·
      refine ⟨472102699269239534718232163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314735132846159689812154775 472102699269239534718232163)
      ·
        refine ⟨708154048903859302077348245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472102699269239534718232163 708154048903859302077348245)
        ·
          refine ⟨33194721042368404784875699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 708154048903859302077348245 33194721042368404784875699)
          ·
            refine ⟨49792081563552607177313549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33194721042368404784875699 49792081563552607177313549)
            ·
              refine ⟨18672030586332227691492581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49792081563552607177313549 18672030586332227691492581)
              ·
                refine ⟨3501005734937292692154859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18672030586332227691492581 3501005734937292692154859)
                ·
                  refine ⟨5251508602405939038232289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501005734937292692154859 5251508602405939038232289)
                  ·
                    refine ⟨3938631451804454278674217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5251508602405939038232289 3938631451804454278674217)
                    ·
                      refine ⟨2953973588853340709005663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938631451804454278674217 2953973588853340709005663)
                      ·
                        rfl

theorem cell23_5752843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 2, 2].length) (baseStart_5752843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752843 prefixEnd_5752843 := by exact prefixLift 5752843
  have htrace : WordTrace (prefixWord ++ tailWord_5752843) baseStart_5752843 baseEnd_5752843 := by
    simpa [prefixWord, tailWord_5752843, baseEnd_5752843] using wordTrace_append hprefix tailTrace_5752843
  have hstable : (prefixWord ++ tailWord_5752843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752843).length < 2 ^ (prefixWord ++ tailWord_5752843).sum := by decide
  have hdescent : baseEnd_5752843 < baseStart_5752843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752892 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_5752892 : Nat := 118140960795 + 5752892 * 2 ^ 59
def prefixEnd_5752892 : Nat := 4983230072969 + 3 ^ 40 * 5752892 * 2
def baseEnd_5752892 : Nat := 984666249801803672430979

theorem tailTrace_5752892 : CollatzResearch.WordTrace tailWord_5752892 prefixEnd_5752892 984666249801803672430979 := by
  unfold tailWord_5752892
  simp only [CollatzResearch.WordTrace]
  refine ⟨104912604537131137288318465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139883472716174849717757953 104912604537131137288318465)
  ·
    refine ⟨78684453402848352966238849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104912604537131137288318465 78684453402848352966238849)
    ·
      refine ⟨59013340052136264724679137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78684453402848352966238849 59013340052136264724679137)
      ·
        refine ⟨44260005039102198543509353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59013340052136264724679137 44260005039102198543509353)
        ·
          refine ⟨33195003779326648907632015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44260005039102198543509353 33195003779326648907632015)
          ·
            refine ⟨49792505668989973361448023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33195003779326648907632015 49792505668989973361448023)
            ·
              refine ⟨74688758503484960042172035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49792505668989973361448023 74688758503484960042172035)
              ·
                refine ⟨112033137755227440063258053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74688758503484960042172035 112033137755227440063258053)
                ·
                  refine ⟨21006213329105145011860885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112033137755227440063258053 21006213329105145011860885)
                  ·
                    refine ⟨984666249801803672430979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21006213329105145011860885 984666249801803672430979)
                    ·
                      rfl

theorem cell23_5752892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_5752892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752892 prefixEnd_5752892 := by exact prefixLift 5752892
  have htrace : WordTrace (prefixWord ++ tailWord_5752892) baseStart_5752892 baseEnd_5752892 := by
    simpa [prefixWord, tailWord_5752892, baseEnd_5752892] using wordTrace_append hprefix tailTrace_5752892
  have hstable : (prefixWord ++ tailWord_5752892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752892).length < 2 ^ (prefixWord ++ tailWord_5752892).sum := by decide
  have hdescent : baseEnd_5752892 < baseStart_5752892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752909 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_5752909 : Nat := 118140960795 + 5752909 * 2 ^ 59
def prefixEnd_5752909 : Nat := 4983230072969 + 3 ^ 40 * 5752909 * 2
def baseEnd_5752909 : Nat := 984669159525512483593453

theorem tailTrace_5752909 : CollatzResearch.WordTrace tailWord_5752909 prefixEnd_5752909 984669159525512483593453 := by
  unfold tailWord_5752909
  simp only [CollatzResearch.WordTrace]
  refine ⟨209825829115200686480005781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139883886076800457653337187 209825829115200686480005781)
  ·
    refine ⟨9835585739775032178750271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209825829115200686480005781 9835585739775032178750271)
    ·
      refine ⟨14753378609662548268125407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835585739775032178750271 14753378609662548268125407)
      ·
        refine ⟨22130067914493822402188111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14753378609662548268125407 22130067914493822402188111)
        ·
          refine ⟨33195101871740733603282167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22130067914493822402188111 33195101871740733603282167)
          ·
            refine ⟨49792652807611100404923251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33195101871740733603282167 49792652807611100404923251)
            ·
              refine ⟨74688979211416650607384877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49792652807611100404923251 74688979211416650607384877)
              ·
                refine ⟨28008367204281243977769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74688979211416650607384877 28008367204281243977769329)
                ·
                  refine ⟨21006275403210932983326997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28008367204281243977769329 21006275403210932983326997)
                  ·
                    refine ⟨984669159525512483593453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21006275403210932983326997 984669159525512483593453)
                    ·
                      rfl

theorem cell23_5752909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_5752909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752909 prefixEnd_5752909 := by exact prefixLift 5752909
  have htrace : WordTrace (prefixWord ++ tailWord_5752909) baseStart_5752909 baseEnd_5752909 := by
    simpa [prefixWord, tailWord_5752909, baseEnd_5752909] using wordTrace_append hprefix tailTrace_5752909
  have hstable : (prefixWord ++ tailWord_5752909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752909).length < 2 ^ (prefixWord ++ tailWord_5752909).sum := by decide
  have hdescent : baseEnd_5752909 < baseStart_5752909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5752922 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_5752922 : Nat := 118140960795 + 5752922 * 2 ^ 59
def prefixEnd_5752922 : Nat := 4983230072969 + 3 ^ 40 * 5752922 * 2
def baseEnd_5752922 : Nat := 328223794869449544435311

theorem tailTrace_5752922 : CollatzResearch.WordTrace tailWord_5752922 prefixEnd_5752922 328223794869449544435311 := by
  unfold tailWord_5752922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52456575816038397425057255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139884202176102393133486013 52456575816038397425057255)
  ·
    refine ⟨78684863724057596137585883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52456575816038397425057255 78684863724057596137585883)
    ·
      refine ⟨118027295586086394206378825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78684863724057596137585883 118027295586086394206378825)
      ·
        refine ⟨88520471689564795654784119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118027295586086394206378825 88520471689564795654784119)
        ·
          refine ⟨132780707534347193482176179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88520471689564795654784119 132780707534347193482176179)
          ·
            refine ⟨199171061301520790223264269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132780707534347193482176179 199171061301520790223264269)
            ·
              refine ⟨74689147988070296333724101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199171061301520790223264269 74689147988070296333724101)
              ·
                refine ⟨14004215247763180562573269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74689147988070296333724101 14004215247763180562573269)
                ·
                  refine ⟨328223794869449544435311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14004215247763180562573269 328223794869449544435311)
                  ·
                    rfl

theorem cell23_5752922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_5752922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5752922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5752922 prefixEnd_5752922 := by exact prefixLift 5752922
  have htrace : WordTrace (prefixWord ++ tailWord_5752922) baseStart_5752922 baseEnd_5752922 := by
    simpa [prefixWord, tailWord_5752922, baseEnd_5752922] using wordTrace_append hprefix tailTrace_5752922
  have hstable : (prefixWord ++ tailWord_5752922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5752922).length < 2 ^ (prefixWord ++ tailWord_5752922).sum := by decide
  have hdescent : baseEnd_5752922 < baseStart_5752922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5752922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753029 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 6]
def baseStart_5753029 : Nat := 118140960795 + 5753029 * 2 ^ 59
def prefixEnd_5753029 : Nat := 4983230072969 + 3 ^ 40 * 5753029 * 2
def baseEnd_5753029 : Nat := 328229899583897442364423

theorem tailTrace_5753029 : CollatzResearch.WordTrace tailWord_5753029 prefixEnd_5753029 328229899583897442364423 := by
  unfold tailWord_5753029
  simp only [CollatzResearch.WordTrace]
  refine ⟨209830205874765946974374141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139886803916510631316249427 209830205874765946974374141)
  ·
    refine ⟨78686327203037230115390303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209830205874765946974374141 78686327203037230115390303)
    ·
      refine ⟨118029490804555845173085455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78686327203037230115390303 118029490804555845173085455)
      ·
        refine ⟨177044236206833767759628183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118029490804555845173085455 177044236206833767759628183)
        ·
          refine ⟨265566354310250651639442275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177044236206833767759628183 265566354310250651639442275)
          ·
            refine ⟨398349531465375977459163413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265566354310250651639442275 398349531465375977459163413)
            ·
              refine ⟨18672634287439498943398285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 398349531465375977459163413 18672634287439498943398285)
              ·
                refine ⟨7002237857789812103774357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18672634287439498943398285 7002237857789812103774357)
                ·
                  refine ⟨328229899583897442364423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7002237857789812103774357 328229899583897442364423)
                  ·
                    rfl

theorem cell23_5753029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_5753029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753029 prefixEnd_5753029 := by exact prefixLift 5753029
  have htrace : WordTrace (prefixWord ++ tailWord_5753029) baseStart_5753029 baseEnd_5753029 := by
    simpa [prefixWord, tailWord_5753029, baseEnd_5753029] using wordTrace_append hprefix tailTrace_5753029
  have hstable : (prefixWord ++ tailWord_5753029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753029).length < 2 ^ (prefixWord ++ tailWord_5753029).sum := by decide
  have hdescent : baseEnd_5753029 < baseStart_5753029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753056 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_5753056 : Nat := 118140960795 + 5753056 * 2 ^ 59
def prefixEnd_5753056 : Nat := 4983230072969 + 3 ^ 40 * 5753056 * 2
def baseEnd_5753056 : Nat := 2954082960232748375642183

theorem tailTrace_5753056 : CollatzResearch.WordTrace tailWord_5753056 prefixEnd_5753056 2954082960232748375642183 := by
  unfold tailWord_5753056
  simp only [CollatzResearch.WordTrace]
  refine ⟨104915595322834065292803511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139887460430445420390404681 104915595322834065292803511)
  ·
    refine ⟨157373392984251097939205267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104915595322834065292803511 157373392984251097939205267)
    ·
      refine ⟨236060089476376646908807901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157373392984251097939205267 236060089476376646908807901)
      ·
        refine ⟨88522533553641242590802963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236060089476376646908807901 88522533553641242590802963)
        ·
          refine ⟨132783800330461863886204445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88522533553641242590802963 132783800330461863886204445)
          ·
            refine ⟨49793925123923198957326667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132783800330461863886204445 49793925123923198957326667)
            ·
              refine ⟨74690887685884798435990001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49793925123923198957326667 74690887685884798435990001)
              ·
                refine ⟨56018165764413598826992501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74690887685884798435990001 56018165764413598826992501)
                ·
                  refine ⟨5251703040413774890030547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56018165764413598826992501 5251703040413774890030547)
                  ·
                    refine ⟨7877554560620662335045821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5251703040413774890030547 7877554560620662335045821)
                    ·
                      refine ⟨2954082960232748375642183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877554560620662335045821 2954082960232748375642183)
                      ·
                        rfl

theorem cell23_5753056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_5753056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753056 prefixEnd_5753056 := by exact prefixLift 5753056
  have htrace : WordTrace (prefixWord ++ tailWord_5753056) baseStart_5753056 baseEnd_5753056 := by
    simpa [prefixWord, tailWord_5753056, baseEnd_5753056] using wordTrace_append hprefix tailTrace_5753056
  have hstable : (prefixWord ++ tailWord_5753056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753056).length < 2 ^ (prefixWord ++ tailWord_5753056).sum := by decide
  have hdescent : baseEnd_5753056 < baseStart_5753056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753063 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 6]
def baseStart_5753063 : Nat := 118140960795 + 5753063 * 2 ^ 59
def prefixEnd_5753063 : Nat := 4983230072969 + 3 ^ 40 * 5753063 * 2
def baseEnd_5753063 : Nat := 328231839399703316472739

theorem tailTrace_5753063 : CollatzResearch.WordTrace tailWord_5753063 prefixEnd_5753063 328231839399703316472739 := by
  unfold tailWord_5753063
  simp only [CollatzResearch.WordTrace]
  refine ⟨209831445956642770781111843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139887630637761847187407895 209831445956642770781111843)
  ·
    refine ⟨314747168934964156171667765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209831445956642770781111843 314747168934964156171667765)
    ·
      refine ⟨29507547087652889641093853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314747168934964156171667765 29507547087652889641093853)
      ·
        refine ⟨11065330157869833615410195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29507547087652889641093853 11065330157869833615410195)
        ·
          refine ⟨16597995236804750423115293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11065330157869833615410195 16597995236804750423115293)
          ·
            refine ⟨6224248213801781408668235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16597995236804750423115293 6224248213801781408668235)
            ·
              refine ⟨9336372320702672113002353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224248213801781408668235 9336372320702672113002353)
              ·
                refine ⟨7002279240527004084751765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336372320702672113002353 7002279240527004084751765)
                ·
                  refine ⟨328231839399703316472739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7002279240527004084751765 328231839399703316472739)
                  ·
                    rfl

theorem cell23_5753063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 6].length) (baseStart_5753063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753063 prefixEnd_5753063 := by exact prefixLift 5753063
  have htrace : WordTrace (prefixWord ++ tailWord_5753063) baseStart_5753063 baseEnd_5753063 := by
    simpa [prefixWord, tailWord_5753063, baseEnd_5753063] using wordTrace_append hprefix tailTrace_5753063
  have hstable : (prefixWord ++ tailWord_5753063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753063).length < 2 ^ (prefixWord ++ tailWord_5753063).sum := by decide
  have hdescent : baseEnd_5753063 < baseStart_5753063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753090 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_5753090 : Nat := 118140960795 + 5753090 * 2 ^ 59
def prefixEnd_5753090 : Nat := 4983230072969 + 3 ^ 40 * 5753090 * 2
def baseEnd_5753090 : Nat := 2954100418575001242617027

theorem tailTrace_5753090 : CollatzResearch.WordTrace tailWord_5753090 prefixEnd_5753090 2954100418575001242617027 := by
  unfold tailWord_5753090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52458107681886238598086181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139888287151696636261563149 52458107681886238598086181)
  ·
    refine ⟨9835895190353669737141159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52458107681886238598086181 9835895190353669737141159)
    ·
      refine ⟨14753842785530504605711739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835895190353669737141159 14753842785530504605711739)
      ·
        refine ⟨22130764178295756908567609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14753842785530504605711739 22130764178295756908567609)
        ·
          refine ⟨16598073133721817681425707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22130764178295756908567609 16598073133721817681425707)
          ·
            refine ⟨24897109700582726522138561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16598073133721817681425707 24897109700582726522138561)
            ·
              refine ⟨18672832275437044891603921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24897109700582726522138561 18672832275437044891603921)
              ·
                refine ⟨14004624206577783668702941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18672832275437044891603921 14004624206577783668702941)
                ·
                  refine ⟨5251734077466668875763603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14004624206577783668702941 5251734077466668875763603)
                  ·
                    refine ⟨7877601116200003313645405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5251734077466668875763603 7877601116200003313645405)
                    ·
                      refine ⟨2954100418575001242617027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877601116200003313645405 2954100418575001242617027)
                      ·
                        rfl

theorem cell23_5753090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_5753090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753090 prefixEnd_5753090 := by exact prefixLift 5753090
  have htrace : WordTrace (prefixWord ++ tailWord_5753090) baseStart_5753090 baseEnd_5753090 := by
    simpa [prefixWord, tailWord_5753090, baseEnd_5753090] using wordTrace_append hprefix tailTrace_5753090
  have hstable : (prefixWord ++ tailWord_5753090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753090).length < 2 ^ (prefixWord ++ tailWord_5753090).sum := by decide
  have hdescent : baseEnd_5753090 < baseStart_5753090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753099 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_5753099 : Nat := 118140960795 + 5753099 * 2 ^ 59
def prefixEnd_5753099 : Nat := 4983230072969 + 3 ^ 40 * 5753099 * 2
def baseEnd_5753099 : Nat := 2954105039900891707404485

theorem tailTrace_5753099 : CollatzResearch.WordTrace tailWord_5753099 prefixEnd_5753099 2954105039900891707404485 := by
  unfold tailWord_5753099
  simp only [CollatzResearch.WordTrace]
  refine ⟨209832758984512348929422351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139888505989674899286281567 209832758984512348929422351)
  ·
    refine ⟨314749138476768523394133527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209832758984512348929422351 314749138476768523394133527)
    ·
      refine ⟨472123707715152785091200291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314749138476768523394133527 472123707715152785091200291)
      ·
        refine ⟨708185561572729177636800437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472123707715152785091200291 708185561572729177636800437)
        ·
          refine ⟨66392396397443360403450041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 708185561572729177636800437 66392396397443360403450041)
          ·
            refine ⟨49794297298082520302587531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66392396397443360403450041 49794297298082520302587531)
            ·
              refine ⟨74691445947123780453881297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49794297298082520302587531 74691445947123780453881297)
              ·
                refine ⟨56018584460342835340410973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74691445947123780453881297 56018584460342835340410973)
                ·
                  refine ⟨21006969172628563252654115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56018584460342835340410973 21006969172628563252654115)
                  ·
                    refine ⟨31510453758942844878981173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21006969172628563252654115 31510453758942844878981173)
                    ·
                      refine ⟨2954105039900891707404485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31510453758942844878981173 2954105039900891707404485)
                      ·
                        rfl

theorem cell23_5753099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_5753099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753099 prefixEnd_5753099 := by exact prefixLift 5753099
  have htrace : WordTrace (prefixWord ++ tailWord_5753099) baseStart_5753099 baseEnd_5753099 := by
    simpa [prefixWord, tailWord_5753099, baseEnd_5753099] using wordTrace_append hprefix tailTrace_5753099
  have hstable : (prefixWord ++ tailWord_5753099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753099).length < 2 ^ (prefixWord ++ tailWord_5753099).sum := by decide
  have hdescent : baseEnd_5753099 < baseStart_5753099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753116 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5753116 : Nat := 118140960795 + 5753116 * 2 ^ 59
def prefixEnd_5753116 : Nat := 4983230072969 + 3 ^ 40 * 5753116 * 2
def baseEnd_5753116 : Nat := 2954113769072018140891907

theorem tailTrace_5753116 : CollatzResearch.WordTrace tailWord_5753116 prefixEnd_5753116 2954113769072018140891907 := by
  unfold tailWord_5753116
  simp only [CollatzResearch.WordTrace]
  refine ⟨104916689512725380416395601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139888919350300507221860801 104916689512725380416395601)
  ·
    refine ⟨78687517134544035312296701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104916689512725380416395601 78687517134544035312296701)
    ·
      refine ⟨29507818925454013242111263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78687517134544035312296701 29507818925454013242111263)
      ·
        refine ⟨44261728388181019863166895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29507818925454013242111263 44261728388181019863166895)
        ·
          refine ⟨66392592582271529794750343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44261728388181019863166895 66392592582271529794750343)
          ·
            refine ⟨99588888873407294692125515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66392592582271529794750343 99588888873407294692125515)
            ·
              refine ⟨149383333310110942038188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99588888873407294692125515 149383333310110942038188273)
              ·
                refine ⟨112037499982583206528641205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149383333310110942038188273 112037499982583206528641205)
                ·
                  refine ⟨10503515623367175612060113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112037499982583206528641205 10503515623367175612060113)
                  ·
                    refine ⟨7877636717525381709045085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10503515623367175612060113 7877636717525381709045085)
                    ·
                      refine ⟨2954113769072018140891907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877636717525381709045085 2954113769072018140891907)
                      ·
                        rfl

theorem cell23_5753116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5753116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753116 prefixEnd_5753116 := by exact prefixLift 5753116
  have htrace : WordTrace (prefixWord ++ tailWord_5753116) baseStart_5753116 baseEnd_5753116 := by
    simpa [prefixWord, tailWord_5753116, baseEnd_5753116] using wordTrace_append hprefix tailTrace_5753116
  have hstable : (prefixWord ++ tailWord_5753116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753116).length < 2 ^ (prefixWord ++ tailWord_5753116).sum := by decide
  have hdescent : baseEnd_5753116 < baseStart_5753116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753119 : List Nat := [1, 1, 2, 4, 3, 1, 11]
def baseStart_5753119 : Nat := 118140960795 + 5753119 * 2 ^ 59
def prefixEnd_5753119 : Nat := 4983230072969 + 3 ^ 40 * 5753119 * 2
def baseEnd_5753119 : Nat := 36470559376715822582153

theorem tailTrace_5753119 : CollatzResearch.WordTrace tailWord_5753119 prefixEnd_5753119 36470559376715822582153 := by
  unfold tailWord_5753119
  simp only [CollatzResearch.WordTrace]
  refine ⟨209833488444439892345150411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139888992296293261563433607 209833488444439892345150411)
  ·
    refine ⟨314750232666659838517725617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209833488444439892345150411 314750232666659838517725617)
    ·
      refine ⟨236062674499994878888294213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314750232666659838517725617 236062674499994878888294213)
      ·
        refine ⟨44261751468749039791555165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236062674499994878888294213 44261751468749039791555165)
        ·
          refine ⟨16598156800780889921833187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44261751468749039791555165 16598156800780889921833187)
          ·
            refine ⟨24897235201171334882749781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16598156800780889921833187 24897235201171334882749781)
            ·
              refine ⟨36470559376715822582153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24897235201171334882749781 36470559376715822582153)
              ·
                rfl

theorem cell23_5753119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 11].length) (baseStart_5753119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753119 prefixEnd_5753119 := by exact prefixLift 5753119
  have htrace : WordTrace (prefixWord ++ tailWord_5753119) baseStart_5753119 baseEnd_5753119 := by
    simpa [prefixWord, tailWord_5753119, baseEnd_5753119] using wordTrace_append hprefix tailTrace_5753119
  have hstable : (prefixWord ++ tailWord_5753119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753119).length < 2 ^ (prefixWord ++ tailWord_5753119).sum := by decide
  have hdescent : baseEnd_5753119 < baseStart_5753119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753139 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_5753139 : Nat := 118140960795 + 5753139 * 2 ^ 59
def prefixEnd_5753139 : Nat := 4983230072969 + 3 ^ 40 * 5753139 * 2
def baseEnd_5753139 : Nat := 2954125579127071550904301

theorem tailTrace_5753139 : CollatzResearch.WordTrace tailWord_5753139 prefixEnd_5753139 2954125579127071550904301 := by
  unfold tailWord_5753139
  simp only [CollatzResearch.WordTrace]
  refine ⟨209834217904367435760878471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139889478602911623840585647 209834217904367435760878471)
  ·
    refine ⟨314751326856551153641317707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209834217904367435760878471 314751326856551153641317707)
    ·
      refine ⟨472126990284826730461976561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314751326856551153641317707 472126990284826730461976561)
      ·
        refine ⟨354095242713620047846482421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472126990284826730461976561 354095242713620047846482421)
        ·
          refine ⟨33196429004401879485607727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354095242713620047846482421 33196429004401879485607727)
          ·
            refine ⟨49794643506602819228411591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33196429004401879485607727 49794643506602819228411591)
            ·
              refine ⟨74691965259904228842617387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49794643506602819228411591 74691965259904228842617387)
              ·
                refine ⟨112037947889856343263926081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74691965259904228842617387 112037947889856343263926081)
                ·
                  refine ⟨84028460917392257447944561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112037947889856343263926081 84028460917392257447944561)
                  ·
                    refine ⟨63021345688044193085958421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84028460917392257447944561 63021345688044193085958421)
                    ·
                      refine ⟨2954125579127071550904301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63021345688044193085958421 2954125579127071550904301)
                      ·
                        rfl

theorem cell23_5753139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_5753139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753139 prefixEnd_5753139 := by exact prefixLift 5753139
  have htrace : WordTrace (prefixWord ++ tailWord_5753139) baseStart_5753139 baseEnd_5753139 := by
    simpa [prefixWord, tailWord_5753139, baseEnd_5753139] using wordTrace_append hprefix tailTrace_5753139
  have hstable : (prefixWord ++ tailWord_5753139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753139).length < 2 ^ (prefixWord ++ tailWord_5753139).sum := by decide
  have hdescent : baseEnd_5753139 < baseStart_5753139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753140 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_5753140 : Nat := 118140960795 + 5753140 * 2 ^ 59
def prefixEnd_5753140 : Nat := 4983230072969 + 3 ^ 40 * 5753140 * 2
def baseEnd_5753140 : Nat := 984708697535908682330599

theorem tailTrace_5753140 : CollatzResearch.WordTrace tailWord_5753140 prefixEnd_5753140 984708697535908682330599 := by
  unfold tailWord_5753140
  simp only [CollatzResearch.WordTrace]
  refine ⟨104917127188681906465832437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139889502918242541954443249 104917127188681906465832437)
  ·
    refine ⟨9835980673938928731171791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104917127188681906465832437 9835980673938928731171791)
    ·
      refine ⟨14753971010908393096757687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835980673938928731171791 14753971010908393096757687)
      ·
        refine ⟨22130956516362589645136531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14753971010908393096757687 22130956516362589645136531)
        ·
          refine ⟨33196434774543884467704797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22130956516362589645136531 33196434774543884467704797)
          ·
            refine ⟨12448663040453956675389299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33196434774543884467704797 12448663040453956675389299)
            ·
              refine ⟨18672994560680935013083949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448663040453956675389299 18672994560680935013083949)
              ·
                refine ⟨7002372960255350629906481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18672994560680935013083949 7002372960255350629906481)
                ·
                  refine ⟨5251779720191512972429861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7002372960255350629906481 5251779720191512972429861)
                  ·
                    refine ⟨984708697535908682330599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5251779720191512972429861 984708697535908682330599)
                    ·
                      rfl

theorem cell23_5753140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_5753140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753140 prefixEnd_5753140 := by exact prefixLift 5753140
  have htrace : WordTrace (prefixWord ++ tailWord_5753140) baseStart_5753140 baseEnd_5753140 := by
    simpa [prefixWord, tailWord_5753140, baseEnd_5753140] using wordTrace_append hprefix tailTrace_5753140
  have hstable : (prefixWord ++ tailWord_5753140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753140).length < 2 ^ (prefixWord ++ tailWord_5753140).sum := by decide
  have hdescent : baseEnd_5753140 < baseStart_5753140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753150 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_5753150 : Nat := 118140960795 + 5753150 * 2 ^ 59
def prefixEnd_5753150 : Nat := 4983230072969 + 3 ^ 40 * 5753150 * 2
def baseEnd_5753150 : Nat := 2954131227414271007866751

theorem tailTrace_5753150 : CollatzResearch.WordTrace tailWord_5753150 prefixEnd_5753150 2954131227414271007866751 := by
  unfold tailWord_5753150
  simp only [CollatzResearch.WordTrace]
  refine ⟨26229327388415948079941113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139889746071551723093019269 26229327388415948079941113)
  ·
    refine ⟨19671995541311961059955835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26229327388415948079941113 19671995541311961059955835)
    ·
      refine ⟨29507993311967941589933753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19671995541311961059955835 29507993311967941589933753)
      ·
        refine ⟨22130994983975956192450315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29507993311967941589933753 22130994983975956192450315)
        ·
          refine ⟨33196492475963934288675473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22130994983975956192450315 33196492475963934288675473)
          ·
            refine ⟨24897369356972950716506605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33196492475963934288675473 24897369356972950716506605)
            ·
              refine ⟨9336513508864856518689977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24897369356972950716506605 9336513508864856518689977)
              ·
                refine ⟨7002385131648642389017483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336513508864856518689977 7002385131648642389017483)
                ·
                  refine ⟨10503577697472963583526225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002385131648642389017483 10503577697472963583526225)
                  ·
                    refine ⟨7877683273104722687644669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10503577697472963583526225 7877683273104722687644669)
                    ·
                      refine ⟨2954131227414271007866751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877683273104722687644669 2954131227414271007866751)
                      ·
                        rfl

theorem cell23_5753150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_5753150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753150 prefixEnd_5753150 := by exact prefixLift 5753150
  have htrace : WordTrace (prefixWord ++ tailWord_5753150) baseStart_5753150 baseEnd_5753150 := by
    simpa [prefixWord, tailWord_5753150, baseEnd_5753150] using wordTrace_append hprefix tailTrace_5753150
  have hstable : (prefixWord ++ tailWord_5753150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753150).length < 2 ^ (prefixWord ++ tailWord_5753150).sum := by decide
  have hdescent : baseEnd_5753150 < baseStart_5753150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753220 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5753220 : Nat := 118140960795 + 5753220 * 2 ^ 59
def prefixEnd_5753220 : Nat := 4983230072969 + 3 ^ 40 * 5753220 * 2
def baseEnd_5753220 : Nat := 2954167171060085733991429

theorem tailTrace_5753220 : CollatzResearch.WordTrace tailWord_5753220 prefixEnd_5753220 2954167171060085733991429 := by
  unfold tailWord_5753220
  simp only [CollatzResearch.WordTrace]
  refine ⟨104918586108536993297288557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139891448144715991063051409 104918586108536993297288557)
  ·
    refine ⟨39344469790701372486483209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104918586108536993297288557 39344469790701372486483209)
    ·
      refine ⟨29508352343026029364862407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39344469790701372486483209 29508352343026029364862407)
      ·
        refine ⟨44262528514539044047293611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29508352343026029364862407 44262528514539044047293611)
        ·
          refine ⟨66393792771808566070940417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44262528514539044047293611 66393792771808566070940417)
          ·
            refine ⟨49795344578856424553205313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66393792771808566070940417 49795344578856424553205313)
            ·
              refine ⟨37346508434142318414903985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49795344578856424553205313 37346508434142318414903985)
              ·
                refine ⟨28009881325606738811177989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37346508434142318414903985 28009881325606738811177989)
                ·
                  refine ⟨5251852748551263527095873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28009881325606738811177989 5251852748551263527095873)
                  ·
                    refine ⟨3938889561413447645321905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5251852748551263527095873 3938889561413447645321905)
                    ·
                      refine ⟨2954167171060085733991429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938889561413447645321905 2954167171060085733991429)
                      ·
                        rfl

theorem cell23_5753220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5753220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753220 prefixEnd_5753220 := by exact prefixLift 5753220
  have htrace : WordTrace (prefixWord ++ tailWord_5753220) baseStart_5753220 baseEnd_5753220 := by
    simpa [prefixWord, tailWord_5753220, baseEnd_5753220] using wordTrace_append hprefix tailTrace_5753220
  have hstable : (prefixWord ++ tailWord_5753220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753220).length < 2 ^ (prefixWord ++ tailWord_5753220).sum := by decide
  have hdescent : baseEnd_5753220 < baseStart_5753220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753313 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_5753313 : Nat := 118140960795 + 5753313 * 2 ^ 59
def prefixEnd_5753313 : Nat := 4983230072969 + 3 ^ 40 * 5753313 * 2
def baseEnd_5753313 : Nat := 2954214924760953870128501

theorem tailTrace_5753313 : CollatzResearch.WordTrace tailWord_5753313 prefixEnd_5753313 2954214924760953870128501 := by
  unfold tailWord_5753313
  simp only [CollatzResearch.WordTrace]
  refine ⟨209840564205737063477712593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139893709470491375651808395 209840564205737063477712593)
  ·
    refine ⟨157380423154302797608284445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209840564205737063477712593 157380423154302797608284445)
    ·
      refine ⟨59017658682863549103106667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157380423154302797608284445 59017658682863549103106667)
      ·
        refine ⟨88526488024295323654660001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59017658682863549103106667 88526488024295323654660001)
        ·
          refine ⟨66394866018221492740995001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88526488024295323654660001 66394866018221492740995001)
          ·
            refine ⟨49796149513666119555746251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66394866018221492740995001 49796149513666119555746251)
            ·
              refine ⟨74694224270499179333619377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49796149513666119555746251 74694224270499179333619377)
              ·
                refine ⟨56020668202874384500214533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74694224270499179333619377 56020668202874384500214533)
                ·
                  refine ⟨10503875288038947093790225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56020668202874384500214533 10503875288038947093790225)
                  ·
                    refine ⟨7877906466029210320342669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10503875288038947093790225 7877906466029210320342669)
                    ·
                      refine ⟨2954214924760953870128501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7877906466029210320342669 2954214924760953870128501)
                      ·
                        rfl

theorem cell23_5753313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_5753313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753313 prefixEnd_5753313 := by exact prefixLift 5753313
  have htrace : WordTrace (prefixWord ++ tailWord_5753313) baseStart_5753313 baseEnd_5753313 := by
    simpa [prefixWord, tailWord_5753313, baseEnd_5753313] using wordTrace_append hprefix tailTrace_5753313
  have hstable : (prefixWord ++ tailWord_5753313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753313).length < 2 ^ (prefixWord ++ tailWord_5753313).sum := by decide
  have hdescent : baseEnd_5753313 < baseStart_5753313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753370 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_5753370 : Nat := 118140960795 + 5753370 * 2 ^ 59
def prefixEnd_5753370 : Nat := 4983230072969 + 3 ^ 40 * 5753370 * 2
def baseEnd_5753370 : Nat := 2954244193158260147115739

theorem tailTrace_5753370 : CollatzResearch.WordTrace tailWord_5753370 prefixEnd_5753370 2954244193158260147115739 := by
  unfold tailWord_5753370
  simp only [CollatzResearch.WordTrace]
  refine ⟨52460660791632640553134391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139895095444353708141691709 52460660791632640553134391)
  ·
    refine ⟨78690991187448960829701587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52460660791632640553134391 78690991187448960829701587)
    ·
      refine ⟨118036486781173441244552381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78690991187448960829701587 118036486781173441244552381)
      ·
        refine ⟨44263682542940040466707143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118036486781173441244552381 44263682542940040466707143)
        ·
          refine ⟨66395523814410060700060715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44263682542940040466707143 66395523814410060700060715)
          ·
            refine ⟨99593285721615091050091073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66395523814410060700060715 99593285721615091050091073)
            ·
              refine ⟨74694964291211318287568305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99593285721615091050091073 74694964291211318287568305)
              ·
                refine ⟨56021223218408488715676229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74694964291211318287568305 56021223218408488715676229)
                ·
                  refine ⟨10503979353451591634189293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56021223218408488715676229 10503979353451591634189293)
                  ·
                    refine ⟨3938992257544346862820985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10503979353451591634189293 3938992257544346862820985)
                    ·
                      refine ⟨2954244193158260147115739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3938992257544346862820985 2954244193158260147115739)
                      ·
                        rfl

theorem cell23_5753370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_5753370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753370 prefixEnd_5753370 := by exact prefixLift 5753370
  have htrace : WordTrace (prefixWord ++ tailWord_5753370) baseStart_5753370 baseEnd_5753370 := by
    simpa [prefixWord, tailWord_5753370, baseEnd_5753370] using wordTrace_append hprefix tailTrace_5753370
  have hstable : (prefixWord ++ tailWord_5753370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753370).length < 2 ^ (prefixWord ++ tailWord_5753370).sum := by decide
  have hdescent : baseEnd_5753370 < baseStart_5753370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753393 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_5753393 : Nat := 118140960795 + 5753393 * 2 ^ 59
def prefixEnd_5753393 : Nat := 4983230072969 + 3 ^ 40 * 5753393 * 2
def baseEnd_5753393 : Nat := 984752001071104519042711

theorem tailTrace_5753393 : CollatzResearch.WordTrace tailWord_5753393 prefixEnd_5753393 984752001071104519042711 := by
  unfold tailWord_5753393
  simp only [CollatzResearch.WordTrace]
  refine ⟨209843482045447237140624833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139895654696964824760416555 209843482045447237140624833)
  ·
    refine ⟨157382611534085427855468625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209843482045447237140624833 157382611534085427855468625)
    ·
      refine ⟨118036958650564070891601469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157382611534085427855468625 118036958650564070891601469)
      ·
        refine ⟨44263859493961526584350551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118036958650564070891601469 44263859493961526584350551)
        ·
          refine ⟨66395789240942289876525827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44263859493961526584350551 66395789240942289876525827)
          ·
            refine ⟨99593683861413434814788741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66395789240942289876525827 99593683861413434814788741)
            ·
              refine ⟨18673815724015019027772889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99593683861413434814788741 18673815724015019027772889)
              ·
                refine ⟨14005361793011264270829667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18673815724015019027772889 14005361793011264270829667)
                ·
                  refine ⟨21008042689516896406244501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14005361793011264270829667 21008042689516896406244501)
                  ·
                    refine ⟨984752001071104519042711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21008042689516896406244501 984752001071104519042711)
                    ·
                      rfl

theorem cell23_5753393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_5753393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753393 prefixEnd_5753393 := by exact prefixLift 5753393
  have htrace : WordTrace (prefixWord ++ tailWord_5753393) baseStart_5753393 baseEnd_5753393 := by
    simpa [prefixWord, tailWord_5753393, baseEnd_5753393] using wordTrace_append hprefix tailTrace_5753393
  have hstable : (prefixWord ++ tailWord_5753393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753393).length < 2 ^ (prefixWord ++ tailWord_5753393).sum := by decide
  have hdescent : baseEnd_5753393 < baseStart_5753393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753400 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_5753400 : Nat := 118140960795 + 5753400 * 2 ^ 59
def prefixEnd_5753400 : Nat := 4983230072969 + 3 ^ 40 * 5753400 * 2
def baseEnd_5753400 : Nat := 2954259597577895029740601

theorem tailTrace_5753400 : CollatzResearch.WordTrace tailWord_5753400 prefixEnd_5753400 2954259597577895029740601 := by
  unfold tailWord_5753400
  simp only [CollatzResearch.WordTrace]
  refine ⟨104921868678210938668064827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139895824904281251557419769 104921868678210938668064827)
  ·
    refine ⟨157382803017316408002097241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104921868678210938668064827 157382803017316408002097241)
    ·
      refine ⟨118037102262987306001572931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157382803017316408002097241 118037102262987306001572931)
      ·
        refine ⟨177055653394480959002359397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118037102262987306001572931 177055653394480959002359397)
        ·
          refine ⟨33197935011465179812942387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177055653394480959002359397 33197935011465179812942387)
          ·
            refine ⟨49796902517197769719413581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33197935011465179812942387 49796902517197769719413581)
            ·
              refine ⟨18673838443949163644780093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49796902517197769719413581 18673838443949163644780093)
              ·
                refine ⟨7002689416480936366792535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18673838443949163644780093 7002689416480936366792535)
                ·
                  refine ⟨10504034124721404550188803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002689416480936366792535 10504034124721404550188803)
                  ·
                    refine ⟨15756051187082106825283205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10504034124721404550188803 15756051187082106825283205)
                    ·
                      refine ⟨2954259597577895029740601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15756051187082106825283205 2954259597577895029740601)
                      ·
                        rfl

theorem cell23_5753400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_5753400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753400 prefixEnd_5753400 := by exact prefixLift 5753400
  have htrace : WordTrace (prefixWord ++ tailWord_5753400) baseStart_5753400 baseEnd_5753400 := by
    simpa [prefixWord, tailWord_5753400, baseEnd_5753400] using wordTrace_append hprefix tailTrace_5753400
  have hstable : (prefixWord ++ tailWord_5753400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753400).length < 2 ^ (prefixWord ++ tailWord_5753400).sum := by decide
  have hdescent : baseEnd_5753400 < baseStart_5753400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753450 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5753450 : Nat := 118140960795 + 5753450 * 2 ^ 59
def prefixEnd_5753450 : Nat := 4983230072969 + 3 ^ 40 * 5753450 * 2
def baseEnd_5753450 : Nat := 2954285271610619834115371

theorem tailTrace_5753450 : CollatzResearch.WordTrace tailWord_5753450 prefixEnd_5753450 2954285271610619834115371 := by
  unfold tailWord_5753450
  simp only [CollatzResearch.WordTrace]
  refine ⟨52461390251560183968862451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139897040670827157250299869 52461390251560183968862451)
  ·
    refine ⟨78692085377340275953293677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52461390251560183968862451 78692085377340275953293677)
    ·
      refine ⟨29509532016502603482485129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78692085377340275953293677 29509532016502603482485129)
      ·
        refine ⟨22132149012376952611863847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29509532016502603482485129 22132149012376952611863847)
        ·
          refine ⟨33198223518565428917795771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22132149012376952611863847 33198223518565428917795771)
          ·
            refine ⟨49797335277848143376693657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33198223518565428917795771 49797335277848143376693657)
            ·
              refine ⟨37348001458386107532520243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49797335277848143376693657 37348001458386107532520243)
              ·
                refine ⟨56022002187579161298780365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37348001458386107532520243 56022002187579161298780365)
                ·
                  refine ⟨21008250820342185487042637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56022002187579161298780365 21008250820342185487042637)
                  ·
                    refine ⟨7878094057628319557640989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21008250820342185487042637 7878094057628319557640989)
                    ·
                      refine ⟨2954285271610619834115371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878094057628319557640989 2954285271610619834115371)
                      ·
                        rfl

theorem cell23_5753450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5753450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753450 prefixEnd_5753450 := by exact prefixLift 5753450
  have htrace : WordTrace (prefixWord ++ tailWord_5753450) baseStart_5753450 baseEnd_5753450 := by
    simpa [prefixWord, tailWord_5753450, baseEnd_5753450] using wordTrace_append hprefix tailTrace_5753450
  have hstable : (prefixWord ++ tailWord_5753450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753450).length < 2 ^ (prefixWord ++ tailWord_5753450).sum := by decide
  have hdescent : baseEnd_5753450 < baseStart_5753450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753507 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 4, 2, 2]
def baseStart_5753507 : Nat := 118140960795 + 5753507 * 2 ^ 59
def prefixEnd_5753507 : Nat := 4983230072969 + 3 ^ 40 * 5753507 * 2
def baseEnd_5753507 : Nat := 2954314540007926111102609

theorem tailTrace_5753507 : CollatzResearch.WordTrace tailWord_5753507 prefixEnd_5753507 2954314540007926111102609 := by
  unfold tailWord_5753507
  simp only [CollatzResearch.WordTrace]
  refine ⟨209847639967034234610274775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139898426644689489740183183 209847639967034234610274775)
  ·
    refine ⟨314771459950551351915412163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209847639967034234610274775 314771459950551351915412163)
    ·
      refine ⟨472157189925827027873118245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314771459950551351915412163 472157189925827027873118245)
      ·
        refine ⟨88529473111092567726209671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 472157189925827027873118245 88529473111092567726209671)
        ·
          refine ⟨132794209666638851589314507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88529473111092567726209671 132794209666638851589314507)
          ·
            refine ⟨199191314499958277383971761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132794209666638851589314507 199191314499958277383971761)
            ·
              refine ⟨149393485874968708037978821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199191314499958277383971761 149393485874968708037978821)
              ·
                refine ⟨28011278601556632757121029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149393485874968708037978821 28011278601556632757121029)
                ·
                  refine ⟨5252114737791868641960193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28011278601556632757121029 5252114737791868641960193)
                  ·
                    refine ⟨3939086053343901481470145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252114737791868641960193 3939086053343901481470145)
                    ·
                      refine ⟨2954314540007926111102609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939086053343901481470145 2954314540007926111102609)
                      ·
                        rfl

theorem cell23_5753507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_5753507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753507 prefixEnd_5753507 := by exact prefixLift 5753507
  have htrace : WordTrace (prefixWord ++ tailWord_5753507) baseStart_5753507 baseEnd_5753507 := by
    simpa [prefixWord, tailWord_5753507, baseEnd_5753507] using wordTrace_append hprefix tailTrace_5753507
  have hstable : (prefixWord ++ tailWord_5753507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753507).length < 2 ^ (prefixWord ++ tailWord_5753507).sum := by decide
  have hdescent : baseEnd_5753507 < baseStart_5753507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753560 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_5753560 : Nat := 118140960795 + 5753560 * 2 ^ 59
def prefixEnd_5753560 : Nat := 4983230072969 + 3 ^ 40 * 5753560 * 2
def baseEnd_5753560 : Nat := 984780584827538134579955

theorem tailTrace_5753560 : CollatzResearch.WordTrace tailWord_5753560 prefixEnd_5753560 984780584827538134579955 := by
  unfold tailWord_5753560
  simp only [CollatzResearch.WordTrace]
  refine ⟨104924786517921112330977067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139899715357228149774636089 104924786517921112330977067)
  ·
    refine ⟨157387179776881668496465601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104924786517921112330977067 157387179776881668496465601)
    ·
      refine ⟨118040384832661251372349201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157387179776881668496465601 118040384832661251372349201)
      ·
        refine ⟨88530288624495938529261901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118040384832661251372349201 88530288624495938529261901)
        ·
          refine ⟨33198858234185976948473213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88530288624495938529261901 33198858234185976948473213)
          ·
            refine ⟨12449571837819741355677455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33198858234185976948473213 12449571837819741355677455)
            ·
              refine ⟨18674357756729612033516183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12449571837819741355677455 18674357756729612033516183)
              ·
                refine ⟨28011536635094418050274275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18674357756729612033516183 28011536635094418050274275)
                ·
                  refine ⟨42017304952641627075411413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28011536635094418050274275 42017304952641627075411413)
                  ·
                    refine ⟨984780584827538134579955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42017304952641627075411413 984780584827538134579955)
                    ·
                      rfl

theorem cell23_5753560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_5753560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753560 prefixEnd_5753560 := by exact prefixLift 5753560
  have htrace : WordTrace (prefixWord ++ tailWord_5753560) baseStart_5753560 baseEnd_5753560 := by
    simpa [prefixWord, tailWord_5753560, baseEnd_5753560] using wordTrace_append hprefix tailTrace_5753560
  have hstable : (prefixWord ++ tailWord_5753560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753560).length < 2 ^ (prefixWord ++ tailWord_5753560).sum := by decide
  have hdescent : baseEnd_5753560 < baseStart_5753560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753564 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 5]
def baseStart_5753564 : Nat := 118140960795 + 5753564 * 2 ^ 59
def prefixEnd_5753564 : Nat := 4983230072969 + 3 ^ 40 * 5753564 * 2
def baseEnd_5753564 : Nat := 328260423156136932009983

theorem tailTrace_5753564 : CollatzResearch.WordTrace tailWord_5753564 prefixEnd_5753564 328260423156136932009983 := by
  unfold tailWord_5753564
  simp only [CollatzResearch.WordTrace]
  refine ⟨104924859463913866672549873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139899812618551822230066497 104924859463913866672549873)
  ·
    refine ⟨78693644597935400004412405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104924859463913866672549873 78693644597935400004412405)
    ·
      refine ⟨7377529181056443750413663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78693644597935400004412405 7377529181056443750413663)
      ·
        refine ⟨11066293771584665625620495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7377529181056443750413663 11066293771584665625620495)
        ·
          refine ⟨16599440657376998438430743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066293771584665625620495 16599440657376998438430743)
          ·
            refine ⟨24899160986065497657646115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16599440657376998438430743 24899160986065497657646115)
            ·
              refine ⟨37348741479098246486469173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24899160986065497657646115 37348741479098246486469173)
              ·
                refine ⟨3501444513665460608106485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37348741479098246486469173 3501444513665460608106485)
                ·
                  refine ⟨328260423156136932009983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3501444513665460608106485 328260423156136932009983)
                  ·
                    rfl

theorem cell23_5753564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_5753564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753564 prefixEnd_5753564 := by exact prefixLift 5753564
  have htrace : WordTrace (prefixWord ++ tailWord_5753564) baseStart_5753564 baseEnd_5753564 := by
    simpa [prefixWord, tailWord_5753564, baseEnd_5753564] using wordTrace_append hprefix tailTrace_5753564
  have hstable : (prefixWord ++ tailWord_5753564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753564).length < 2 ^ (prefixWord ++ tailWord_5753564).sum := by decide
  have hdescent : baseEnd_5753564 < baseStart_5753564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753580 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_5753580 : Nat := 118140960795 + 5753580 * 2 ^ 59
def prefixEnd_5753580 : Nat := 4983230072969 + 3 ^ 40 * 5753580 * 2
def baseEnd_5753580 : Nat := 2954352024095704325489773

theorem tailTrace_5753580 : CollatzResearch.WordTrace tailWord_5753580 prefixEnd_5753580 2954352024095704325489773 := by
  unfold tailWord_5753580
  simp only [CollatzResearch.WordTrace]
  refine ⟨104925151247884884038841097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139900201663846512051788129 104925151247884884038841097)
  ·
    refine ⟨78693863435913663029130823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104925151247884884038841097 78693863435913663029130823)
    ·
      refine ⟨118040795153870494543696235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78693863435913663029130823 118040795153870494543696235)
      ·
        refine ⟨177061192730805741815544353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118040795153870494543696235 177061192730805741815544353)
        ·
          refine ⟨132795894548104306361658265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177061192730805741815544353 132795894548104306361658265)
          ·
            refine ⟨99596920911078229771243699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132795894548104306361658265 99596920911078229771243699)
            ·
              refine ⟨149395381366617344656865549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99596920911078229771243699 149395381366617344656865549)
              ·
                refine ⟨56023268012481504246324581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149395381366617344656865549 56023268012481504246324581)
                ·
                  refine ⟨10504362752340282046185859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56023268012481504246324581 10504362752340282046185859)
                  ·
                    refine ⟨15756544128510423069278789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10504362752340282046185859 15756544128510423069278789)
                    ·
                      refine ⟨2954352024095704325489773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15756544128510423069278789 2954352024095704325489773)
                      ·
                        rfl

theorem cell23_5753580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_5753580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753580 prefixEnd_5753580 := by exact prefixLift 5753580
  have htrace : WordTrace (prefixWord ++ tailWord_5753580) baseStart_5753580 baseEnd_5753580 := by
    simpa [prefixWord, tailWord_5753580, baseEnd_5753580] using wordTrace_append hprefix tailTrace_5753580
  have hstable : (prefixWord ++ tailWord_5753580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753580).length < 2 ^ (prefixWord ++ tailWord_5753580).sum := by decide
  have hdescent : baseEnd_5753580 < baseStart_5753580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753597 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_5753597 : Nat := 118140960795 + 5753597 * 2 ^ 59
def prefixEnd_5753597 : Nat := 4983230072969 + 3 ^ 40 * 5753597 * 2
def baseEnd_5753597 : Nat := 2954360753266830758977195

theorem tailTrace_5753597 : CollatzResearch.WordTrace tailWord_5753597 prefixEnd_5753597 2954360753266830758977195 := by
  unfold tailWord_5753597
  simp only [CollatzResearch.WordTrace]
  refine ⟨209850922536708179981051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139900615024472119987367363 209850922536708179981051045)
  ·
    refine ⟨39347047975632783746447071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209850922536708179981051045 39347047975632783746447071)
    ·
      refine ⟨59020571963449175619670607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39347047975632783746447071 59020571963449175619670607)
      ·
        refine ⟨88530857945173763429505911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59020571963449175619670607 88530857945173763429505911)
        ·
          refine ⟨132796286917760645144258867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88530857945173763429505911 132796286917760645144258867)
          ·
            refine ⟨199194430376640967716388301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132796286917760645144258867 199194430376640967716388301)
            ·
              refine ⟨74697911391240362893645613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199194430376640967716388301 74697911391240362893645613)
              ·
                refine ⟨28011716771715136085117105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74697911391240362893645613 28011716771715136085117105)
                ·
                  refine ⟨21008787578786352063837829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28011716771715136085117105 21008787578786352063837829)
                  ·
                    refine ⟨3939147671022441011969593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21008787578786352063837829 3939147671022441011969593)
                    ·
                      refine ⟨2954360753266830758977195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939147671022441011969593 2954360753266830758977195)
                      ·
                        rfl

theorem cell23_5753597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_5753597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753597 prefixEnd_5753597 := by exact prefixLift 5753597
  have htrace : WordTrace (prefixWord ++ tailWord_5753597) baseStart_5753597 baseEnd_5753597 := by
    simpa [prefixWord, tailWord_5753597, baseEnd_5753597] using wordTrace_append hprefix tailTrace_5753597
  have hstable : (prefixWord ++ tailWord_5753597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753597).length < 2 ^ (prefixWord ++ tailWord_5753597).sum := by decide
  have hdescent : baseEnd_5753597 < baseStart_5753597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753610 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5753610 : Nat := 118140960795 + 5753610 * 2 ^ 59
def prefixEnd_5753610 : Nat := 4983230072969 + 3 ^ 40 * 5753610 * 2
def baseEnd_5753610 : Nat := 2954367428515339208114635

theorem tailTrace_5753610 : CollatzResearch.WordTrace tailWord_5753610 prefixEnd_5753610 2954367428515339208114635 := by
  unfold tailWord_5753610
  simp only [CollatzResearch.WordTrace]
  refine ⟨52462849171415270800318571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139900931123774055467516189 52462849171415270800318571)
  ·
    refine ⟨78694273757122906200477857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52462849171415270800318571 78694273757122906200477857)
    ·
      refine ⟨59020705317842179650358393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78694273757122906200477857 59020705317842179650358393)
      ·
        refine ⟨44265528988381634737768795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59020705317842179650358393 44265528988381634737768795)
        ·
          refine ⟨66398293482572452106653193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44265528988381634737768795 66398293482572452106653193)
          ·
            refine ⟨49798720111929339079989895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66398293482572452106653193 49798720111929339079989895)
            ·
              refine ⟨74698080167894008619984843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49798720111929339079989895 74698080167894008619984843)
              ·
                refine ⟨112047120251841012929977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74698080167894008619984843 112047120251841012929977265)
                ·
                  refine ⟨84035340188880759697482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112047120251841012929977265 84035340188880759697482949)
                  ·
                    refine ⟨15756626285415142443278053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84035340188880759697482949 15756626285415142443278053)
                    ·
                      refine ⟨2954367428515339208114635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15756626285415142443278053 2954367428515339208114635)
                      ·
                        rfl

theorem cell23_5753610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5753610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753610 prefixEnd_5753610 := by exact prefixLift 5753610
  have htrace : WordTrace (prefixWord ++ tailWord_5753610) baseStart_5753610 baseEnd_5753610 := by
    simpa [prefixWord, tailWord_5753610, baseEnd_5753610] using wordTrace_append hprefix tailTrace_5753610
  have hstable : (prefixWord ++ tailWord_5753610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753610).length < 2 ^ (prefixWord ++ tailWord_5753610).sum := by decide
  have hdescent : baseEnd_5753610 < baseStart_5753610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753634 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_5753634 : Nat := 118140960795 + 5753634 * 2 ^ 59
def prefixEnd_5753634 : Nat := 4983230072969 + 3 ^ 40 * 5753634 * 2
def baseEnd_5753634 : Nat := 2954379752051047114214525

theorem tailTrace_5753634 : CollatzResearch.WordTrace tailWord_5753634 prefixEnd_5753634 2954379752051047114214525 := by
  unfold tailWord_5753634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52463068009393533825036989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139901514691716090200098637 52463068009393533825036989)
  ·
    refine ⟨19673650503522575184388871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52463068009393533825036989 19673650503522575184388871)
    ·
      refine ⟨29510475755283862776583307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19673650503522575184388871 29510475755283862776583307)
      ·
        refine ⟨44265713632925794164874961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29510475755283862776583307 44265713632925794164874961)
        ·
          refine ⟨33199285224694345623656221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44265713632925794164874961 33199285224694345623656221)
          ·
            refine ⟨12449731959260379608871083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33199285224694345623656221 12449731959260379608871083)
            ·
              refine ⟨18674597938890569413306625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12449731959260379608871083 18674597938890569413306625)
              ·
                refine ⟨14005948454167927059979969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18674597938890569413306625 14005948454167927059979969)
                ·
                  refine ⟨10504461340625945294984977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14005948454167927059979969 10504461340625945294984977)
                  ·
                    refine ⟨7878346005469458971238733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10504461340625945294984977 7878346005469458971238733)
                    ·
                      refine ⟨2954379752051047114214525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878346005469458971238733 2954379752051047114214525)
                      ·
                        rfl

theorem cell23_5753634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_5753634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753634 prefixEnd_5753634 := by exact prefixLift 5753634
  have htrace : WordTrace (prefixWord ++ tailWord_5753634) baseStart_5753634 baseEnd_5753634 := by
    simpa [prefixWord, tailWord_5753634, baseEnd_5753634] using wordTrace_append hprefix tailTrace_5753634
  have hstable : (prefixWord ++ tailWord_5753634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753634).length < 2 ^ (prefixWord ++ tailWord_5753634).sum := by decide
  have hdescent : baseEnd_5753634 < baseStart_5753634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753668 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5753668 : Nat := 118140960795 + 5753668 * 2 ^ 59
def prefixEnd_5753668 : Nat := 4983230072969 + 3 ^ 40 * 5753668 * 2
def baseEnd_5753668 : Nat := 2954397210393299981189369

theorem tailTrace_5753668 : CollatzResearch.WordTrace tailWord_5753668 prefixEnd_5753668 2954397210393299981189369 := by
  unfold tailWord_5753668
  simp only [CollatzResearch.WordTrace]
  refine ⟨104926756059725479553442829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139902341412967306071257105 104926756059725479553442829)
  ·
    refine ⟨39347533522397054832541061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104926756059725479553442829 39347533522397054832541061)
    ·
      refine ⟨7377662535449447781101449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39347533522397054832541061 7377662535449447781101449)
      ·
        refine ⟨5533246901587085835826087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7377662535449447781101449 5533246901587085835826087)
        ·
          refine ⟨8299870352380628753739131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533246901587085835826087 8299870352380628753739131)
          ·
            refine ⟨12449805528570943130608697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8299870352380628753739131 12449805528570943130608697)
            ·
              refine ⟨9337354146428207347956523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12449805528570943130608697 9337354146428207347956523)
              ·
                refine ⟨14006031219642311021934785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337354146428207347956523 14006031219642311021934785)
                ·
                  refine ⟨10504523414731733266451089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14006031219642311021934785 10504523414731733266451089)
                  ·
                    refine ⟨7878392561048799949838317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10504523414731733266451089 7878392561048799949838317)
                    ·
                      refine ⟨2954397210393299981189369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878392561048799949838317 2954397210393299981189369)
                      ·
                        rfl

theorem cell23_5753668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5753668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753668 prefixEnd_5753668 := by exact prefixLift 5753668
  have htrace : WordTrace (prefixWord ++ tailWord_5753668) baseStart_5753668 baseEnd_5753668 := by
    simpa [prefixWord, tailWord_5753668, baseEnd_5753668] using wordTrace_append hprefix tailTrace_5753668
  have hstable : (prefixWord ++ tailWord_5753668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753668).length < 2 ^ (prefixWord ++ tailWord_5753668).sum := by decide
  have hdescent : baseEnd_5753668 < baseStart_5753668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753680 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_5753680 : Nat := 118140960795 + 5753680 * 2 ^ 59
def prefixEnd_5753680 : Nat := 4983230072969 + 3 ^ 40 * 5753680 * 2
def baseEnd_5753680 : Nat := 984801124053717978079771

theorem tailTrace_5753680 : CollatzResearch.WordTrace tailWord_5753680 prefixEnd_5753680 984801124053717978079771 := by
  unfold tailWord_5753680
  simp only [CollatzResearch.WordTrace]
  refine ⟨104926974897703742578161247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139902633196938323437548329 104926974897703742578161247)
  ·
    refine ⟨157390462346555613867241871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104926974897703742578161247 157390462346555613867241871)
    ·
      refine ⟨236085693519833420800862807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157390462346555613867241871 236085693519833420800862807)
      ·
        refine ⟨354128540279750131201294211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236085693519833420800862807 354128540279750131201294211)
        ·
          refine ⟨531192810419625196801941317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354128540279750131201294211 531192810419625196801941317)
          ·
            refine ⟨99598651953679724400363997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 531192810419625196801941317 99598651953679724400363997)
            ·
              refine ⟨37349494482629896650136499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99598651953679724400363997 37349494482629896650136499)
              ·
                refine ⟨56024241723944844975204749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37349494482629896650136499 56024241723944844975204749)
                ·
                  refine ⟨21009090646479316865701781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56024241723944844975204749 21009090646479316865701781)
                  ·
                    refine ⟨984801124053717978079771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21009090646479316865701781 984801124053717978079771)
                    ·
                      rfl

theorem cell23_5753680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_5753680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753680 prefixEnd_5753680 := by exact prefixLift 5753680
  have htrace : WordTrace (prefixWord ++ tailWord_5753680) baseStart_5753680 baseEnd_5753680 := by
    simpa [prefixWord, tailWord_5753680, baseEnd_5753680] using wordTrace_append hprefix tailTrace_5753680
  have hstable : (prefixWord ++ tailWord_5753680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753680).length < 2 ^ (prefixWord ++ tailWord_5753680).sum := by decide
  have hdescent : baseEnd_5753680 < baseStart_5753680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753707 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3]
def baseStart_5753707 : Nat := 118140960795 + 5753707 * 2 ^ 59
def prefixEnd_5753707 : Nat := 4983230072969 + 3 ^ 40 * 5753707 * 2
def baseEnd_5753707 : Nat := 2954417236138825328601689

theorem tailTrace_5753707 : CollatzResearch.WordTrace tailWord_5753707 prefixEnd_5753707 2954417236138825328601689 := by
  unfold tailWord_5753707
  simp only [CollatzResearch.WordTrace]
  refine ⟨209854934566309668767555375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139903289710873112511703583 209854934566309668767555375)
  ·
    refine ⟨314782401849464503151333063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209854934566309668767555375 314782401849464503151333063)
    ·
      refine ⟨472173602774196754726999595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314782401849464503151333063 472173602774196754726999595)
      ·
        refine ⟨708260404161295132090499393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472173602774196754726999595 708260404161295132090499393)
        ·
          refine ⟨531195303120971349067874545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708260404161295132090499393 531195303120971349067874545)
          ·
            refine ⟨398396477340728511800905909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531195303120971349067874545 398396477340728511800905909)
            ·
              refine ⟨37349669750693297981334929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398396477340728511800905909 37349669750693297981334929)
              ·
                refine ⟨28012252313019973486001197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37349669750693297981334929 28012252313019973486001197)
                ·
                  refine ⟨10504594617382490057250449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28012252313019973486001197 10504594617382490057250449)
                  ·
                    refine ⟨7878445963036867542937837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10504594617382490057250449 7878445963036867542937837)
                    ·
                      refine ⟨2954417236138825328601689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878445963036867542937837 2954417236138825328601689)
                      ·
                        rfl

theorem cell23_5753707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].length) (baseStart_5753707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753707 prefixEnd_5753707 := by exact prefixLift 5753707
  have htrace : WordTrace (prefixWord ++ tailWord_5753707) baseStart_5753707 baseEnd_5753707 := by
    simpa [prefixWord, tailWord_5753707, baseEnd_5753707] using wordTrace_append hprefix tailTrace_5753707
  have hstable : (prefixWord ++ tailWord_5753707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753707).length < 2 ^ (prefixWord ++ tailWord_5753707).sum := by decide
  have hdescent : baseEnd_5753707 < baseStart_5753707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753714 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_5753714 : Nat := 118140960795 + 5753714 * 2 ^ 59
def prefixEnd_5753714 : Nat := 4983230072969 + 3 ^ 40 * 5753714 * 2
def baseEnd_5753714 : Nat := 984806943501135600404719

theorem tailTrace_5753714 : CollatzResearch.WordTrace tailWord_5753714 prefixEnd_5753714 984806943501135600404719 := by
  unfold tailWord_5753714
  simp only [CollatzResearch.WordTrace]
  refine ⟨52463797469321077240765049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139903459918189539308706797 52463797469321077240765049)
  ·
    refine ⟨39347848101990807930573787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52463797469321077240765049 39347848101990807930573787)
    ·
      refine ⟨59021772152986211895860681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39347848101990807930573787 59021772152986211895860681)
      ·
        refine ⟨44266329114739658921895511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59021772152986211895860681 44266329114739658921895511)
        ·
          refine ⟨66399493672109488382843267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44266329114739658921895511 66399493672109488382843267)
          ·
            refine ⟨99599240508164232574264901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66399493672109488382843267 99599240508164232574264901)
            ·
              refine ⟨18674857595280793607674669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99599240508164232574264901 18674857595280793607674669)
              ·
                refine ⟨7003071598230297602878001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18674857595280793607674669 7003071598230297602878001)
                ·
                  refine ⟨5252303698672723202158501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003071598230297602878001 5252303698672723202158501)
                  ·
                    refine ⟨984806943501135600404719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5252303698672723202158501 984806943501135600404719)
                    ·
                      rfl

theorem cell23_5753714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_5753714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753714 prefixEnd_5753714 := by exact prefixLift 5753714
  have htrace : WordTrace (prefixWord ++ tailWord_5753714) baseStart_5753714 baseEnd_5753714 := by
    simpa [prefixWord, tailWord_5753714, baseEnd_5753714] using wordTrace_append hprefix tailTrace_5753714
  have hstable : (prefixWord ++ tailWord_5753714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753714).length < 2 ^ (prefixWord ++ tailWord_5753714).sum := by decide
  have hdescent : baseEnd_5753714 < baseStart_5753714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753721 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 3, 2, 2]
def baseStart_5753721 : Nat := 118140960795 + 5753721 * 2 ^ 59
def prefixEnd_5753721 : Nat := 4983230072969 + 3 ^ 40 * 5753721 * 2
def baseEnd_5753721 : Nat := 2954424424867988273826625

theorem tailTrace_5753721 : CollatzResearch.WordTrace tailWord_5753721 prefixEnd_5753721 2954424424867988273826625 := by
  unfold tailWord_5753721
  simp only [CollatzResearch.WordTrace]
  refine ⟨209855445188258949158565017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139903630125505966105710011 209855445188258949158565017)
  ·
    refine ⟨157391583891194211868923763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209855445188258949158565017 157391583891194211868923763)
    ·
      refine ⟨236087375836791317803385645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157391583891194211868923763 236087375836791317803385645)
      ·
        refine ⟨88532765938796744176269617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236087375836791317803385645 88532765938796744176269617)
        ·
          refine ⟨66399574454097558132202213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88532765938796744176269617 66399574454097558132202213)
          ·
            refine ⟨12449920210143292149787915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66399574454097558132202213 12449920210143292149787915)
            ·
              refine ⟨18674880315214938224681873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12449920210143292149787915 18674880315214938224681873)
              ·
                refine ⟨14006160236411203668511405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18674880315214938224681873 14006160236411203668511405)
                ·
                  refine ⟨5252310088654201375691777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14006160236411203668511405 5252310088654201375691777)
                  ·
                    refine ⟨3939232566490651031768833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252310088654201375691777 3939232566490651031768833)
                    ·
                      refine ⟨2954424424867988273826625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939232566490651031768833 2954424424867988273826625)
                      ·
                        rfl

theorem cell23_5753721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_5753721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753721 prefixEnd_5753721 := by exact prefixLift 5753721
  have htrace : WordTrace (prefixWord ++ tailWord_5753721) baseStart_5753721 baseEnd_5753721 := by
    simpa [prefixWord, tailWord_5753721, baseEnd_5753721] using wordTrace_append hprefix tailTrace_5753721
  have hstable : (prefixWord ++ tailWord_5753721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753721).length < 2 ^ (prefixWord ++ tailWord_5753721).sum := by decide
  have hdescent : baseEnd_5753721 < baseStart_5753721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753738 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5753738 : Nat := 118140960795 + 5753738 * 2 ^ 59
def prefixEnd_5753738 : Nat := 4983230072969 + 3 ^ 40 * 5753738 * 2
def baseEnd_5753738 : Nat := 2954433154039114707314047

theorem tailTrace_5753738 : CollatzResearch.WordTrace tailWord_5753738 prefixEnd_5753738 2954433154039114707314047 := by
  unfold tailWord_5753738
  simp only [CollatzResearch.WordTrace]
  refine ⟨52464016307299340265483467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139904043486131574041289245 52464016307299340265483467)
  ·
    refine ⟨78696024460949010398225201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52464016307299340265483467 78696024460949010398225201)
    ·
      refine ⟨59022018345711757798668901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78696024460949010398225201 59022018345711757798668901)
      ·
        refine ⟨11066628439820954587250419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59022018345711757798668901 11066628439820954587250419)
        ·
          refine ⟨16599942659731431880875629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11066628439820954587250419 16599942659731431880875629)
          ·
            refine ⟨6224978497399286955328361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16599942659731431880875629 6224978497399286955328361)
            ·
              refine ⟨4668733873049465216496271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6224978497399286955328361 4668733873049465216496271)
              ·
                refine ⟨7003100809574197824744407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668733873049465216496271 7003100809574197824744407)
                ·
                  refine ⟨10504651214361296737116611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003100809574197824744407 10504651214361296737116611)
                  ·
                    refine ⟨15756976821541945105674917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10504651214361296737116611 15756976821541945105674917)
                    ·
                      refine ⟨2954433154039114707314047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15756976821541945105674917 2954433154039114707314047)
                      ·
                        rfl

theorem cell23_5753738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5753738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753738 prefixEnd_5753738 := by exact prefixLift 5753738
  have htrace : WordTrace (prefixWord ++ tailWord_5753738) baseStart_5753738 baseEnd_5753738 := by
    simpa [prefixWord, tailWord_5753738, baseEnd_5753738] using wordTrace_append hprefix tailTrace_5753738
  have hstable : (prefixWord ++ tailWord_5753738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753738).length < 2 ^ (prefixWord ++ tailWord_5753738).sum := by decide
  have hdescent : baseEnd_5753738 < baseStart_5753738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753845 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5753845 : Nat := 118140960795 + 5753845 * 2 ^ 59
def prefixEnd_5753845 : Nat := 4983230072969 + 3 ^ 40 * 5753845 * 2
def baseEnd_5753845 : Nat := 2954488096469145788676055

theorem tailTrace_5753845 : CollatzResearch.WordTrace tailWord_5753845 prefixEnd_5753845 2954488096469145788676055 := by
  unfold tailWord_5753845
  simp only [CollatzResearch.WordTrace]
  refine ⟨209859967839809718336078989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139906645226539812224052659 209859967839809718336078989)
  ·
    refine ⟨78697487939928644376029621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209859967839809718336078989 78697487939928644376029621)
    ·
      refine ⟨7377889494368310410252777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78697487939928644376029621 7377889494368310410252777)
      ·
        refine ⟨5533417120776232807689583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7377889494368310410252777 5533417120776232807689583)
        ·
          refine ⟨8300125681164349211534375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533417120776232807689583 8300125681164349211534375)
          ·
            refine ⟨12450188521746523817301563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300125681164349211534375 12450188521746523817301563)
            ·
              refine ⟨18675282782619785725952345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450188521746523817301563 18675282782619785725952345)
              ·
                refine ⟨14006462086964839294464259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18675282782619785725952345 14006462086964839294464259)
                ·
                  refine ⟨21009693130447258941696389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14006462086964839294464259 21009693130447258941696389)
                  ·
                    refine ⟨3939317461958861051568073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21009693130447258941696389 3939317461958861051568073)
                    ·
                      refine ⟨2954488096469145788676055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3939317461958861051568073 2954488096469145788676055)
                      ·
                        rfl

theorem cell23_5753845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5753845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753845 prefixEnd_5753845 := by exact prefixLift 5753845
  have htrace : WordTrace (prefixWord ++ tailWord_5753845) baseStart_5753845 baseEnd_5753845 := by
    simpa [prefixWord, tailWord_5753845, baseEnd_5753845] using wordTrace_append hprefix tailTrace_5753845
  have hstable : (prefixWord ++ tailWord_5753845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753845).length < 2 ^ (prefixWord ++ tailWord_5753845).sum := by decide
  have hdescent : baseEnd_5753845 < baseStart_5753845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753864 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_5753864 : Nat := 118140960795 + 5753864 * 2 ^ 59
def prefixEnd_5753864 : Nat := 4983230072969 + 3 ^ 40 * 5753864 * 2
def baseEnd_5753864 : Nat := 984832617533860404779489

theorem tailTrace_5753864 : CollatzResearch.WordTrace tailWord_5753864 prefixEnd_5753864 984832617533860404779489 := by
  unfold tailWord_5753864
  simp only [CollatzResearch.WordTrace]
  refine ⟨104930330413370442290510323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139907107217827256387347097 104930330413370442290510323)
  ·
    refine ⟨157395495620055663435765485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104930330413370442290510323 157395495620055663435765485)
    ·
      refine ⟨59023310857520873788412057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157395495620055663435765485 59023310857520873788412057)
      ·
        refine ⟨44267483143140655341309043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59023310857520873788412057 44267483143140655341309043)
        ·
          refine ⟨66401224714710983011963565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44267483143140655341309043 66401224714710983011963565)
          ·
            refine ⟨24900459268016618629486337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66401224714710983011963565 24900459268016618629486337)
            ·
              refine ⟨18675344451012463972114753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24900459268016618629486337 18675344451012463972114753)
              ·
                refine ⟨14006508338259347979086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18675344451012463972114753 14006508338259347979086065)
                ·
                  refine ⟨10504881253694510984314549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14006508338259347979086065 10504881253694510984314549)
                  ·
                    refine ⟨984832617533860404779489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10504881253694510984314549 984832617533860404779489)
                    ·
                      rfl

theorem cell23_5753864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_5753864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753864 prefixEnd_5753864 := by exact prefixLift 5753864
  have htrace : WordTrace (prefixWord ++ tailWord_5753864) baseStart_5753864 baseEnd_5753864 := by
    simpa [prefixWord, tailWord_5753864, baseEnd_5753864] using wordTrace_append hprefix tailTrace_5753864
  have hstable : (prefixWord ++ tailWord_5753864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753864).length < 2 ^ (prefixWord ++ tailWord_5753864).sum := by decide
  have hdescent : baseEnd_5753864 < baseStart_5753864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753868 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 5]
def baseStart_5753868 : Nat := 118140960795 + 5753868 * 2 ^ 59
def prefixEnd_5753868 : Nat := 4983230072969 + 3 ^ 40 * 5753868 * 2
def baseEnd_5753868 : Nat := 328277767391577688743161

theorem tailTrace_5753868 : CollatzResearch.WordTrace tailWord_5753868 prefixEnd_5753868 328277767391577688743161 := by
  unfold tailWord_5753868
  simp only [CollatzResearch.WordTrace]
  refine ⟨104930403359363196632083129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139907204479150928842777505 104930403359363196632083129)
  ·
    refine ⟨78697802519522397474062347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104930403359363196632083129 78697802519522397474062347)
    ·
      refine ⟨118046703779283596211093521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78697802519522397474062347 118046703779283596211093521)
      ·
        refine ⟨88535027834462697158320141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118046703779283596211093521 88535027834462697158320141)
        ·
          refine ⟨33200635437923511434370053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88535027834462697158320141 33200635437923511434370053)
          ·
            refine ⟨6225119144610658393944385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33200635437923511434370053 6225119144610658393944385)
            ·
              refine ⟨4668839358457993795458289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225119144610658393944385 4668839358457993795458289)
              ·
                refine ⟨3501629518843495346593717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4668839358457993795458289 3501629518843495346593717)
                ·
                  refine ⟨328277767391577688743161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3501629518843495346593717 328277767391577688743161)
                  ·
                    rfl

theorem cell23_5753868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_5753868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753868 prefixEnd_5753868 := by exact prefixLift 5753868
  have htrace : WordTrace (prefixWord ++ tailWord_5753868) baseStart_5753868 baseEnd_5753868 := by
    simpa [prefixWord, tailWord_5753868, baseEnd_5753868] using wordTrace_append hprefix tailTrace_5753868
  have hstable : (prefixWord ++ tailWord_5753868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753868).length < 2 ^ (prefixWord ++ tailWord_5753868).sum := by decide
  have hdescent : baseEnd_5753868 < baseStart_5753868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753898 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_5753898 : Nat := 118140960795 + 5753898 * 2 ^ 59
def prefixEnd_5753898 : Nat := 4983230072969 + 3 ^ 40 * 5753898 * 2
def baseEnd_5753898 : Nat := 984838436981278027104437

theorem tailTrace_5753898 : CollatzResearch.WordTrace tailWord_5753898 prefixEnd_5753898 984838436981278027104437 := by
  unfold tailWord_5753898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52465475227154427096939587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139907933939078472258505565 52465475227154427096939587)
  ·
    refine ⟨78698212840731640645409381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52465475227154427096939587 78698212840731640645409381)
    ·
      refine ⟨14755914907637182621014259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78698212840731640645409381 14755914907637182621014259)
      ·
        refine ⟨22133872361455773931521389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14755914907637182621014259 22133872361455773931521389)
        ·
          refine ⟨8300202135545915224320521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22133872361455773931521389 8300202135545915224320521)
          ·
            refine ⟨6225151601659436418240391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8300202135545915224320521 6225151601659436418240391)
            ·
              refine ⟨9337727402489154627360587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225151601659436418240391 9337727402489154627360587)
              ·
                refine ⟨14006591103733731941040881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337727402489154627360587 14006591103733731941040881)
                ·
                  refine ⟨10504943327800298955780661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14006591103733731941040881 10504943327800298955780661)
                  ·
                    refine ⟨984838436981278027104437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10504943327800298955780661 984838436981278027104437)
                    ·
                      rfl

theorem cell23_5753898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_5753898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753898 prefixEnd_5753898 := by exact prefixLift 5753898
  have htrace : WordTrace (prefixWord ++ tailWord_5753898) baseStart_5753898 baseEnd_5753898 := by
    simpa [prefixWord, tailWord_5753898, baseEnd_5753898] using wordTrace_append hprefix tailTrace_5753898
  have hstable : (prefixWord ++ tailWord_5753898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753898).length < 2 ^ (prefixWord ++ tailWord_5753898).sum := by decide
  have hdescent : baseEnd_5753898 < baseStart_5753898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753904 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_5753904 : Nat := 118140960795 + 5753904 * 2 ^ 59
def prefixEnd_5753904 : Nat := 4983230072969 + 3 ^ 40 * 5753904 * 2
def baseEnd_5753904 : Nat := 2954518391827761057838283

theorem tailTrace_5753904 : CollatzResearch.WordTrace tailWord_5753904 prefixEnd_5753904 2954518391827761057838283 := by
  unfold tailWord_5753904
  simp only [CollatzResearch.WordTrace]
  refine ⟨104931059873297985706238383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139908079831063980941651177 104931059873297985706238383)
  ·
    refine ⟨157396589809946978559357575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104931059873297985706238383 157396589809946978559357575)
    ·
      refine ⟨236094884714920467839036363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157396589809946978559357575 236094884714920467839036363)
      ·
        refine ⟨354142327072380701758554545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236094884714920467839036363 354142327072380701758554545)
        ·
          refine ⟨265606745304285526318915909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354142327072380701758554545 265606745304285526318915909)
          ·
            refine ⟨49801264744553536184796733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265606745304285526318915909 49801264744553536184796733)
            ·
              refine ⟨18675474279207576069298775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49801264744553536184796733 18675474279207576069298775)
              ·
                refine ⟨28013211418811364103948163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18675474279207576069298775 28013211418811364103948163)
                ·
                  refine ⟨42019817128217046155922245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28013211418811364103948163 42019817128217046155922245)
                  ·
                    refine ⟨7878715711540696154235421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42019817128217046155922245 7878715711540696154235421)
                    ·
                      refine ⟨2954518391827761057838283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7878715711540696154235421 2954518391827761057838283)
                      ·
                        rfl

theorem cell23_5753904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_5753904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753904 prefixEnd_5753904 := by exact prefixLift 5753904
  have htrace : WordTrace (prefixWord ++ tailWord_5753904) baseStart_5753904 baseEnd_5753904 := by
    simpa [prefixWord, tailWord_5753904, baseEnd_5753904] using wordTrace_append hprefix tailTrace_5753904
  have hstable : (prefixWord ++ tailWord_5753904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753904).length < 2 ^ (prefixWord ++ tailWord_5753904).sum := by decide
  have hdescent : baseEnd_5753904 < baseStart_5753904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5753907 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 8]
def baseStart_5753907 : Nat := 118140960795 + 5753907 * 2 ^ 59
def prefixEnd_5753907 : Nat := 4983230072969 + 3 ^ 40 * 5753907 * 2
def baseEnd_5753907 : Nat := 328279992474413838455641

theorem tailTrace_5753907 : CollatzResearch.WordTrace tailWord_5753907 prefixEnd_5753907 328279992474413838455641 := by
  unfold tailWord_5753907
  simp only [CollatzResearch.WordTrace]
  refine ⟨209862229165585102924835975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139908152777056735283223983 209862229165585102924835975)
  ·
    refine ⟨314793343748377654387253963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209862229165585102924835975 314793343748377654387253963)
    ·
      refine ⟨472190015622566481580880945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314793343748377654387253963 472190015622566481580880945)
      ·
        refine ⟨354142511716924861185660709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472190015622566481580880945 354142511716924861185660709)
        ·
          refine ⟨66401720946923411472311383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354142511716924861185660709 66401720946923411472311383)
          ·
            refine ⟨99602581420385117208467075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66401720946923411472311383 99602581420385117208467075)
            ·
              refine ⟨149403872130577675812700613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99602581420385117208467075 149403872130577675812700613)
              ·
                refine ⟨28013226024483314214881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149403872130577675812700613 28013226024483314214881365)
                ·
                  refine ⟨328279992474413838455641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28013226024483314214881365 328279992474413838455641)
                  ·
                    rfl

theorem cell23_5753907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 8].length) (baseStart_5753907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5753907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5753907 prefixEnd_5753907 := by exact prefixLift 5753907
  have htrace : WordTrace (prefixWord ++ tailWord_5753907) baseStart_5753907 baseEnd_5753907 := by
    simpa [prefixWord, tailWord_5753907, baseEnd_5753907] using wordTrace_append hprefix tailTrace_5753907
  have hstable : (prefixWord ++ tailWord_5753907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5753907).length < 2 ^ (prefixWord ++ tailWord_5753907).sum := by decide
  have hdescent : baseEnd_5753907 < baseStart_5753907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5753907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
